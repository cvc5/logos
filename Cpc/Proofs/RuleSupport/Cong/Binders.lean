module

public import Cpc.Proofs.RuleSupport.Cong.RegLanSpine
import all Cpc.Proofs.RuleSupport.Cong.RegLanSpine

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

private theorem smtx_model_eval_eq_true_bool_true_iff
    (a b : SmtValue) :
    __smtx_model_eval_eq a b = SmtValue.Boolean true ->
    (a = SmtValue.Boolean true ↔ b = SmtValue.Boolean true) := by
  intro h
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, native_veq] at h ⊢ <;> simp_all

private theorem smtx_model_eval_eq_true_not_true_iff
    (a b : SmtValue) :
    __smtx_model_eval_eq a b = SmtValue.Boolean true ->
    (__smtx_model_eval_not a = SmtValue.Boolean true ↔
      __smtx_model_eval_not b = SmtValue.Boolean true) := by
  intro h
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq] at h ⊢ <;>
      simp_all

private theorem eo_eq_true_bool_eval_true_iff
    (M : SmtModel) (body body' : Term) :
    eo_interprets M (mkEq body body') true ->
    (__smtx_model_eval M (__eo_to_smt body) = SmtValue.Boolean true ↔
      __smtx_model_eval M (__eo_to_smt body') = SmtValue.Boolean true) := by
  intro hEq
  exact smtx_model_eval_eq_true_bool_true_iff
    (__smtx_model_eval M (__eo_to_smt body))
    (__smtx_model_eval M (__eo_to_smt body'))
    ((RuleProofs.smt_value_rel_iff_model_eval_eq_true
      (__smtx_model_eval M (__eo_to_smt body))
      (__smtx_model_eval M (__eo_to_smt body'))).mp
      (RuleProofs.eo_interprets_eq_rel M body body' hEq))

private theorem eo_eq_true_not_eval_true_iff
    (M : SmtModel) (body body' : Term) :
    eo_interprets M (mkEq body body') true ->
    (__smtx_model_eval M (SmtTerm.not (__eo_to_smt body)) = SmtValue.Boolean true ↔
      __smtx_model_eval M (SmtTerm.not (__eo_to_smt body')) = SmtValue.Boolean true) := by
  intro hEq
  rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_7]
  exact smtx_model_eval_eq_true_not_true_iff
      (__smtx_model_eval M (__eo_to_smt body))
      (__smtx_model_eval M (__eo_to_smt body'))
      ((RuleProofs.smt_value_rel_iff_model_eval_eq_true
        (__smtx_model_eval M (__eo_to_smt body))
        (__smtx_model_eval M (__eo_to_smt body'))).mp
        (RuleProofs.eo_interprets_eq_rel M body body' hEq))

private theorem eo_to_smt_exists_eval_true_iff_of_body_true_iff
    (M : SmtModel) (body body' : SmtTerm)
    (hBody :
      ∀ N, model_wf N ->
        model_agrees_on_globals M N ->
        (__smtx_model_eval N body = SmtValue.Boolean true ↔
          __smtx_model_eval N body' = SmtValue.Boolean true)) :
    ∀ (xs : Term) (N : SmtModel),
      QuantifierBinderTypesWf xs ->
      model_wf N ->
      model_agrees_on_globals M N ->
      (__smtx_model_eval N (__eo_to_smt_exists xs body) =
          SmtValue.Boolean true ↔
        __smtx_model_eval N (__eo_to_smt_exists xs body') =
          SmtValue.Boolean true)
  | Term.__eo_List_nil, N, _hBindersWf, hN, hAgree => hBody N hN hAgree
  | Term.Apply f xs, N, hBindersWf, hN, hAgree => by
      cases f
      all_goals
        try simp [__eo_to_smt_exists, __smtx_model_eval]
      case Apply f' head =>
        cases f'
        all_goals
          try simp [__eo_to_smt_exists, __smtx_model_eval]
        case __eo_List_cons =>
          cases head
          all_goals
            try simp [__eo_to_smt_exists, __smtx_model_eval]
          case Var name T =>
            cases name
            all_goals
              try simp [__eo_to_smt_exists, __smtx_model_eval]
            case String s =>
              have hBinderWf :
                  __smtx_type_wf (__eo_to_smt_type T) = true ∧
                    QuantifierBinderTypesWf xs := by
                simpa [QuantifierBinderTypesWf] using hBindersWf
              constructor
              · intro hEval
                by_cases hSat :
                    ∃ v : SmtValue,
                      __smtx_typeof_value v = __eo_to_smt_type T ∧
                        __smtx_value_canonical v = true ∧
                        __smtx_model_eval
                            (native_model_push N s (__eo_to_smt_type T) v)
                            (__eo_to_smt_exists xs body) =
                          SmtValue.Boolean true
                · have hSat' :
                      ∃ v : SmtValue,
                        __smtx_typeof_value v = __eo_to_smt_type T ∧
                          __smtx_value_canonical v = true ∧
                          __smtx_model_eval
                              (native_model_push N s (__eo_to_smt_type T) v)
                              (__eo_to_smt_exists xs body') =
                            SmtValue.Boolean true := by
                    rcases hSat with ⟨v, hvTy, hvCan, hvEval⟩
                    refine ⟨v, hvTy, hvCan, ?_⟩
                    exact
                      (eo_to_smt_exists_eval_true_iff_of_body_true_iff
                        M body body' hBody xs
                        (native_model_push N s (__eo_to_smt_type T) v)
                        hBinderWf.2
                        (model_total_typed_push hN s (__eo_to_smt_type T) v
                          hBinderWf.1 hvTy
                          (by simpa [value_canonical] using hvCan))
                        (model_agrees_on_globals_trans hAgree
                          (model_agrees_on_globals_push N s (__eo_to_smt_type T) v))).1
                        hvEval
                  simp [hSat']
                · simp [hSat] at hEval
              · intro hEval
                by_cases hSat :
                    ∃ v : SmtValue,
                      __smtx_typeof_value v = __eo_to_smt_type T ∧
                        __smtx_value_canonical v = true ∧
                        __smtx_model_eval
                            (native_model_push N s (__eo_to_smt_type T) v)
                            (__eo_to_smt_exists xs body') =
                          SmtValue.Boolean true
                · have hSat' :
                      ∃ v : SmtValue,
                        __smtx_typeof_value v = __eo_to_smt_type T ∧
                          __smtx_value_canonical v = true ∧
                          __smtx_model_eval
                              (native_model_push N s (__eo_to_smt_type T) v)
                              (__eo_to_smt_exists xs body) =
                            SmtValue.Boolean true := by
                    rcases hSat with ⟨v, hvTy, hvCan, hvEval⟩
                    refine ⟨v, hvTy, hvCan, ?_⟩
                    exact
                      (eo_to_smt_exists_eval_true_iff_of_body_true_iff
                        M body body' hBody xs
                        (native_model_push N s (__eo_to_smt_type T) v)
                        hBinderWf.2
                        (model_total_typed_push hN s (__eo_to_smt_type T) v
                          hBinderWf.1 hvTy
                          (by simpa [value_canonical] using hvCan))
                        (model_agrees_on_globals_trans hAgree
                          (model_agrees_on_globals_push N s (__eo_to_smt_type T) v))).2
                        hvEval
                  simp [hSat']
                · simp [hSat] at hEval
  | Term.UOp _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UOp1 _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UOp2 _ _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UOp3 _ _ _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.__eo_List, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.__eo_List_cons, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Bool, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Boolean _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Numeral _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Rational _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.String _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Binary _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Type, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Stuck, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.FunType, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.Var _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DatatypeType _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DatatypeTypeRef _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DtcAppType _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DtCons _ _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.DtSel _ _ _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.USort _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
  | Term.UConst _ _, N, _hBindersWf, hN, hAgree => by
      simp [__eo_to_smt_exists, __smtx_model_eval]
termination_by xs N _ _ _ => xs

private theorem eo_to_smt_exists_eval_eq_of_body_true_iff_cons
    (M : SmtModel) (body body' : SmtTerm)
    (hBody :
      ∀ N, model_wf N ->
        model_agrees_on_globals M N ->
        (__smtx_model_eval N body = SmtValue.Boolean true ↔
          __smtx_model_eval N body' = SmtValue.Boolean true))
    (head tail : Term) (N : SmtModel)
    (hBindersWf :
      QuantifierBinderTypesWf
        (Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
    (hN : model_wf N)
    (hAgree : model_agrees_on_globals M N) :
    __smtx_model_eval N
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons head) tail) body) =
      __smtx_model_eval N
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons head) tail) body') := by
  cases head
  all_goals
    try simp [__eo_to_smt_exists, __smtx_model_eval]
  case Var name T =>
    cases name
    all_goals
      try simp [__eo_to_smt_exists, __smtx_model_eval]
    case String s =>
      have hBinderWf :
          __smtx_type_wf (__eo_to_smt_type T) = true ∧
            QuantifierBinderTypesWf tail := by
        simpa [QuantifierBinderTypesWf] using hBindersWf
      by_cases hSat :
          ∃ v : SmtValue,
            __smtx_typeof_value v = __eo_to_smt_type T ∧
              __smtx_value_canonical v = true ∧
              __smtx_model_eval
                  (native_model_push N s (__eo_to_smt_type T) v)
                  (__eo_to_smt_exists tail body) =
                SmtValue.Boolean true
      · have hSat' :
            ∃ v : SmtValue,
              __smtx_typeof_value v = __eo_to_smt_type T ∧
                __smtx_value_canonical v = true ∧
                __smtx_model_eval
                    (native_model_push N s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists tail body') =
                  SmtValue.Boolean true := by
          rcases hSat with ⟨v, hvTy, hvCan, hvEval⟩
          refine ⟨v, hvTy, hvCan, ?_⟩
          exact
            (eo_to_smt_exists_eval_true_iff_of_body_true_iff
              M body body' hBody tail
              (native_model_push N s (__eo_to_smt_type T) v)
              hBinderWf.2
              (model_total_typed_push hN s (__eo_to_smt_type T) v
                hBinderWf.1 hvTy
                (by simpa [value_canonical] using hvCan))
              (model_agrees_on_globals_trans hAgree
                (model_agrees_on_globals_push N s (__eo_to_smt_type T) v))).1
              hvEval
        simp [hSat, hSat']
      · have hSat' :
            ¬ ∃ v : SmtValue,
              __smtx_typeof_value v = __eo_to_smt_type T ∧
                __smtx_value_canonical v = true ∧
                __smtx_model_eval
                    (native_model_push N s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists tail body') =
                  SmtValue.Boolean true := by
          intro hSat'
          apply hSat
          rcases hSat' with ⟨v, hvTy, hvCan, hvEval⟩
          refine ⟨v, hvTy, hvCan, ?_⟩
          exact
            (eo_to_smt_exists_eval_true_iff_of_body_true_iff
              M body body' hBody tail
              (native_model_push N s (__eo_to_smt_type T) v)
              hBinderWf.2
              (model_total_typed_push hN s (__eo_to_smt_type T) v
                hBinderWf.1 hvTy
                (by simpa [value_canonical] using hvCan))
              (model_agrees_on_globals_trans hAgree
                (model_agrees_on_globals_push N s (__eo_to_smt_type T) v))).2
              hvEval
        simp [hSat, hSat']

private abbrev mkBinderApp (op : UserOp) (xs body : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp op) xs) body

private theorem premiseEvidence_lifts_congruence_over_binders
    (M : SmtModel) (hM : model_wf M)
    (premises : List Term)
    (op : UserOp) (xs body body' : Term)
    (hOp : op = UserOp.forall ∨ op = UserOp.exists) :
    RulePremiseEvidence M premises ->
    mkEq body body' ∈ premises ->
    QuantifierBinderTypesWf xs ->
    RuleProofs.eo_has_bool_type (mkEq (mkBinderApp op xs body)
      (mkBinderApp op xs body')) ->
    eo_interprets M (mkEq (mkBinderApp op xs body)
      (mkBinderApp op xs body')) true := by
  intro hEvidence hBodyMem hBinderTypesWf hEqBool
  -- The semantic work here is exactly the old binder-congruence shortcut, but
  -- the required checker-side fact is now explicit: the body equality premise
  -- is available in every variable-variant model via `true_in_var_model`.
  have hBodyAny :
      ∀ N, model_wf N ->
        model_agrees_on_globals M N ->
        eo_interprets N (mkEq body body') true := by
    intro N hN hAgree
    exact hEvidence.true_in_var_model N hN hAgree
      (mkEq body body') hBodyMem
  have hLeftTrans :
      RuleProofs.eo_has_smt_translation (mkBinderApp op xs body) := by
    have hLeftNN :=
      (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (mkBinderApp op xs body) (mkBinderApp op xs body') hEqBool).2
    simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkBinderApp op xs body)))
        (__smtx_model_eval M (__eo_to_smt (mkBinderApp op xs body'))) := by
    cases hOp with
    | inl hForall =>
        subst hForall
        have hNotBody :
            ∀ N, model_wf N ->
              model_agrees_on_globals M N ->
              (__smtx_model_eval N (SmtTerm.not (__eo_to_smt body)) =
                  SmtValue.Boolean true ↔
                __smtx_model_eval N (SmtTerm.not (__eo_to_smt body')) =
                  SmtValue.Boolean true) := by
          intro N hN hAgree
          exact eo_eq_true_not_eval_true_iff N body body' (hBodyAny N hN hAgree)
        rcases forall_translation_arg_is_cons xs body hLeftTrans with
          ⟨head, tail, hXs⟩
        subst hXs
        have hInner :
            __smtx_model_eval M
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
                  (SmtTerm.not (__eo_to_smt body))) =
              __smtx_model_eval M
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
                  (SmtTerm.not (__eo_to_smt body'))) :=
          eo_to_smt_exists_eval_eq_of_body_true_iff_cons
            M (SmtTerm.not (__eo_to_smt body))
            (SmtTerm.not (__eo_to_smt body')) hNotBody
            head tail M hBinderTypesWf hM (model_agrees_on_globals_refl M)
        rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
        change __smtx_model_eval_eq
          (__smtx_model_eval M
            (SmtTerm.not
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
                (SmtTerm.not (__eo_to_smt body)))))
          (__smtx_model_eval M
            (SmtTerm.not
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
                (SmtTerm.not (__eo_to_smt body'))))) =
            SmtValue.Boolean true
        rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_7]
        rw [hInner]
        exact RuleProofs.smtx_model_eval_eq_refl
          (__smtx_model_eval_not
            (__smtx_model_eval M
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
                (SmtTerm.not (__eo_to_smt body')))))
    | inr hExists =>
        subst hExists
        have hBodyTrue :
            ∀ N, model_wf N ->
              model_agrees_on_globals M N ->
              (__smtx_model_eval N (__eo_to_smt body) =
                  SmtValue.Boolean true ↔
                __smtx_model_eval N (__eo_to_smt body') =
                  SmtValue.Boolean true) := by
          intro N hN hAgree
          exact eo_eq_true_bool_eval_true_iff N body body' (hBodyAny N hN hAgree)
        rcases exists_translation_arg_is_cons xs body hLeftTrans with
          ⟨head, tail, hXs⟩
        subst hXs
        have hEval :
            __smtx_model_eval M
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
                  (__eo_to_smt body)) =
              __smtx_model_eval M
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
                  (__eo_to_smt body')) :=
          eo_to_smt_exists_eval_eq_of_body_true_iff_cons
            M (__eo_to_smt body) (__eo_to_smt body') hBodyTrue
            head tail M hBinderTypesWf hM (model_agrees_on_globals_refl M)
        rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
        change __smtx_model_eval_eq
          (__smtx_model_eval M
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
              (__eo_to_smt body)))
          (__smtx_model_eval M
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
              (__eo_to_smt body'))) =
            SmtValue.Boolean true
        rw [hEval]
        exact RuleProofs.smtx_model_eval_eq_refl
          (__smtx_model_eval M
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
              (__eo_to_smt body')))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkBinderApp op xs body) (mkBinderApp op xs body') hEqBool hRel

private theorem stable_lifts_congruence_over_binders
    (M : SmtModel) (hM : model_wf M)
    (op : UserOp) (xs body body' : Term)
    (hOp : op = UserOp.forall ∨ op = UserOp.exists) :
    StableInAnyVarModel M (mkEq body body') ->
    QuantifierBinderTypesWf xs ->
    RuleProofs.eo_has_bool_type (mkEq (mkBinderApp op xs body)
      (mkBinderApp op xs body')) ->
    eo_interprets M (mkEq (mkBinderApp op xs body)
      (mkBinderApp op xs body')) true := by
  intro hBodyStable hBinderTypesWf hEqBool
  have hEvidence :
      RulePremiseEvidence M [mkEq body body'] := by
    refine ⟨?_, ?_⟩
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst q
      exact hBodyStable M hM (model_agrees_on_globals_refl M)
    · intro N hN hAgree q hq
      simp only [List.mem_singleton] at hq
      subst q
      exact hBodyStable N hN hAgree
  exact premiseEvidence_lifts_congruence_over_binders
    M hM [mkEq body body'] op xs body body' hOp hEvidence
    (by simp) hBinderTypesWf hEqBool

theorem congEvidenceSpine_quantifier_eq_true
    (M : SmtModel) (hM : model_wf M)
    (premises : List Term)
    (op : UserOp) (xs body rhs : Term)
    (hOp : op = UserOp.forall ∨ op = UserOp.exists) :
    RulePremiseEvidence M premises ->
    QuantifierBinderTypesWf xs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp op) xs) body) rhs) ->
    CongEvidenceSpine M premises
      (Term.Apply (Term.Apply (Term.UOp op) xs) body) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp op) xs) body) rhs) true := by
  intro hEvidence hBinderTypesWf hEqBool hSpine
  cases hSpine with
  | refl _ =>
      exact RuleProofs.eo_interprets_eq_of_rel M
        (Term.Apply (Term.Apply (Term.UOp op) xs) body)
        (Term.Apply (Term.Apply (Term.UOp op) xs) body)
        hEqBool
        (RuleProofs.smt_value_rel_refl _)
  | @app f g x y hHead hBodyMem hBodyTrue =>
      have hHeadTrue : CongTrueSpine M
          (Term.Apply (Term.UOp op) xs) g :=
        congTrueSpine_of_congEvidenceSpine M premises hEvidence hHead
      rcases congTrueSpine_unary_uop_inv M op xs g hHeadTrue with
        ⟨ys, hGEq, hList⟩
      subst hGEq
      cases hList with
      | inl hListEq =>
          subst hListEq
          exact
            premiseEvidence_lifts_congruence_over_binders
              M hM premises op xs body y hOp hEvidence hBodyMem
              hBinderTypesWf
              (by simpa [mkEq, mkBinderApp] using hEqBool)
      | inr hListTrue =>
          have hTrans :
              RuleProofs.eo_has_smt_translation
                (Term.Apply (Term.Apply (Term.UOp op) xs) body) := by
            have hLeftNN :=
              (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                (Term.Apply (Term.Apply (Term.UOp op) xs) body)
                (Term.Apply (Term.Apply (Term.UOp op) ys) y) hEqBool).2
            simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
          have hListBool : RuleProofs.eo_has_bool_type (mkEq xs ys) :=
            RuleProofs.eo_has_bool_type_of_interprets_true M (mkEq xs ys)
              hListTrue
          cases hOp with
          | inl hForall =>
              subst hForall
              exact False.elim
                (forall_arg_not_eq_bool_of_translation xs ys body hTrans
                  (by simpa [mkEq] using hListBool))
          | inr hExists =>
              subst hExists
              exact False.elim
                (exists_arg_not_eq_bool_of_translation xs ys body hTrans
                  (by simpa [mkEq] using hListBool))

theorem congStableSpine_quantifier_eq_true
    (M : SmtModel) (hM : model_wf M)
    (op : UserOp) (xs body rhs : Term)
    (hOp : op = UserOp.forall ∨ op = UserOp.exists) :
    QuantifierBinderTypesWf xs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp op) xs) body) rhs) ->
    CongStableSpine M
      (Term.Apply (Term.Apply (Term.UOp op) xs) body) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp op) xs) body) rhs) true := by
  intro hBinderTypesWf hEqBool hSpine
  cases hSpine with
  | refl _ =>
      exact RuleProofs.eo_interprets_eq_of_rel M
        (Term.Apply (Term.Apply (Term.UOp op) xs) body)
        (Term.Apply (Term.Apply (Term.UOp op) xs) body)
        hEqBool
        (RuleProofs.smt_value_rel_refl _)
  | @app f g x y hHead hBodyStable =>
      have hHeadTrue : CongTrueSpine M
          (Term.Apply (Term.UOp op) xs) g :=
        congTrueSpine_of_congStableSpine M hM hHead
      rcases congTrueSpine_unary_uop_inv M op xs g hHeadTrue with
        ⟨ys, hGEq, hList⟩
      subst hGEq
      cases hList with
      | inl hListEq =>
          subst hListEq
          exact
            stable_lifts_congruence_over_binders
              M hM op xs body y hOp hBodyStable hBinderTypesWf
              (by simpa [mkEq, mkBinderApp] using hEqBool)
      | inr hListTrue =>
          have hTrans :
              RuleProofs.eo_has_smt_translation
                (Term.Apply (Term.Apply (Term.UOp op) xs) body) := by
            have hLeftNN :=
              (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                (Term.Apply (Term.Apply (Term.UOp op) xs) body)
                (Term.Apply (Term.Apply (Term.UOp op) ys) y) hEqBool).2
            simpa [RuleProofs.eo_has_smt_translation] using hLeftNN
          have hListBool : RuleProofs.eo_has_bool_type (mkEq xs ys) :=
            RuleProofs.eo_has_bool_type_of_interprets_true M (mkEq xs ys)
              hListTrue
          cases hOp with
          | inl hForall =>
              subst hForall
              exact False.elim
                (forall_arg_not_eq_bool_of_translation xs ys body hTrans
                  (by simpa [mkEq] using hListBool))
          | inr hExists =>
              subst hExists
              exact False.elim
                (exists_arg_not_eq_bool_of_translation xs ys body hTrans
                  (by simpa [mkEq] using hListBool))

def NotTopLevelQuantifier (t : Term) : Prop :=
  (∀ xs body,
    t ≠ Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ∧
  (∀ xs body,
    t ≠ Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)

private theorem typeof_exists_eq_local
    (s : native_String) (T : SmtType) (t : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None := by
  rw [smtx_typeof_exists_term_eq]

private theorem quantifierBinderTypesWf_of_eo_to_smt_exists_non_none :
    ∀ (xs : Term) (body : SmtTerm),
      __smtx_typeof (__eo_to_smt_exists xs body) ≠ SmtType.None ->
      QuantifierBinderTypesWf xs := by
  intro xs body hNN
  cases xs <;> try exact True.intro
  case Apply f tail =>
    cases f <;> try exact True.intro
    case Apply g head =>
      cases g <;> try exact True.intro
      case __eo_List_cons =>
        cases head <;> try exact True.intro
        case Var name T =>
          cases name <;> try exact True.intro
          case String s =>
            have hExistsNN :
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail body)) ≠ SmtType.None := by
              simpa [__eo_to_smt_exists] using hNN
            have hTermNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists tail body)) := by
              unfold term_has_non_none_type
              exact hExistsNN
            have hTailBool :
                __smtx_typeof (__eo_to_smt_exists tail body) =
                  SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hTermNN
            have hGuardNN :
                __smtx_typeof_guard_wf (__eo_to_smt_type T)
                    SmtType.Bool ≠
                  SmtType.None := by
              intro hGuardNone
              apply hExistsNN
              rw [typeof_exists_eq_local]
              simp [hTailBool, hGuardNone, native_ite, native_Teq]
            have hHeadWf :
                __smtx_type_wf (__eo_to_smt_type T) = true :=
              smtx_typeof_guard_wf_wf_of_non_none
                (__eo_to_smt_type T) SmtType.Bool hGuardNN
            have hTailWf : QuantifierBinderTypesWf tail :=
              quantifierBinderTypesWf_of_eo_to_smt_exists_non_none tail body
                (by
                  rw [hTailBool]
                  simp)
            exact ⟨hHeadWf, hTailWf⟩

private theorem eo_to_smt_forall_non_nil_eq
    {xs body : Term}
    (hxs : xs ≠ Term.__eo_List_nil) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) =
      SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body))) := by
  cases xs <;> first | exact False.elim (hxs rfl) | rfl

private theorem eo_to_smt_exists_non_nil_eq
    {xs body : Term}
    (hxs : xs ≠ Term.__eo_List_nil) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) =
      __eo_to_smt_exists xs (__eo_to_smt body) := by
  cases xs <;> first | exact False.elim (hxs rfl) | rfl

theorem quantifierBinderTypesWf_of_forall_translation
    (xs body : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ->
    QuantifierBinderTypesWf xs := by
  intro hTrans
  by_cases hxs : xs = Term.__eo_List_nil
  · subst hxs
    simp [QuantifierBinderTypesWf]
  · have hNotNN :
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))) ≠
          SmtType.None := by
      simpa [RuleProofs.eo_has_smt_translation,
        eo_to_smt_forall_non_nil_eq hxs] using hTrans
    have hChainBool :
        __smtx_typeof
            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body))) =
          SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none _ hNotNN
    exact
      quantifierBinderTypesWf_of_eo_to_smt_exists_non_none
        xs (SmtTerm.not (__eo_to_smt body)) (by
          rw [hChainBool]
          simp)

theorem quantifierBinderTypesWf_of_exists_translation
    (xs body : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ->
    QuantifierBinderTypesWf xs := by
  intro hTrans
  by_cases hxs : xs = Term.__eo_List_nil
  · subst hxs
    simp [QuantifierBinderTypesWf]
  · have hChainNN :
        __smtx_typeof (__eo_to_smt_exists xs (__eo_to_smt body)) ≠
          SmtType.None := by
      simpa [RuleProofs.eo_has_smt_translation,
        eo_to_smt_exists_non_nil_eq hxs] using hTrans
    exact
      quantifierBinderTypesWf_of_eo_to_smt_exists_non_none
        xs (__eo_to_smt body) hChainNN

private theorem smtx_typeof_apply_none_head (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  simp [__smtx_typeof, __smtx_typeof_apply]

private theorem smtx_typeof_apply_not_head_none (f x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.not f) x) = SmtType.None := by
  cases hTy : __smtx_typeof f <;>
    simp [__smtx_typeof, __smtx_typeof_apply,
      hTy, native_ite, native_Teq]

private theorem smtx_typeof_apply_exists_head_none
    (s : native_String) (T : SmtType) (f x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.exists s T f) x) =
      SmtType.None := by
  cases hTy : __smtx_typeof f <;>
    cases hWf : __smtx_type_wf T <;>
    simp [__smtx_typeof, __smtx_typeof_apply,
      hTy, native_ite, native_Teq,
      __smtx_typeof_guard_wf, hWf]

theorem smtx_typeof_apply_forall_top_none (xs body x : Term) :
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body))
          (__eo_to_smt x)) =
      SmtType.None := by
  cases xs
  case __eo_List_nil =>
    change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
      SmtType.None
    exact smtx_typeof_apply_none_head (__eo_to_smt x)
  all_goals
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.not
              (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt body))))
            (__eo_to_smt x)) =
        SmtType.None
    exact smtx_typeof_apply_not_head_none
      (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt body))) (__eo_to_smt x)

theorem smtx_typeof_apply_exists_top_none (xs body x : Term) :
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body))
          (__eo_to_smt x)) =
      SmtType.None := by
  cases xs
  case __eo_List_nil =>
    change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
      SmtType.None
    exact smtx_typeof_apply_none_head (__eo_to_smt x)
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            change
              __smtx_typeof
                  (SmtTerm.Apply
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt body)))
                    (__eo_to_smt x)) =
                SmtType.None
            exact smtx_typeof_apply_exists_head_none s
              (__eo_to_smt_type T)
              (__eo_to_smt_exists tail (__eo_to_smt body)) (__eo_to_smt x)
          all_goals
            change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
              SmtType.None
            exact smtx_typeof_apply_none_head (__eo_to_smt x)
        all_goals
          change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
            SmtType.None
          exact smtx_typeof_apply_none_head (__eo_to_smt x)
      all_goals
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
          SmtType.None
        exact smtx_typeof_apply_none_head (__eo_to_smt x)
    all_goals
      change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
        SmtType.None
      exact smtx_typeof_apply_none_head (__eo_to_smt x)
  all_goals
    change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
      SmtType.None
    exact smtx_typeof_apply_none_head (__eo_to_smt x)

theorem no_translation_of_eo_apply_type_none {f x : Term} :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x) ->
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) =
      SmtType.None ->
    RuleProofs.eo_has_smt_translation (Term.Apply f x) ->
    False := by
  intro hToSmt hTy
  exact no_translation_of_smt_type_none (t := Term.Apply f x) (by
    rw [hToSmt]
    exact hTy)

theorem no_bool_eq_left_of_eo_apply_type_none {f x rhs : Term} :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x) ->
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) =
      SmtType.None ->
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply f x) rhs) ->
    False := by
  intro hToSmt hTy
  exact no_bool_eq_left_of_smt_type_none
    (t := Term.Apply f x) (rhs := rhs) (by
      rw [hToSmt]
      exact hTy)

theorem no_translation_of_eo_apply_none_head {f x : Term} :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply SmtTerm.None (__eo_to_smt x) ->
    RuleProofs.eo_has_smt_translation (Term.Apply f x) ->
    False := by
  intro hToSmt
  exact no_translation_of_smt_type_none (t := Term.Apply f x) (by
    rw [hToSmt]
    simp [__smtx_typeof, __smtx_typeof_apply])

theorem no_bool_eq_left_of_eo_apply_none_head {f x rhs : Term} :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply SmtTerm.None (__eo_to_smt x) ->
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply f x) rhs) ->
    False := by
  intro hToSmt
  exact no_bool_eq_left_of_smt_type_none
    (t := Term.Apply f x) (rhs := rhs) (by
      rw [hToSmt]
      simp [__smtx_typeof, __smtx_typeof_apply])

set_option maxHeartbeats 100000000 in
/-- The `@strings_occur_index` choice translation collapses to type `None`
whenever its occurrence-count argument does. -/
private theorem occur_index_translation_type_none_of_last_none
    (s t n : SmtTerm) (hn : __smtx_typeof n = SmtType.None) :
    __smtx_typeof (SmtTerm._at_strings_occur_index s t n) =
      SmtType.None := by
  have hTy :
      __smtx_typeof (SmtTerm._at_strings_occur_index s t n) =
        __smtx_typeof_str_indexof (__smtx_typeof s) (__smtx_typeof t)
          (__smtx_typeof n) := by
    rw [__smtx_typeof.eq_def] <;> simp only
  rw [hTy, hn]
  unfold __smtx_typeof_str_indexof
  split <;> simp_all

private theorem occur_index_re_translation_type_none_of_last_none
    (s t n : SmtTerm) (hn : __smtx_typeof n = SmtType.None) :
    __smtx_typeof (SmtTerm._at_strings_occur_index_re s t n) =
      SmtType.None := by
  have hTy :
      __smtx_typeof (SmtTerm._at_strings_occur_index_re s t n) =
        native_ite
          (native_Teq (__smtx_typeof s) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof n) SmtType.Int)
              SmtType.Int SmtType.None)
            SmtType.None)
          SmtType.None := by
    rw [__smtx_typeof.eq_def] <;> simp only
  rw [hTy, hn]
  simp [native_ite, native_Teq]

theorem eo_apply_apply_arg_has_translation_of_has_translation
    (f z x : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply f z) x) ->
    RuleProofs.eo_has_smt_translation x := by
  intro hTrans
  have hWhole := hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans ⊢
  intro hx
  cases f with
  | UOp op =>
      cases op
      case «or» =>
        exact hTrans (smt_bool_binop_type_none_of_second_arg_none
          SmtTerm.or (__eo_to_smt z) (__eo_to_smt x)
          (fun h => (smt_typeof_or_args_bool_of_non_none
            (__eo_to_smt z) (__eo_to_smt x) h).2) hx)
      case «and» =>
        exact hTrans (smt_bool_binop_type_none_of_second_arg_none
          SmtTerm.and (__eo_to_smt z) (__eo_to_smt x)
          (fun h => (smt_typeof_and_args_bool_of_non_none
            (__eo_to_smt z) (__eo_to_smt x) h).2) hx)
      case imp =>
        exact hTrans (smt_bool_binop_type_none_of_second_arg_none
          SmtTerm.imp (__eo_to_smt z) (__eo_to_smt x)
          (fun h => (smt_typeof_imp_args_bool_of_non_none
            (__eo_to_smt z) (__eo_to_smt x) h).2) hx)
      case xor =>
        exact hTrans (smt_bool_binop_type_none_of_second_arg_none
          SmtTerm.xor (__eo_to_smt z) (__eo_to_smt x)
          (fun h => (smt_typeof_xor_args_bool_of_non_none
            (__eo_to_smt z) (__eo_to_smt x) h).2) hx)
      case eq =>
        exact hTrans (smt_eq_type_none_of_second_arg_none
          (__eo_to_smt z) (__eo_to_smt x) hx)
      case plus =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.plus (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_binop_args_non_reg_of_non_none SmtTerm.plus
            (by intro a b; exact typeof_plus_eq a b)) hx)
      case neg =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.neg (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_binop_args_non_reg_of_non_none SmtTerm.neg
            (by intro a b; exact typeof_neg_eq a b)) hx)
      case mult =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.mult (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_binop_args_non_reg_of_non_none SmtTerm.mult
            (by intro a b; exact typeof_mult_eq a b)) hx)
      case lt =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.lt (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.lt
            SmtType.Bool (by intro a b; exact typeof_lt_eq a b)) hx)
      case leq =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.leq (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.leq
            SmtType.Bool (by intro a b; exact typeof_leq_eq a b)) hx)
      case gt =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.gt (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.gt
            SmtType.Bool (by intro a b; exact typeof_gt_eq a b)) hx)
      case geq =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.geq (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.geq
            SmtType.Bool (by intro a b; exact typeof_geq_eq a b)) hx)
      case div =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.div (__eo_to_smt z) (__eo_to_smt x)
          (int_binop_args_non_reg_of_non_none SmtTerm.div SmtType.Int
            (by intro a b; exact typeof_div_eq a b)) hx)
      case mod =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.mod (__eo_to_smt z) (__eo_to_smt x)
          (int_binop_args_non_reg_of_non_none SmtTerm.mod SmtType.Int
            (by intro a b; exact typeof_mod_eq a b)) hx)
      case divisible =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.divisible (__eo_to_smt z) (__eo_to_smt x)
          (int_binop_args_non_reg_of_non_none SmtTerm.divisible SmtType.Bool
            (by intro a b; exact typeof_divisible_eq a b)) hx)
      case div_total =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.div_total (__eo_to_smt z) (__eo_to_smt x)
          (int_binop_args_non_reg_of_non_none SmtTerm.div_total SmtType.Int
            (by intro a b; exact typeof_div_total_eq a b)) hx)
      case mod_total =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.mod_total (__eo_to_smt z) (__eo_to_smt x)
          (int_binop_args_non_reg_of_non_none SmtTerm.mod_total SmtType.Int
            (by intro a b; exact typeof_mod_total_eq a b)) hx)
      case select =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.select (__eo_to_smt z) (__eo_to_smt x)
          select_args_non_reg_of_non_none hx)
      case concat =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.concat (__eo_to_smt z) (__eo_to_smt x)
          bv_concat_args_non_reg_of_non_none hx)
      case bvand =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvand (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvand
            (by intro a b; rw [__smtx_typeof.eq_40])) hx)
      case bvor =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvor (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvor
            (by intro a b; rw [__smtx_typeof.eq_41])) hx)
      case bvnand =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvnand (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvnand
            (by intro a b; rw [__smtx_typeof.eq_42])) hx)
      case bvnor =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvnor (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvnor
            (by intro a b; rw [__smtx_typeof.eq_43])) hx)
      case bvxor =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvxor (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvxor
            (by intro a b; rw [__smtx_typeof.eq_44])) hx)
      case bvxnor =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvxnor (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvxnor
            (by intro a b; rw [__smtx_typeof.eq_45])) hx)
      case bvcomp =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvcomp (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvcomp
            (SmtType.BitVec 1) (by intro a b; rw [__smtx_typeof.eq_46])) hx)
      case bvadd =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvadd (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvadd
            (by intro a b; rw [__smtx_typeof.eq_48])) hx)
      case bvmul =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvmul (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvmul
            (by intro a b; rw [__smtx_typeof.eq_49])) hx)
      case bvudiv =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvudiv (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvudiv
            (by intro a b; rw [__smtx_typeof.eq_50])) hx)
      case bvurem =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvurem (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvurem
            (by intro a b; rw [__smtx_typeof.eq_51])) hx)
      case bvsub =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsub (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvsub
            (by intro a b; rw [__smtx_typeof.eq_52])) hx)
      case bvsdiv =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsdiv (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvsdiv
            (by intro a b; rw [__smtx_typeof.eq_53])) hx)
      case bvsrem =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsrem (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvsrem
            (by intro a b; rw [__smtx_typeof.eq_54])) hx)
      case bvsmod =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsmod (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvsmod
            (by intro a b; rw [__smtx_typeof.eq_55])) hx)
      case bvult =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvult (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvult
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_56])) hx)
      case bvule =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvule (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvule
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_57])) hx)
      case bvugt =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvugt (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvugt
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_58])) hx)
      case bvuge =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvuge (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvuge
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_59])) hx)
      case bvslt =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvslt (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvslt
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_60])) hx)
      case bvsle =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsle (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvsle
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_61])) hx)
      case bvsgt =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsgt (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvsgt
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_62])) hx)
      case bvsge =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsge (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvsge
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_63])) hx)
      case bvshl =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvshl (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvshl
            (by intro a b; rw [__smtx_typeof.eq_64])) hx)
      case bvlshr =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvlshr (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvlshr
            (by intro a b; rw [__smtx_typeof.eq_65])) hx)
      case bvashr =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvashr (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_args_non_reg_of_non_none SmtTerm.bvashr
            (by intro a b; rw [__smtx_typeof.eq_66])) hx)
      case bvuaddo =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvuaddo (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvuaddo
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_71])) hx)
      case bvsaddo =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsaddo (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvsaddo
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_73])) hx)
      case bvumulo =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvumulo (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvumulo
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_74])) hx)
      case bvsmulo =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsmulo (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvsmulo
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_75])) hx)
      case bvusubo =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvusubo (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvusubo
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_76])) hx)
      case bvssubo =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvssubo (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvssubo
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_77])) hx)
      case bvsdivo =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.bvsdivo (__eo_to_smt z) (__eo_to_smt x)
          (bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvsdivo
            SmtType.Bool (by intro a b; rw [__smtx_typeof.eq_78])) hx)
      case bvultbv =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          (bvPredToBv SmtTerm.bvult) (__eo_to_smt z) (__eo_to_smt x)
          (bv_pred_to_bv_args_non_reg_of_non_none SmtTerm.bvult
            (by intro a b; rw [__smtx_typeof.eq_56])) hx)
      case bvsltbv =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          (bvPredToBv SmtTerm.bvslt) (__eo_to_smt z) (__eo_to_smt x)
          (bv_pred_to_bv_args_non_reg_of_non_none SmtTerm.bvslt
            (by intro a b; rw [__smtx_typeof.eq_60])) hx)
      case _at_from_bools =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          bvFromBoolsTerm (__eo_to_smt z) (__eo_to_smt x)
          bv_from_bools_args_non_reg_of_non_none hx)
      case str_concat =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.str_concat (__eo_to_smt z) (__eo_to_smt x)
          (seq_binop_args_non_reg_of_non_none SmtTerm.str_concat
            (by intro a b; exact typeof_str_concat_eq a b)) hx)
      case str_contains =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.str_contains (__eo_to_smt z) (__eo_to_smt x)
          (seq_binop_ret_args_non_reg_of_non_none SmtTerm.str_contains
            SmtType.Bool (by intro a b; exact typeof_str_contains_eq a b)) hx)
      case str_at =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.str_at (__eo_to_smt z) (__eo_to_smt x)
          str_at_args_non_reg_of_non_none hx)
      case str_prefixof =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.str_prefixof (__eo_to_smt z) (__eo_to_smt x)
          (seq_binop_ret_args_non_reg_of_non_none SmtTerm.str_prefixof
            SmtType.Bool (by intro a b; exact typeof_str_prefixof_eq a b)) hx)
      case str_suffixof =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.str_suffixof (__eo_to_smt z) (__eo_to_smt x)
          (seq_binop_ret_args_non_reg_of_non_none SmtTerm.str_suffixof
            SmtType.Bool (by intro a b; exact typeof_str_suffixof_eq a b)) hx)
      case str_lt =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.str_lt (__eo_to_smt z) (__eo_to_smt x)
          (seq_char_binop_args_non_reg_of_non_none SmtTerm.str_lt
            SmtType.Bool (by intro a b; exact typeof_str_lt_eq a b)) hx)
      case str_leq =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.str_leq (__eo_to_smt z) (__eo_to_smt x)
          (seq_char_binop_args_non_reg_of_non_none SmtTerm.str_leq
            SmtType.Bool (by intro a b; exact typeof_str_leq_eq a b)) hx)
      case re_range =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.re_range (__eo_to_smt z) (__eo_to_smt x)
          (seq_char_binop_args_non_reg_of_non_none SmtTerm.re_range
            SmtType.RegLan (by intro a b; exact typeof_re_range_eq a b)) hx)
      case re_concat =>
        exact hTrans (smt_reglan_binop_type_none_of_second_arg_none
          SmtTerm.re_concat (by intro a b; exact typeof_re_concat_eq a b)
          (__eo_to_smt z) (__eo_to_smt x) hx)
      case re_inter =>
        exact hTrans (smt_reglan_binop_type_none_of_second_arg_none
          SmtTerm.re_inter (by intro a b; exact typeof_re_inter_eq a b)
          (__eo_to_smt z) (__eo_to_smt x) hx)
      case re_union =>
        exact hTrans (smt_reglan_binop_type_none_of_second_arg_none
          SmtTerm.re_union (by intro a b; exact typeof_re_union_eq a b)
          (__eo_to_smt z) (__eo_to_smt x) hx)
      case re_diff =>
        exact hTrans (smt_reglan_binop_type_none_of_second_arg_none
          SmtTerm.re_diff (by intro a b; exact typeof_re_diff_eq a b)
          (__eo_to_smt z) (__eo_to_smt x) hx)
      case str_in_re =>
        exact hTrans (smt_seq_char_reglan_binop_type_none_of_second_arg_none
          SmtTerm.str_in_re (by intro a b; exact typeof_str_in_re_eq a b)
          (__eo_to_smt z) (__eo_to_smt x) hx)
      case seq_nth =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.seq_nth (__eo_to_smt z) (__eo_to_smt x)
          seq_nth_args_non_reg_of_non_none hx)
      case _at_strings_num_occur =>
        exact hTrans (by
          change __smtx_typeof
            (stringsNumOccurTerm (__eo_to_smt z) (__eo_to_smt x)) =
              SmtType.None
          exact smt_binop_type_none_of_second_arg_none
            stringsNumOccurTerm (__eo_to_smt z) (__eo_to_smt x)
            strings_num_occur_args_non_reg_of_non_none hx)
      case _at_strings_num_occur_re =>
        exact hTrans (by
          change
            __smtx_typeof
              (stringsNumOccurReTerm (__eo_to_smt z) (__eo_to_smt x)) =
                SmtType.None
          simp only [stringsNumOccurReTerm]
          rw [typeof_neg_eq, typeof_str_len_eq, typeof_str_len_eq,
            typeof_str_replace_re_all_eq, typeof_str_replace_re_all_eq, hx]
          cases hTeq : native_Teq (__smtx_typeof (__eo_to_smt z))
              (SmtType.Seq SmtType.Char) <;>
            simp [native_ite, native_Teq,
              __smtx_typeof_seq_op_1_ret,
              __smtx_typeof_arith_overload_op_2])
      case set_union =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.set_union (__eo_to_smt z) (__eo_to_smt x)
          (set_binop_args_non_reg_of_non_none SmtTerm.set_union
            (by intro a b; exact typeof_set_union_eq a b)) hx)
      case set_inter =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.set_inter (__eo_to_smt z) (__eo_to_smt x)
          (set_binop_args_non_reg_of_non_none SmtTerm.set_inter
            (by intro a b; exact typeof_set_inter_eq a b)) hx)
      case set_minus =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.set_minus (__eo_to_smt z) (__eo_to_smt x)
          (set_binop_args_non_reg_of_non_none SmtTerm.set_minus
            (by intro a b; exact typeof_set_minus_eq a b)) hx)
      case set_member =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.set_member (__eo_to_smt z) (__eo_to_smt x)
          set_member_args_non_reg_of_non_none hx)
      case set_subset =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.set_subset (__eo_to_smt z) (__eo_to_smt x)
          (set_binop_ret_args_non_reg_of_non_none SmtTerm.set_subset
            SmtType.Bool (by intro a b; exact typeof_set_subset_eq a b)) hx)
      case tuple =>
        have hNN :
            __smtx_typeof
                (__eo_to_smt_tuple_prepend (__eo_to_smt z)
                  (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt x)) ≠
              SmtType.None := by
          change
            __smtx_typeof
                (__eo_to_smt_tuple_prepend (__eo_to_smt z)
                  (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt x)) ≠
              SmtType.None at hTrans
          exact hTrans
        rcases tuple_prepend_tail_type_of_non_none
            (__eo_to_smt z) (__smtx_typeof (__eo_to_smt z))
            (__eo_to_smt x) hNN with
          ⟨c, hxTail⟩
        rw [hx] at hxTail
        cases hxTail
      case set_insert =>
        exact hTrans
          (eo_to_smt_set_insert_type_none_of_arg_none
            z (__eo_to_smt x) hx)
      case qdiv =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.qdiv (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.qdiv
            SmtType.Real (by intro a b; exact typeof_qdiv_eq a b)) hx)
      case qdiv_total =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.qdiv_total (__eo_to_smt z) (__eo_to_smt x)
          (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.qdiv_total
            SmtType.Real (by intro a b; exact typeof_qdiv_total_eq a b)) hx)
      case _at_array_deq_diff =>
        exact hTrans (by
          change
            __smtx_typeof
              (__eo_to_smt_array_deq_diff (__eo_to_smt z)
                (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt x)
                (__smtx_typeof (__eo_to_smt x))) = SmtType.None
          cases hz : __smtx_typeof (__eo_to_smt z) <;>
            simp [__eo_to_smt_array_deq_diff, hx,
              TranslationProofs.smtx_typeof_none])
      case _at_strings_deq_diff =>
        exact hTrans (smt_binop_type_none_of_second_arg_none
          SmtTerm.seq_diff (__eo_to_smt z) (__eo_to_smt x)
          strings_deq_diff_args_non_reg_of_non_none hx)
      case _at_strings_stoi_result =>
        exact hTrans (by
          change
            __smtx_typeof
              (stringsStoiResultTerm (__eo_to_smt z) (__eo_to_smt x)) =
              SmtType.None
          rw [stringsStoiResultTerm, typeof_ite_eq, typeof_eq_eq, hx]
          simp [__smtx_typeof_eq, __smtx_typeof_guard,
            __smtx_typeof_ite, native_ite, native_Teq])
      case _at_strings_itos_result =>
        exact hTrans (by
          change
            __smtx_typeof
              (stringsItosResultTerm (__eo_to_smt z) (__eo_to_smt x)) =
              SmtType.None
          rw [stringsItosResultTerm, typeof_ite_eq, typeof_eq_eq, hx]
          simp [__smtx_typeof_eq, __smtx_typeof_guard,
            __smtx_typeof_ite, native_ite, native_Teq])
      case _at_sets_deq_diff =>
        exact hTrans (by
          change
            __smtx_typeof
              (__eo_to_smt_sets_deq_diff (__eo_to_smt z)
                (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt x)
                (__smtx_typeof (__eo_to_smt x))) = SmtType.None
          cases hz : __smtx_typeof (__eo_to_smt z) <;>
            simp [__eo_to_smt_sets_deq_diff, hx,
              TranslationProofs.smtx_typeof_none])
      case «forall» =>
        rcases forall_translation_arg_is_cons z x hWhole with
          ⟨head, tail, hZ⟩
        subst hZ
        exact hTrans (eo_to_smt_forall_type_none_of_body_none
          (Term.Apply (Term.Apply Term.__eo_List_cons head) tail) x hx)
      case «exists» =>
        rcases exists_translation_arg_is_cons z x hWhole with
          ⟨head, tail, hZ⟩
        subst hZ
        exact hTrans
          (eo_to_smt_exists_type_none_of_body_none
            (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
            (__eo_to_smt x) hx)
      all_goals
        exact hTrans
          (eo_apply_apply_generic_type_none_of_arg_none _ _ _ (by rfl) hx)
  | UOp1 op idx =>
      cases op
      case update =>
        have hNN :
            __smtx_typeof
                (__eo_to_smt_updater (__eo_to_smt idx)
                  (__eo_to_smt z) (__eo_to_smt x)) ≠ SmtType.None := by
          change
            __smtx_typeof
                (__eo_to_smt_updater (__eo_to_smt idx)
                  (__eo_to_smt z) (__eo_to_smt x)) ≠ SmtType.None at hTrans
          exact hTrans
        rcases updater_args_non_reg_of_non_none
            (__eo_to_smt idx) (__eo_to_smt z) (__eo_to_smt x) hNN with
          ⟨_A, B, _hzA, hxB, _hANN, hBNN, _hAReg, _hBReg⟩
        rw [hx] at hxB
        exact hBNN hxB.symm
      case tuple_update =>
        have hNN :
            __smtx_typeof
                (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt z))
                  (__eo_to_smt idx) (__eo_to_smt z) (__eo_to_smt x)) ≠
              SmtType.None := by
          change
            __smtx_typeof
                (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt z))
                  (__eo_to_smt idx) (__eo_to_smt z) (__eo_to_smt x)) ≠
              SmtType.None at hTrans
          exact hTrans
        rcases tuple_update_args_non_reg_of_non_none
            (__smtx_typeof (__eo_to_smt z)) (__eo_to_smt idx)
            (__eo_to_smt z) (__eo_to_smt x) hNN with
          ⟨_A, B, _hzA, hxB, _hANN, hBNN, _hAReg, _hBReg⟩
        rw [hx] at hxB
        exact hBNN hxB.symm
      all_goals
        exact hTrans
          (eo_apply_apply_generic_type_none_of_arg_none _ _ _ (by rfl) hx)
  | Apply g y =>
      cases g with
      | UOp op =>
          cases op
          case ite =>
            exact hTrans (smt_ite_type_none_of_else_arg_none
              (__eo_to_smt y) (__eo_to_smt z) (__eo_to_smt x) hx)
          case store =>
            exact hTrans (smt_ternop_type_none_of_third_arg_none
              SmtTerm.store (__eo_to_smt y) (__eo_to_smt z) (__eo_to_smt x)
              store_args_non_reg_of_non_none hx)
          case bvite =>
            exact hTrans (smt_ite_type_none_of_else_arg_none
              (SmtTerm.eq (__eo_to_smt y) (SmtTerm.Binary 1 1))
              (__eo_to_smt z) (__eo_to_smt x) hx)
          case str_substr =>
            exact hTrans (smt_ternop_type_none_of_third_arg_none
              SmtTerm.str_substr (__eo_to_smt y) (__eo_to_smt z)
              (__eo_to_smt x) str_substr_args_non_reg_of_non_none hx)
          case str_replace =>
            exact hTrans (smt_ternop_type_none_of_third_arg_none
              SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt z)
              (__eo_to_smt x)
              (seq_triop_args_non_reg_of_non_none SmtTerm.str_replace
                (by intro a b c; exact typeof_str_replace_eq a b c)) hx)
          case str_indexof =>
            exact hTrans (smt_ternop_type_none_of_third_arg_none
              SmtTerm.str_indexof (__eo_to_smt y) (__eo_to_smt z)
              (__eo_to_smt x) str_indexof_args_non_reg_of_non_none hx)
          case str_update =>
            exact hTrans (smt_ternop_type_none_of_third_arg_none
              SmtTerm.str_update (__eo_to_smt y) (__eo_to_smt z)
              (__eo_to_smt x) str_update_args_non_reg_of_non_none hx)
          case str_replace_all =>
            exact hTrans (smt_ternop_type_none_of_third_arg_none
              SmtTerm.str_replace_all (__eo_to_smt y) (__eo_to_smt z)
              (__eo_to_smt x)
              (seq_triop_args_non_reg_of_non_none SmtTerm.str_replace_all
                (by intro a b c; exact typeof_str_replace_all_eq a b c)) hx)
          case str_replace_re =>
            exact hTrans (smt_str_replace_re_type_none_of_third_arg_none
              SmtTerm.str_replace_re
              (by intro a b c; exact typeof_str_replace_re_eq a b c)
              (__eo_to_smt y) (__eo_to_smt z) (__eo_to_smt x) hx)
          case str_replace_re_all =>
            exact hTrans (smt_str_replace_re_type_none_of_third_arg_none
              SmtTerm.str_replace_re_all
              (by intro a b c; exact typeof_str_replace_re_all_eq a b c)
              (__eo_to_smt y) (__eo_to_smt z) (__eo_to_smt x) hx)
          case str_indexof_re =>
            exact hTrans (smt_str_indexof_re_type_none_of_third_arg_none
              (__eo_to_smt y) (__eo_to_smt z) (__eo_to_smt x) hx)
          case _at_strings_occur_index =>
            exact hTrans (by
              change
                __smtx_typeof
                  (SmtTerm._at_strings_occur_index (__eo_to_smt y)
                    (__eo_to_smt z) (__eo_to_smt x)) = SmtType.None
              exact occur_index_translation_type_none_of_last_none _ _ _ hx)
          case _at_strings_occur_index_re =>
            exact hTrans (by
              change
                __smtx_typeof
                  (SmtTerm._at_strings_occur_index_re (__eo_to_smt y)
                    (__eo_to_smt z) (__eo_to_smt x)) = SmtType.None
              exact occur_index_re_translation_type_none_of_last_none
                _ _ _ hx)
          all_goals
            exact hTrans
              (eo_apply_apply_generic_type_none_of_arg_none _ _ _ (by rfl) hx)
      | Apply g' y' =>
          cases g' with
          | UOp op =>
              cases op
              case _at_strings_replace_all_result =>
                exact hTrans (by
                  change
                    __smtx_typeof
                      (SmtTerm.str_replace_all
                        (SmtTerm.str_substr (__eo_to_smt y')
                          (SmtTerm._at_strings_occur_index (__eo_to_smt y')
                            (__eo_to_smt y) (__eo_to_smt x))
                          (SmtTerm.str_len (__eo_to_smt y')))
                        (__eo_to_smt y) (__eo_to_smt z)) = SmtType.None
                  have hIdxNone :=
                    occur_index_translation_type_none_of_last_none
                      (__eo_to_smt y') (__eo_to_smt y) (__eo_to_smt x) hx
                  rw [typeof_str_replace_all_eq, typeof_str_substr_eq,
                    hIdxNone]
                  cases hA : __smtx_typeof (__eo_to_smt y') <;>
                    simp [__smtx_typeof_str_substr, __smtx_typeof_seq_op_3])
              case _at_strings_replace_re_all_result =>
                exact hTrans (by
                  change
                    __smtx_typeof
                      (SmtTerm.str_replace_re_all
                        (SmtTerm.str_substr (__eo_to_smt y')
                          (SmtTerm._at_strings_occur_index_re
                            (__eo_to_smt y') (__eo_to_smt y)
                            (__eo_to_smt x))
                          (SmtTerm.str_len (__eo_to_smt y')))
                        (__eo_to_smt y) (__eo_to_smt z)) = SmtType.None
                  have hIdxNone :=
                    occur_index_re_translation_type_none_of_last_none
                      (__eo_to_smt y') (__eo_to_smt y) (__eo_to_smt x) hx
                  rw [typeof_str_replace_re_all_eq, typeof_str_substr_eq,
                    hIdxNone]
                  cases hA : __smtx_typeof (__eo_to_smt y') <;>
                    simp [__smtx_typeof_str_substr, native_ite, native_Teq])
              all_goals
                exact hTrans
                  (eo_apply_apply_generic_type_none_of_arg_none _ _ _
                    (by rfl) hx)
          | _ =>
              exact hTrans
                (eo_apply_apply_generic_type_none_of_arg_none _ _ _
                  (by rfl) hx)
      | _ =>
          exact hTrans
            (eo_apply_apply_generic_type_none_of_arg_none _ _ _ (by rfl) hx)
  | _ =>
      exact hTrans
        (eo_apply_apply_generic_type_none_of_arg_none _ _ _ (by rfl) hx)

private theorem eo_apply_generic_type_none_of_arg_none
    (f x : Term)
    (hToSmt :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) :
    __smtx_typeof (__eo_to_smt x) = SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      SmtType.None := by
  intro hx
  rw [hToSmt]
  exact smt_apply_type_none_of_arg_none (__eo_to_smt f) (__eo_to_smt x) hx

theorem congTypeSpine_uop_apply_none_head_eq_has_bool_type
    (op : UserOp) (x rhs : Term)
    (hToSmt :
      __eo_to_smt (Term.Apply (Term.UOp op) x) =
        SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) x) ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp op) x) rhs) := by
  intro hTrans
  exact False.elim
    (no_translation_of_eo_apply_none_head
      (f := Term.UOp op) (x := x) hToSmt hTrans)

theorem congTrueSpine_uop_apply_none_head_eq_true
    (M : SmtModel) (op : UserOp) (x rhs : Term)
    (hToSmt :
      __eo_to_smt (Term.Apply (Term.UOp op) x) =
        SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) :
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply (Term.UOp op) x) rhs) ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp op) x) rhs) true := by
  intro hEqBool
  exact False.elim
    (no_bool_eq_left_of_eo_apply_none_head
      (f := Term.UOp op) (x := x) (rhs := rhs) hToSmt hEqBool)

theorem smt_apply_binary_typeof_none
    (w n : native_Int) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Binary w n) x) =
      SmtType.None := by
  cases hw : native_zleq 0 w <;>
    cases hn : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [__smtx_typeof, native_ite, native_and, hw, hn,
        __smtx_typeof_apply]

theorem eo_to_smt_apply_var_non_string_none_head
    {name T x : Term}
    (hName : ∀ s : native_String, name ≠ Term.String s) :
    __eo_to_smt (Term.Apply (Term.Var name T) x) =
      SmtTerm.Apply SmtTerm.None (__eo_to_smt x) := by
  cases name <;> try rfl
  case String s =>
    exact False.elim (hName s rfl)

def uopHasUnarySmtTranslation : UserOp -> Bool
  | UserOp.not
  | UserOp.distinct
  | UserOp._at_purify
  | UserOp.to_real
  | UserOp.to_int
  | UserOp.is_int
  | UserOp.abs
  | UserOp.__eoo_neg_2
  | UserOp.int_pow2
  | UserOp.int_log2
  | UserOp.int_ispow2
  | UserOp._at_int_div_by_zero
  | UserOp._at_mod_by_zero
  | UserOp._at_bvsize
  | UserOp.bvnot
  | UserOp.bvneg
  | UserOp.bvnego
  | UserOp.bvredand
  | UserOp.bvredor
  | UserOp.str_len
  | UserOp.str_rev
  | UserOp.str_to_lower
  | UserOp.str_to_upper
  | UserOp.str_to_code
  | UserOp.str_from_code
  | UserOp.str_is_digit
  | UserOp.str_to_int
  | UserOp.str_from_int
  | UserOp.str_to_re
  | UserOp._at_strings_stoi_non_digit
  | UserOp.re_mult
  | UserOp.re_plus
  | UserOp.re_opt
  | UserOp.re_comp
  | UserOp.seq_unit
  | UserOp.set_singleton
  | UserOp.set_choose
  | UserOp.set_is_empty
  | UserOp.set_is_singleton
  | UserOp._at_div_by_zero
  | UserOp.ubv_to_int
  | UserOp.sbv_to_int => true
  | _ => false

private theorem typeof_apply_none_head_eq_none
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x :=
    generic_apply_type_of_non_datatype_head
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric]
  simp [__smtx_typeof_apply]

private theorem typeof_apply_reglan_head_eq_none
    (f x : SmtTerm)
    (hF : __smtx_typeof f = SmtType.RegLan)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  have hGeneric : generic_apply_type f x :=
    generic_apply_type_of_non_datatype_head hSel hTester
  rw [hGeneric, hF]
  rfl

private theorem typeof_apply_tuple_unit_head_eq_none
    (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) x) =
      SmtType.None := by
  have hGeneric :
      generic_apply_type
        (SmtTerm.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) x :=
    generic_apply_type_of_non_datatype_head
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric]
  simp only [__eo_to_smt_tuple_decl]
  rw [TranslationProofs.smtx_typeof_tuple_unit_translation]
  rfl

theorem typeof_apply_eo_to_smt_seq_empty_eq_none
    (T : SmtType) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt_seq_empty T) x) =
      SmtType.None := by
  cases T <;> try exact typeof_apply_none_head_eq_none x
  case Seq U =>
    have hGeneric : generic_apply_type (SmtTerm.seq_empty U) x :=
      generic_apply_type_of_non_datatype_head
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
    change __smtx_typeof (SmtTerm.Apply (SmtTerm.seq_empty U) x) =
      SmtType.None
    rw [hGeneric]
    cases hWf : __smtx_type_wf (SmtType.Seq U) <;>
      simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard_wf,
        native_ite, hWf]

theorem typeof_apply_eo_to_smt_set_empty_eq_none
    (T : SmtType) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt_set_empty T) x) =
      SmtType.None := by
  cases T <;> try exact typeof_apply_none_head_eq_none x
  case Set U =>
    have hGeneric : generic_apply_type (SmtTerm.set_empty U) x :=
      generic_apply_type_of_non_datatype_head
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
    change __smtx_typeof (SmtTerm.Apply (SmtTerm.set_empty U) x) =
      SmtType.None
    rw [hGeneric]
    cases hWf : __smtx_type_wf (SmtType.Set U) <;>
      simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard_wf,
        native_ite, hWf]

theorem eo_to_smt_at_bv_ne_dt_sel
    (a b : SmtTerm) :
    ∀ s d i j, SmtTerm.int_to_bv b a ≠ SmtTerm.DtSel s d i j := by
  intro s d i j h
  cases h

theorem eo_to_smt_at_bv_ne_dt_tester
    (a b : SmtTerm) :
    ∀ s d i, SmtTerm.int_to_bv b a ≠ SmtTerm.DtTester s d i := by
  intro s d i h
  cases h

private theorem eo_to_smt_quant_skolemize_ne_dt_sel
    (vs : Term) (G : SmtTerm) (n : native_Nat) :
    ∀ s d i j,
      __eo_to_smt_quantifiers_skolemize vs G n ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ k ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

private theorem eo_to_smt_quant_skolemize_ne_dt_tester
    (vs : Term) (G : SmtTerm) (n : native_Nat) :
    ∀ s d i,
      __eo_to_smt_quantifiers_skolemize vs G n ≠
        SmtTerm.DtTester s d i := by
  intro s d i
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ k ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

theorem eo_to_smt_quant_skolemize_top_ne_dt_sel
    (q idx : Term) :
    ∀ s d i j,
      __eo_to_smt (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change
            native_ite (__eo_to_smt_nat_is_valid idx)
                (__eo_to_smt_quantifiers_skolemize
                  xs (SmtTerm.not (__eo_to_smt body))
                  (__eo_to_smt_nat idx))
                SmtTerm.None =
              SmtTerm.DtSel s d i j at h
          unfold native_ite at h
          split at h <;> try cases h
          exact
            eo_to_smt_quant_skolemize_ne_dt_sel
              xs (SmtTerm.not (__eo_to_smt body))
              (__eo_to_smt_nat idx) s d i j h

theorem eo_to_smt_quant_skolemize_top_ne_dt_tester
    (q idx : Term) :
    ∀ s d i,
      __eo_to_smt (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) ≠
        SmtTerm.DtTester s d i := by
  intro s d i h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change
            native_ite (__eo_to_smt_nat_is_valid idx)
                (__eo_to_smt_quantifiers_skolemize
                  xs (SmtTerm.not (__eo_to_smt body))
                  (__eo_to_smt_nat idx))
                SmtTerm.None =
              SmtTerm.DtTester s d i at h
          unfold native_ite at h
          split at h <;> try cases h
          exact
            eo_to_smt_quant_skolemize_ne_dt_tester
              xs (SmtTerm.not (__eo_to_smt body))
              (__eo_to_smt_nat idx) s d i h

private theorem eo_to_smt_re_unfold_ne_dt_sel
    (str re : SmtTerm) (n : native_Nat) :
    ∀ s d i j,
      __eo_to_smt_re_unfold_pos_component str re n ≠
        SmtTerm.DtSel s d i j := by
  induction n generalizing str re with
  | zero =>
      intro s d i j h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro s d i j h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ s d i j h

private theorem eo_to_smt_re_unfold_ne_dt_tester
    (str re : SmtTerm) (n : native_Nat) :
    ∀ s d i,
      __eo_to_smt_re_unfold_pos_component str re n ≠
        SmtTerm.DtTester s d i := by
  induction n generalizing str re with
  | zero =>
      intro s d i h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro s d i h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ s d i h

private theorem smt_apply_type_none_of_non_function_head
    (f x : SmtTerm)
    (hGeneric : generic_apply_type f x)
    (hFun : ∀ A B, __smtx_typeof f ≠ SmtType.FunType A B)
    (hDtc : ∀ A B, __smtx_typeof f ≠ SmtType.DtcAppType A B) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  rw [hGeneric]
  cases hF : __smtx_typeof f <;> try rfl
  · exact False.elim (hFun _ _ hF)
  · exact False.elim (hDtc _ _ hF)

private theorem smtx_typeof_re_unfold_pos_component_of_non_none
    (s r : SmtTerm) (n : native_Nat)
    (hNN :
      __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) =
      SmtType.Seq SmtType.Char := by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN ⊢
      case re_concat r1 r2 =>
        have hTermNN :
            term_has_non_none_type
              (SmtTerm.str_substr s (SmtTerm.Numeral 0)
                (SmtTerm.str_indexof_re_split s r1 r2)) := by
          unfold term_has_non_none_type
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN
        rcases str_substr_args_of_non_none hTermNN with
          ⟨T, hS, hStart, hLen⟩
        have hSplitNN :
            term_has_non_none_type (SmtTerm.str_indexof_re_split s r1 r2) := by
          unfold term_has_non_none_type
          rw [hLen]
          simp
        have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
        have hT : T = SmtType.Char := by
          cases hS.symm.trans hSplitArgs.1
          rfl
        rw [typeof_str_substr_eq, hS, hStart, hLen, hT]
        simp [__smtx_typeof_str_substr]
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN ⊢
      case re_concat r1 r2 =>
        exact ih _ r2 hNN

private theorem typeof_apply_re_unfold_pos_component_head_eq_none
    (s r : SmtTerm) (n : native_Nat) (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_re_unfold_pos_component s r n) x) =
      SmtType.None := by
  exact smt_apply_type_none_of_non_function_head _ _
    (generic_apply_type_of_non_datatype_head
      (eo_to_smt_re_unfold_ne_dt_sel s r n)
      (eo_to_smt_re_unfold_ne_dt_tester s r n))
    (by
      intro A B hFun
      have hNN :
          __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠
            SmtType.None := by
        rw [hFun]
        simp
      have hTy :=
        smtx_typeof_re_unfold_pos_component_of_non_none s r n hNN
      rw [hTy] at hFun
      cases hFun)
    (by
      intro A B hDtc
      have hNN :
          __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠
            SmtType.None := by
        rw [hDtc]
        simp
      have hTy :=
        smtx_typeof_re_unfold_pos_component_of_non_none s r n hNN
      rw [hTy] at hDtc
      cases hDtc)

theorem typeof_apply_re_unfold_top_eq_none
    (str re idx x : Term) :
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt (Term._at_re_unfold_pos_component str re idx))
          (__eo_to_smt x)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_re_unfold_pos_component
              (__eo_to_smt str) (__eo_to_smt re) (__eo_to_smt_nat idx))
            SmtTerm.None)
          (__eo_to_smt x)) =
      SmtType.None
  cases __eo_to_smt_nat_is_valid idx <;>
    simp [native_ite, TranslationProofs.typeof_apply_none_eq,
      typeof_apply_re_unfold_pos_component_head_eq_none]

theorem eo_to_smt_witness_string_length_ne_dt_sel
    (T len id : Term) :
    ∀ s d i j,
      __eo_to_smt
          (Term.UOp3 UserOp3._at_witness_string_length T len id) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j h
  change
    native_ite (__eo_to_smt_nat_is_valid len)
      (native_ite (__eo_to_smt_nat_is_valid id)
        (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type T)
          (SmtTerm.eq
            (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type T)))
            (__eo_to_smt len)))
        SmtTerm.None)
        SmtTerm.None =
      SmtTerm.DtSel s d i j at h
  unfold native_ite at h
  split at h <;> try cases h
  split at h <;> cases h

theorem eo_to_smt_witness_string_length_ne_dt_tester
    (T len id : Term) :
    ∀ s d i,
      __eo_to_smt
          (Term.UOp3 UserOp3._at_witness_string_length T len id) ≠
        SmtTerm.DtTester s d i := by
  intro s d i h
  change
    native_ite (__eo_to_smt_nat_is_valid len)
      (native_ite (__eo_to_smt_nat_is_valid id)
        (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type T)
          (SmtTerm.eq
            (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type T)))
            (__eo_to_smt len)))
        SmtTerm.None)
        SmtTerm.None =
      SmtTerm.DtTester s d i at h
  unfold native_ite at h
  split at h <;> try cases h
  split at h <;> cases h

private theorem uop_apply_typeof_none_of_not_unary_smt_translation
    (op : UserOp) (x : Term) :
    uopHasUnarySmtTranslation op = false ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      SmtType.None := by
  intro hUnary
  cases op <;>
    simp [uopHasUnarySmtTranslation] at hUnary ⊢
  case re_allchar =>
    exact typeof_apply_reglan_head_eq_none _ _
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case re_none =>
    exact typeof_apply_reglan_head_eq_none _ _
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case re_all =>
    exact typeof_apply_reglan_head_eq_none _ _
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case tuple_unit =>
    exact typeof_apply_tuple_unit_head_eq_none (__eo_to_smt x)
  all_goals
    first
    | exact typeof_apply_none_head_eq_none (__eo_to_smt x)

private theorem uop_apply_typeof_none_of_arg_none
    (op : UserOp) (x : Term) :
    op ≠ UserOp.distinct ->
    __smtx_typeof (__eo_to_smt x) = SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      SmtType.None := by
  intro hDistinct hx
  match hUnary : uopHasUnarySmtTranslation op with
  | false =>
      exact uop_apply_typeof_none_of_not_unary_smt_translation op x hUnary
  | true =>
      cases op <;> simp [uopHasUnarySmtTranslation] at hUnary
      case not =>
        change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) = SmtType.None
        rw [typeof_not_eq, hx]
        rfl
      case distinct =>
        exact False.elim (hDistinct rfl)
      case _at_purify =>
        change __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) = SmtType.None
        simpa [__smtx_typeof] using hx
      case to_real =>
        change __smtx_typeof (SmtTerm.to_real (__eo_to_smt x)) = SmtType.None
        rw [typeof_to_real_eq, hx]
        rfl
      case to_int =>
        change __smtx_typeof (SmtTerm.to_int (__eo_to_smt x)) = SmtType.None
        rw [typeof_to_int_eq, hx]
        rfl
      case is_int =>
        change __smtx_typeof (SmtTerm.is_int (__eo_to_smt x)) = SmtType.None
        rw [typeof_is_int_eq, hx]
        rfl
      case abs =>
        change __smtx_typeof (SmtTerm.abs (__eo_to_smt x)) = SmtType.None
        rw [typeof_abs_eq, hx]
        rfl
      case __eoo_neg_2 =>
        change __smtx_typeof (SmtTerm.uneg (__eo_to_smt x)) = SmtType.None
        rw [typeof_uneg_eq, hx]
        rfl
      case int_pow2 =>
        change __smtx_typeof (SmtTerm.int_pow2 (__eo_to_smt x)) = SmtType.None
        rw [typeof_int_pow2_eq, hx]
        rfl
      case int_log2 =>
        change __smtx_typeof (SmtTerm.int_log2 (__eo_to_smt x)) = SmtType.None
        rw [typeof_int_log2_eq, hx]
        rfl
      case int_ispow2 =>
        change
          __smtx_typeof
            (SmtTerm.and
              (SmtTerm.geq (__eo_to_smt x) (SmtTerm.Numeral 0))
              (SmtTerm.eq (__eo_to_smt x)
                (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt x))))) =
            SmtType.None
        rw [typeof_and_eq, typeof_geq_eq, hx]
        rfl
      case _at_int_div_by_zero =>
        change
          __smtx_typeof (SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0)) =
            SmtType.None
        rw [typeof_div_eq, hx]
        rfl
      case _at_mod_by_zero =>
        change
          __smtx_typeof (SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0)) =
            SmtType.None
        rw [typeof_mod_eq, hx]
        rfl
      case _at_bvsize =>
        change
          __smtx_typeof
            (native_ite
              (native_zleq 0
                (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
              (SmtTerm._at_purify
                (SmtTerm.Numeral
                  (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
              SmtTerm.None) =
            SmtType.None
        rw [hx]
        have hle :
            native_zleq 0 (__eo_to_smt_bv_size SmtType.None) = false := by
          rfl
        simp [hle, native_ite]
      case bvnot =>
        change __smtx_typeof (SmtTerm.bvnot (__eo_to_smt x)) = SmtType.None
        simp [__smtx_typeof, hx, __smtx_typeof_bv_op_1]
      case bvneg =>
        change __smtx_typeof (SmtTerm.bvneg (__eo_to_smt x)) = SmtType.None
        simp [__smtx_typeof, hx, __smtx_typeof_bv_op_1]
      case bvnego =>
        change __smtx_typeof (SmtTerm.bvnego (__eo_to_smt x)) = SmtType.None
        simp [__smtx_typeof, hx, __smtx_typeof_bv_op_1_ret]
      case bvredand =>
        change
          __smtx_typeof
            (SmtTerm.bvcomp (__eo_to_smt x)
              (SmtTerm.bvnot
                (SmtTerm.Binary
                  (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))
                  0))) = SmtType.None
        simp [__smtx_typeof, hx, __smtx_typeof_bv_op_1,
          __smtx_typeof_bv_op_2_ret]
      case bvredor =>
        change
          __smtx_typeof
            (SmtTerm.bvnot
              (SmtTerm.bvcomp (__eo_to_smt x)
                (SmtTerm.Binary
                  (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))
                  0))) = SmtType.None
        simp [__smtx_typeof, hx, __smtx_typeof_bv_op_1,
          __smtx_typeof_bv_op_2_ret]
      case str_len =>
        change __smtx_typeof (SmtTerm.str_len (__eo_to_smt x)) = SmtType.None
        rw [typeof_str_len_eq, hx]
        rfl
      case str_rev =>
        change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt x)) = SmtType.None
        rw [typeof_str_rev_eq, hx]
        rfl
      case str_to_lower =>
        change __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_str_to_lower_eq, hx]
        rfl
      case str_to_upper =>
        change __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_str_to_upper_eq, hx]
        rfl
      case str_to_code =>
        change __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_str_to_code_eq, hx]
        rfl
      case str_from_code =>
        change __smtx_typeof (SmtTerm.str_from_code (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_str_from_code_eq, hx]
        rfl
      case str_is_digit =>
        change __smtx_typeof (SmtTerm.str_is_digit (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_str_is_digit_eq, hx]
        rfl
      case str_to_int =>
        change __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_str_to_int_eq, hx]
        rfl
      case str_from_int =>
        change __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_str_from_int_eq, hx]
        rfl
      case str_to_re =>
        change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_str_to_re_eq, hx]
        rfl
      case _at_strings_stoi_non_digit =>
        change __smtx_typeof (stringsStoiNonDigitTerm (__eo_to_smt x)) =
          SmtType.None
        rw [stringsStoiNonDigitTerm, typeof_str_indexof_re_eq, hx]
        rfl
      case re_mult =>
        change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_re_mult_eq, hx]
        rfl
      case re_plus =>
        change __smtx_typeof (SmtTerm.re_plus (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_re_plus_eq, hx]
        rfl
      case re_opt =>
        change __smtx_typeof (SmtTerm.re_opt (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_re_opt_eq, hx]
        rfl
      case re_comp =>
        change __smtx_typeof (SmtTerm.re_comp (__eo_to_smt x)) =
          SmtType.None
        rw [typeof_re_comp_eq, hx]
        rfl
      case seq_unit =>
        change __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt x)) =
          SmtType.None
        simp [__smtx_typeof, hx, __smtx_typeof_guard_wf,
          __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
          native_and, native_ite]
      case set_singleton =>
        change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt x)) =
          SmtType.None
        simp [__smtx_typeof, hx, __smtx_typeof_guard_wf,
          __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
          native_and, native_ite]
      case set_choose =>
        change
          __smtx_typeof
            (SmtTerm.map_diff (__eo_to_smt x)
              (SmtTerm.set_empty
                (__eo_to_smt_set_elem_type
                  (__smtx_typeof (__eo_to_smt x))))) = SmtType.None
        rw [typeof_map_diff_eq, hx]
        rfl
      case set_is_empty =>
        change
          __smtx_typeof
            (SmtTerm.eq (__eo_to_smt x)
              (SmtTerm.set_empty
                (__eo_to_smt_set_elem_type
                  (__smtx_typeof (__eo_to_smt x))))) =
            SmtType.None
        rw [typeof_eq_eq, hx]
        rfl
      case set_is_singleton =>
        change
          __smtx_typeof
            (SmtTerm.eq (__eo_to_smt x)
              (SmtTerm.set_singleton
                (SmtTerm.map_diff (__eo_to_smt x)
                  (SmtTerm.set_empty
                    (__eo_to_smt_set_elem_type
                      (__smtx_typeof (__eo_to_smt x))))))) =
            SmtType.None
        rw [typeof_eq_eq, hx]
        rfl
      case _at_div_by_zero =>
        change
          __smtx_typeof
            (SmtTerm.qdiv (__eo_to_smt x)
              (SmtTerm.Rational (native_mk_rational 0 1))) =
            SmtType.None
        rw [typeof_qdiv_eq, hx]
        rfl
      case ubv_to_int =>
        change __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt x)) =
          SmtType.None
        rw [__smtx_typeof.eq_def] <;> simp only
        rw [hx]
        rfl
      case sbv_to_int =>
        change __smtx_typeof (SmtTerm.sbv_to_int (__eo_to_smt x)) =
          SmtType.None
        rw [__smtx_typeof.eq_def] <;> simp only
        rw [hx]
        rfl

private theorem uop1_apply_typeof_none_of_arg_none
    (op : UserOp1) (idx x : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)) =
      SmtType.None := by
  intro hx
  cases op
  case «repeat» =>
    change __smtx_typeof (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt x)) =
      SmtType.None
    rw [typeof_repeat_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case zero_extend =>
    change
      __smtx_typeof (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_zero_extend_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case sign_extend =>
    change
      __smtx_typeof (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_sign_extend_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case rotate_left =>
    change
      __smtx_typeof (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_rotate_left_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case rotate_right =>
    change
      __smtx_typeof (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_rotate_right_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case _at_bit =>
    change
      __smtx_typeof
        (SmtTerm.eq (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
          (__eo_to_smt x)) (SmtTerm.Binary 1 1)) = SmtType.None
    have hExt :
        __smtx_typeof
          (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
            (__eo_to_smt x)) = SmtType.None := by
      rw [typeof_extract_eq, hx]
      cases __eo_to_smt idx <;> rfl
    rw [typeof_eq_eq, hExt]
    rfl
  case re_exp =>
    change __smtx_typeof (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt x)) =
      SmtType.None
    rw [typeof_re_exp_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case is =>
    change
      __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx)) (__eo_to_smt x)) =
        SmtType.None
    exact smt_apply_type_none_of_arg_none
      (__eo_to_smt_tester (__eo_to_smt idx)) (__eo_to_smt x) hx
  case tuple_select =>
    change
      __smtx_typeof
        (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt x))
          (__eo_to_smt idx) (__eo_to_smt x)) = SmtType.None
    rw [hx]
    simp [__eo_to_smt_tuple_select]
  case int_to_bv =>
    change __smtx_typeof (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt x)) =
      SmtType.None
    rw [typeof_int_to_bv_eq, hx]
    cases __eo_to_smt idx <;> rfl
  all_goals
    exact eo_apply_generic_type_none_of_arg_none _ _ (by rfl) hx

private theorem uop2_apply_typeof_none_of_arg_none
    (op : UserOp2) (idx₁ idx₂ x : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp2 op idx₁ idx₂) x)) =
      SmtType.None := by
  intro hx
  cases op
  case extract =>
    change
      __smtx_typeof
        (SmtTerm.extract (__eo_to_smt idx₁) (__eo_to_smt idx₂)
          (__eo_to_smt x)) = SmtType.None
    rw [typeof_extract_eq, hx]
    cases __eo_to_smt idx₁ <;> cases __eo_to_smt idx₂ <;> rfl
  case re_loop =>
    change
      __smtx_typeof
        (SmtTerm.re_loop (__eo_to_smt idx₁) (__eo_to_smt idx₂)
          (__eo_to_smt x)) = SmtType.None
    rw [typeof_re_loop_eq, hx]
    cases __eo_to_smt idx₁ <;> cases __eo_to_smt idx₂ <;> rfl
  all_goals
    exact eo_apply_generic_type_none_of_arg_none _ _ (by rfl) hx

theorem eo_apply_arg_has_translation_of_has_translation_or_distinct
    (f x : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply f x) ->
    f = Term.UOp UserOp.distinct ∨
      RuleProofs.eo_has_smt_translation x := by
  intro hTrans
  cases f with
  | UOp op =>
      by_cases hDistinct : op = UserOp.distinct
      · left
        rw [hDistinct]
      · right
        unfold RuleProofs.eo_has_smt_translation at hTrans ⊢
        intro hx
        exact hTrans
          (uop_apply_typeof_none_of_arg_none op x hDistinct hx)
  | UOp1 op idx =>
      right
      unfold RuleProofs.eo_has_smt_translation at hTrans ⊢
      intro hx
      exact hTrans (uop1_apply_typeof_none_of_arg_none op idx x hx)
  | UOp2 op idx₁ idx₂ =>
      right
      unfold RuleProofs.eo_has_smt_translation at hTrans ⊢
      intro hx
      exact hTrans (uop2_apply_typeof_none_of_arg_none op idx₁ idx₂ x hx)
  | Apply g z =>
      right
      exact eo_apply_apply_arg_has_translation_of_has_translation g z x hTrans
  | _ =>
      right
      unfold RuleProofs.eo_has_smt_translation at hTrans ⊢
      intro hx
      exact hTrans
        (eo_apply_generic_type_none_of_arg_none _ _ (by rfl) hx)

theorem congTypeSpine_uop_apply_not_unary_eq_has_bool_type
    (op : UserOp) (x rhs : Term)
    (hUnary : uopHasUnarySmtTranslation op = false) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) x) ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp op) x) rhs) := by
  intro hTrans
  exact False.elim
    (no_translation_of_smt_type_none
      (t := Term.Apply (Term.UOp op) x)
      (uop_apply_typeof_none_of_not_unary_smt_translation op x hUnary)
      hTrans)

theorem congTrueSpine_uop_apply_not_unary_eq_true
    (M : SmtModel) (op : UserOp) (x rhs : Term)
    (hUnary : uopHasUnarySmtTranslation op = false) :
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply (Term.UOp op) x) rhs) ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp op) x) rhs) true := by
  intro hEqBool
  exact False.elim
    (no_bool_eq_left_of_smt_type_none
      (t := Term.Apply (Term.UOp op) x) (rhs := rhs)
      (uop_apply_typeof_none_of_not_unary_smt_translation op x hUnary)
      hEqBool)

private def __eo_to_smt_type_is_tlist : Term -> native_Bool
  | Term.Apply (Term.UOp UserOp._at__at_TypedList) _ => true
  | _ => false

private theorem eo_to_smt_type_is_tlist_true_eq
    {T : Term} :
    __eo_to_smt_type_is_tlist T = true ->
    ∃ U, T = Term.Apply (Term.UOp UserOp._at__at_TypedList) U := by
  intro hGuard
  cases T <;> try (change false = true at hGuard; cases hGuard)
  case Apply f U =>
    cases f <;> try (change false = true at hGuard; cases hGuard)
    case UOp op =>
      cases op <;> try (change false = true at hGuard; cases hGuard)
      case _at__at_TypedList =>
        exact ⟨U, rfl⟩

private theorem eo_to_smt_type_is_tlist_true_type_none
    {T : Term} :
    __eo_to_smt_type_is_tlist T = true ->
    __eo_to_smt_type T = SmtType.None := by
  intro hGuard
  rcases eo_to_smt_type_is_tlist_true_eq hGuard with ⟨U, hT⟩
  rw [hT]
  rfl

theorem no_bool_eq_arg_of_distinct_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) x) ->
    RuleProofs.eo_has_bool_type (mkEq x y) ->
    False := by
  intro hTrans hArg
  by_cases hGuard :
      native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None = true
  · apply hTrans
    change
      __smtx_typeof
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct x)) = SmtType.None
    simp [native_ite, hGuard]
  · have hxNN :
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None :=
      (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hArg).2
    have hElemNe : __eo_to_smt_typed_list_elem_type x ≠ SmtType.None := by
      intro hElem
      apply hGuard
      simp [native_Teq, hElem]
    rcases TranslationProofs.eo_to_smt_typed_list_elem_type_of_non_none
        x hElemNe with
      ⟨T, hXType, _hXSmt, _hTValid⟩
    have hMatch :
        __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
    have hTypeNone :
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp._at__at_TypedList) T) =
          SmtType.None :=
      eo_to_smt_type_is_tlist_true_type_none (T := Term.Apply (Term.UOp UserOp._at__at_TypedList) T)
        (by rfl)
    apply hxNN
    rw [hMatch, hXType, hTypeNone]


end CongSupport
