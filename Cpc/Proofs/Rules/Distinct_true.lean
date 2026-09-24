module

public import Cpc.Proofs.RuleSupport.DistinctTermsSupport
import all Cpc.Proofs.RuleSupport.DistinctTermsSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_ite_then_false_eq_true {c t : Term} :
    __eo_ite c t (Term.Boolean false) = Term.Boolean true ->
    c = Term.Boolean true ∧ t = Term.Boolean true := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢
    exact h

private theorem typed_list_cons_type_parts
    (x xs : Term)
    (hNN :
      __eo_to_smt_typed_list_elem_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) = __eo_to_smt_typed_list_elem_type xs ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ∧
      __eo_to_smt_typed_list_elem_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) =
        __smtx_typeof (__eo_to_smt x) := by
  let headTy := __smtx_typeof (__eo_to_smt x)
  let tailTy := __eo_to_smt_typed_list_elem_type xs
  have hEqBool : native_Teq headTy tailTy = true := by
    cases hEq : native_Teq headTy tailTy <;>
      simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy, native_ite, hEq]
        at hNN ⊢
  have hHeadTail : headTy = tailTy := by
    simpa [native_Teq] using hEqBool
  have hHeadNN : headTy ≠ SmtType.None := by
    intro hHeadNone
    apply hNN
    simp [__eo_to_smt_typed_list_elem_type, headTy, native_ite, hHeadNone]
  have hTailNN : tailTy ≠ SmtType.None := by
    rw [← hHeadTail]
    exact hHeadNN
  have hConsEq :
      __eo_to_smt_typed_list_elem_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) =
        headTy := by
    simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy, native_ite,
      hEqBool]
  exact ⟨hHeadTail, hHeadNN, hTailNN, hConsEq⟩

private theorem are_distinct_terms_list_rec_cons_true
    {t x xs T : Term}
    (ht : t ≠ Term.Stuck) :
    __are_distinct_terms_list_rec t
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) T =
      Term.Boolean true ->
    __eo_ite
        (__eo_ite (__eo_eq t x) (Term.Boolean false)
          (__are_distinct_terms_type t x T))
        (__are_distinct_terms_list_rec t xs T)
        (Term.Boolean false) =
      Term.Boolean true := by
  intro h
  cases t <;> try exact False.elim (ht rfl)
  all_goals
    cases T <;>
      simp [__are_distinct_terms_list_rec] at h ⊢
  all_goals exact h

private theorem are_distinct_terms_list_cons_true
    {x xs T : Term} :
    __are_distinct_terms_list
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) T =
      Term.Boolean true ->
    __eo_ite (__are_distinct_terms_list_rec x xs T)
        (__are_distinct_terms_list xs T)
        (Term.Boolean false) =
      Term.Boolean true := by
  intro h
  cases T <;>
    simp [__are_distinct_terms_list.eq_def,
      __eo_l_1___are_distinct_terms_list] at h ⊢
  all_goals exact h

private theorem distinct_pairs_eval_true_of_guard_rec
    (M : SmtModel) (hM : model_wf M) (t T : Term)
    (htTrans : RuleProofs.eo_has_smt_translation t) :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __are_distinct_terms_list_rec t xs T = Term.Boolean true ->
      __smtx_model_eval M (__eo_to_smt_distinct_pairs (__eo_to_smt t) xs) =
        SmtValue.Boolean true
  | Term.Apply f a, hElemNN, hGuard => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              change __smtx_model_eval M (SmtTerm.Boolean true) =
                SmtValue.Boolean true
              rw [__smtx_model_eval.eq_1]
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hElemNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hElemNN with
                    ⟨_hHeadTail, hHeadNN, hTailNN, _hConsEq⟩
                  have hxTrans : RuleProofs.eo_has_smt_translation x := by
                    simpa [RuleProofs.eo_has_smt_translation] using hHeadNN
                  have htNe : t ≠ Term.Stuck := by
                    intro ht
                    subst t
                    exact htTrans (by
                      change __smtx_typeof SmtTerm.None = SmtType.None
                      exact TranslationProofs.smtx_typeof_none)
                  have hOuter :
                      __eo_ite
                          (__eo_ite (__eo_eq t x) (Term.Boolean false)
                            (__are_distinct_terms_type t x T))
                          (__are_distinct_terms_list_rec t a T)
                          (Term.Boolean false) =
                        Term.Boolean true :=
                    are_distinct_terms_list_rec_cons_true htNe hGuard
                  rcases eo_ite_then_false_eq_true hOuter with
                    ⟨hHeadGuard, hTailGuard⟩
                  rcases eo_ite_eq_false_guard_true hHeadGuard with
                    ⟨hEqFalse, hDistinct⟩
                  have hEvalEqFalse :
                      __smtx_model_eval_eq
                          (__smtx_model_eval M (__eo_to_smt t))
                          (__smtx_model_eval M (__eo_to_smt x)) =
                        SmtValue.Boolean false :=
                    are_distinct_terms_type_model_eval_eq_false_of_any_type
                      M hM T t x htTrans hxTrans hEqFalse hDistinct
                  have hHeadEval :
                      __smtx_model_eval M
                          (SmtTerm.not
                            (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt x))) =
                        SmtValue.Boolean true := by
                    rw [__smtx_model_eval.eq_7, smtx_eval_eq_term_eq,
                      hEvalEqFalse]
                    simp [__smtx_model_eval_not, SmtEval.native_not]
                  have hTailEval :
                      __smtx_model_eval M
                          (__eo_to_smt_distinct_pairs (__eo_to_smt t) a) =
                        SmtValue.Boolean true :=
                    distinct_pairs_eval_true_of_guard_rec M hM t T
                      htTrans a hTailNN hTailGuard
                  change
                    __smtx_model_eval M
                        (SmtTerm.and
                          (SmtTerm.not
                            (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt x)))
                          (__eo_to_smt_distinct_pairs (__eo_to_smt t) a)) =
                      SmtValue.Boolean true
                  rw [__smtx_model_eval.eq_9, hHeadEval, hTailEval]
                  simp [__smtx_model_eval_and, SmtEval.native_and]
              | _ =>
                  simp [__eo_to_smt_typed_list_elem_type] at hElemNN
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hElemNN
      | _ =>
          simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Stuck, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UOp _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UOp1 _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UOp2 _ _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UOp3 _ _ _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.__eo_List, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.__eo_List_nil, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.__eo_List_cons, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Bool, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Boolean _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Numeral _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Rational _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.String _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Binary _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Type, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.FunType, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Var _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DatatypeType _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DatatypeTypeRef _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DtcAppType _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DtCons _ _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DtSel _ _ _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.USort _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UConst _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN

private theorem distinct_eval_true_of_guard_list
    (M : SmtModel) (hM : model_wf M) (T : Term) :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __are_distinct_terms_list xs T = Term.Boolean true ->
      __smtx_model_eval M (__eo_to_smt_distinct xs) =
        SmtValue.Boolean true
  | Term.Apply f a, hElemNN, hGuard => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              change __smtx_model_eval M (SmtTerm.Boolean true) =
                SmtValue.Boolean true
              rw [__smtx_model_eval.eq_1]
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hElemNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hElemNN with
                    ⟨_hHeadTail, hHeadNN, hTailNN, _hConsEq⟩
                  have hxTrans : RuleProofs.eo_has_smt_translation x := by
                    simpa [RuleProofs.eo_has_smt_translation] using hHeadNN
                  have hOuter :
                      __eo_ite (__are_distinct_terms_list_rec x a T)
                          (__are_distinct_terms_list a T)
                          (Term.Boolean false) =
                        Term.Boolean true :=
                    are_distinct_terms_list_cons_true hGuard
                  rcases eo_ite_then_false_eq_true hOuter with
                    ⟨hPairsGuard, hTailGuard⟩
                  have hPairsEval :
                      __smtx_model_eval M
                          (__eo_to_smt_distinct_pairs (__eo_to_smt x) a) =
                        SmtValue.Boolean true :=
                    distinct_pairs_eval_true_of_guard_rec M hM x T
                      hxTrans a hTailNN hPairsGuard
                  have hTailEval :
                      __smtx_model_eval M (__eo_to_smt_distinct a) =
                        SmtValue.Boolean true :=
                    distinct_eval_true_of_guard_list M hM T
                      a hTailNN hTailGuard
                  change
                    __smtx_model_eval M
                        (SmtTerm.and
                          (__eo_to_smt_distinct_pairs (__eo_to_smt x) a)
                          (__eo_to_smt_distinct a)) =
                      SmtValue.Boolean true
                  rw [__smtx_model_eval.eq_9, hPairsEval, hTailEval]
                  simp [__smtx_model_eval_and, SmtEval.native_and]
              | _ =>
                  simp [__eo_to_smt_typed_list_elem_type] at hElemNN
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hElemNN
      | _ =>
          simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Stuck, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UOp _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UOp1 _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UOp2 _ _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UOp3 _ _ _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.__eo_List, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.__eo_List_nil, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.__eo_List_cons, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Bool, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Boolean _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Numeral _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Rational _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.String _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Binary _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Type, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.FunType, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.Var _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DatatypeType _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DatatypeTypeRef _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DtcAppType _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DtCons _ _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.DtSel _ _ _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.USort _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | Term.UConst _ _, hElemNN, _ => by
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN

private theorem distinct_true_shape_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_distinct_true a1) = Term.Bool ->
  ∃ xs,
    a1 =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (Term.Boolean true) ∧
    __are_distinct_terms_list xs
        (__typed_list_element_type (__eo_typeof xs)) =
      Term.Boolean true ∧
    __are_distinct_terms_list xs
        (__typed_list_element_type (__eo_typeof xs)) ≠
      Term.Stuck := by
  intro hTy
  have hProg : __eo_prog_distinct_true a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f rhs =>
      cases rhs with
      | Boolean b =>
          cases b with
          | true =>
              cases f with
              | Apply g lhs =>
                  cases g with
                  | UOp op =>
                      cases op with
                      | eq =>
                          cases lhs with
                          | Apply d xs =>
                              cases d with
                              | UOp op =>
                                  cases op with
                                  | distinct =>
                                      let guard :=
                                        __are_distinct_terms_list xs
                                          (__typed_list_element_type
                                            (__eo_typeof xs))
                                      have hReq :
                                          __eo_requires guard
                                            (Term.Boolean true)
                                            (Term.Apply
                                              (Term.Apply (Term.UOp UserOp.eq)
                                                (Term.Apply (Term.UOp UserOp.distinct) xs))
                                              (Term.Boolean true)) ≠
                                            Term.Stuck := by
                                        simpa [__eo_prog_distinct_true, guard]
                                          using hProg
                                      have hGuard : guard = Term.Boolean true :=
                                        _root_.eo_requires_arg_eq_of_ne_stuck hReq
                                      refine ⟨xs, rfl, ?_, ?_⟩
                                      · simpa [guard] using hGuard
                                      · intro hStuck
                                        have : guard = Term.Stuck := by
                                          simpa [guard] using hStuck
                                        rw [hGuard] at this
                                        cases this
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | false =>
              exfalso
              apply hProg
              cases f <;> simp [__eo_prog_distinct_true]
      | _ =>
          exfalso
          apply hProg
          cases f <;> simp [__eo_prog_distinct_true]
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_distinct_true_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_distinct_true a1) = Term.Bool ->
  __eo_prog_distinct_true a1 = a1 := by
  intro hTy
  rcases distinct_true_shape_of_typeof_bool a1 hTy with
    ⟨xs, rfl, hGuard, _hGuardNe⟩
  simp [__eo_prog_distinct_true, hGuard, __eo_requires, native_teq,
    native_ite, native_not, SmtEval.native_not]

private theorem typed___eo_prog_distinct_true_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_distinct_true a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_distinct_true a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_distinct_true a1 = a1 :=
    prog_distinct_true_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem distinct_true_sound
    (M : SmtModel) (hM : model_wf M) (xs : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (Term.Boolean true)) ->
  __are_distinct_terms_list xs
      (__typed_list_element_type (__eo_typeof xs)) =
    Term.Boolean true ->
  eo_interprets M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (Term.Boolean true)) true := by
  intro hFormulaBool hGuard
  let distinctTerm := Term.Apply (Term.UOp UserOp.distinct) xs
  have hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        distinctTerm (Term.Boolean true) hFormulaBool with
      ⟨_hTyEq, hDistinctNN⟩
    intro hNone
    have hDistinctNone :
        __smtx_typeof (__eo_to_smt distinctTerm) = SmtType.None := by
      change __smtx_typeof
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct xs)) = SmtType.None
      simp [hNone, native_Teq, native_ite]
    exact hDistinctNN hDistinctNone
  have hDistinctSmt :
      __eo_to_smt distinctTerm = __eo_to_smt_distinct xs := by
    change native_ite
      (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) = __eo_to_smt_distinct xs
    simp [native_Teq, native_ite, hElemNN]
  have hDistinctEval :
      __smtx_model_eval M (__eo_to_smt_distinct xs) =
        SmtValue.Boolean true :=
    distinct_eval_true_of_guard_list M hM
      (__typed_list_element_type (__eo_typeof xs)) xs hElemNN hGuard
  apply RuleProofs.eo_interprets_eq_of_rel M distinctTerm (Term.Boolean true)
  · exact hFormulaBool
  · rw [hDistinctSmt, hDistinctEval]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl,
      __smtx_model_eval.eq_1]
    change RuleProofs.smt_value_rel (SmtValue.Boolean true)
      (SmtValue.Boolean true)
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean true)

private theorem facts___eo_prog_distinct_true_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_distinct_true a1) = Term.Bool ->
  eo_interprets M (__eo_prog_distinct_true a1) true := by
  intro hA1Trans hResultTy
  rcases distinct_true_shape_of_typeof_bool a1 hResultTy with
    ⟨xs, rfl, hGuard, _hGuardNe⟩
  have hProgEq :
      __eo_prog_distinct_true
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean true)) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean true) :=
    prog_distinct_true_eq_arg_of_typeof_bool
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (Term.Boolean true)) hResultTy
  have hFormulaTy :
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hFormulaBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean true)) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (Term.Boolean true))
      hA1Trans hFormulaTy
  rw [hProgEq]
  exact distinct_true_sound M hM xs hFormulaBool hGuard

public theorem cmd_step_distinct_true_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.distinct_true args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_true args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.distinct_true args premises ≠ Term.Stuck :=
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
              let A1 := a1
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons A1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation A1 := by
                simpa [A1, cArgListTranslationOk, RuleProofs.eo_has_smt_translation,
                  eoHasSmtTranslation] using hArgsTrans.1
              change __eo_typeof (__eo_prog_distinct_true A1) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_distinct_true A1) true
                exact facts___eo_prog_distinct_true_impl M hM A1
                  hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_distinct_true A1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_distinct_true A1)
                  (typed___eo_prog_distinct_true_impl A1 hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
