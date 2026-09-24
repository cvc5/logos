module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def qforall (x F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) F

private def qand (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def quantMiniscopeAndFormula (x F G : Term) : Term :=
  qeq (qforall x F) G

private theorem eo_to_smt_and_eq (A B : Term) :
    __eo_to_smt (qand A B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qforall x F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem smtx_typeof_not_arg_of_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_not_bool_of_arg_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_not_bool_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hNN
  have hArg : __smtx_typeof t = SmtType.Bool := by
    cases h : __smtx_typeof t <;>
      simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢
  exact smtx_typeof_not_bool_of_arg_bool t hArg

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  exact smtx_typeof_not_arg_of_bool t
    (smtx_typeof_not_bool_of_non_none t hNN)

private theorem smtx_typeof_and_args_of_bool
    (A B : SmtTerm) :
    __smtx_typeof (SmtTerm.and A B) = SmtType.Bool ->
    __smtx_typeof A = SmtType.Bool ∧
      __smtx_typeof B = SmtType.Bool := by
  intro hTy
  rw [typeof_and_eq] at hTy
  cases hA : __smtx_typeof A <;>
    cases hB : __smtx_typeof B <;>
    simp [hA, hB, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  intro hTy
  have hExists :
      __smtx_typeof
          (SmtTerm.exists s (__eo_to_smt_type T)
            (__eo_to_smt_exists xs body)) = SmtType.Bool := by
    simpa [__eo_to_smt_exists] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists xs body)) := by
    unfold term_has_non_none_type
    rw [hExists]
    simp
  exact exists_body_bool_of_non_none hNN

private theorem smtx_type_wf_of_exists_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠ SmtType.None := by
    intro hNone
    have hExists :
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs body)) = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    rw [smtx_typeof_exists_term_eq, hTail] at hExists
    simp [native_ite, native_Teq, hNone] at hExists
  exact smtx_typeof_guard_wf_wf_of_non_none
    (__eo_to_smt_type T) SmtType.Bool hGuardNN

private theorem smtx_typeof_eo_to_smt_exists_same_binders
    (xs : Term) (body body' : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body' = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body') = SmtType.Bool := by
  intro hTy hBody'
  cases hxs : xs
  case __eo_List_nil =>
      subst hxs
      simpa [__eo_to_smt_exists] using hBody'
  case Apply f a =>
      subst hxs
      cases f with
      | Apply g y =>
          cases g with
          | __eo_List_cons =>
              cases y with
              | Var name T =>
                  cases name with
                  | String s =>
                      have hTail :
                          __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                        smtx_typeof_exists_tail_bool_of_cons_bool s T a body hTy
                      have hTail' :
                          __smtx_typeof (__eo_to_smt_exists a body') = SmtType.Bool :=
                        smtx_typeof_eo_to_smt_exists_same_binders a body body'
                          hTail hBody'
                      have hWF :
                          __smtx_type_wf (__eo_to_smt_type T) = true :=
                        smtx_type_wf_of_exists_cons_bool s T a body hTy
                      change
                        __smtx_typeof
                          (SmtTerm.exists s (__eo_to_smt_type T)
                            (__eo_to_smt_exists a body')) = SmtType.Bool
                      rw [smtx_typeof_exists_term_eq, hTail']
                      simp [native_ite, native_Teq, __smtx_typeof_guard_wf, hWF]
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | _ =>
          simp [__eo_to_smt_exists] at hTy
  all_goals
      subst hxs
      simp [__eo_to_smt_exists] at hTy

private theorem false_of_smtx_typeof_none_bool :
    __smtx_typeof SmtTerm.None = SmtType.Bool -> False := by
  intro h
  exact TranslationProofs.smtx_typeof_none_ne_bool h

private theorem smtx_typeof_eo_to_smt_stuck_none :
    __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.None := by
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem smtx_typeof_eo_to_smt_true_bool :
    __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
  change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
  rw [__smtx_typeof.eq_1]

private theorem smtx_model_eval_eo_true
    (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
      SmtValue.Boolean true := by
  change __smtx_model_eval M (SmtTerm.Boolean true) =
    SmtValue.Boolean true
  rw [__smtx_model_eval.eq_1]

private theorem qforall_non_nil_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    x ≠ Term.__eo_List_nil := by
  intro hNN hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_bool_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    RuleProofs.eo_has_bool_type (qforall x F) := by
  intro hNN
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hNN
  unfold RuleProofs.eo_has_bool_type
  rw [eo_to_smt_forall_eq x F hx]
  exact smtx_typeof_not_bool_of_non_none
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) (by
      simpa [eo_to_smt_forall_eq x F hx] using hNN)

private theorem qforall_exists_type_bool_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
  intro hNN
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hNN
  exact smtx_typeof_not_arg_of_non_none
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) (by
      simpa [eo_to_smt_forall_eq x F hx] using hNN)

private theorem qforall_bool_of_exists_type_bool
    (x F : Term) :
    x ≠ Term.__eo_List_nil ->
    __smtx_typeof
        (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool ->
    RuleProofs.eo_has_bool_type (qforall x F) := by
  intro hx hExists
  unfold RuleProofs.eo_has_bool_type
  rw [eo_to_smt_forall_eq x F hx]
  exact smtx_typeof_not_bool_of_arg_bool
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) hExists

private theorem smtx_model_eval_exists_not_and_true_iff
    (M : SmtModel) (hM : model_wf M) :
    ∀ (xs : Term) (A B : SmtTerm),
    __smtx_typeof (__eo_to_smt_exists xs (SmtTerm.not A)) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs (SmtTerm.not B)) = SmtType.Bool ->
    (__smtx_model_eval M
        (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.and A B))) =
        SmtValue.Boolean true ↔
      __smtx_model_eval M (__eo_to_smt_exists xs (SmtTerm.not A)) =
          SmtValue.Boolean true ∨
        __smtx_model_eval M (__eo_to_smt_exists xs (SmtTerm.not B)) =
          SmtValue.Boolean true)
  | Term.__eo_List_nil, A, B => by
      intro hA hB
      have hANot : __smtx_typeof (SmtTerm.not A) = SmtType.Bool := by
        simpa [__eo_to_smt_exists] using hA
      have hBNot : __smtx_typeof (SmtTerm.not B) = SmtType.Bool := by
        simpa [__eo_to_smt_exists] using hB
      have hATy : __smtx_typeof A = SmtType.Bool :=
        smtx_typeof_not_arg_of_bool A hANot
      have hBTy : __smtx_typeof B = SmtType.Bool :=
        smtx_typeof_not_arg_of_bool B hBNot
      rcases smt_model_eval_bool_is_boolean M hM A hATy with ⟨a, ha⟩
      rcases smt_model_eval_bool_is_boolean M hM B hBTy with ⟨b, hb⟩
      cases a <;> cases b <;>
        simp [__eo_to_smt_exists, __smtx_model_eval, ha, hb,
          __smtx_model_eval_not, __smtx_model_eval_and, SmtEval.native_not,
          SmtEval.native_and]
  | Term.Apply f a, A, B => by
      intro hA hB
      cases f with
      | Apply g y =>
          cases g with
          | __eo_List_cons =>
              cases y with
              | Var name T =>
                  cases name with
                  | String s =>
                      have hTailA :
                          __smtx_typeof
                              (__eo_to_smt_exists a (SmtTerm.not A)) =
                            SmtType.Bool :=
                        smtx_typeof_exists_tail_bool_of_cons_bool s T a
                          (SmtTerm.not A) hA
                      have hTailB :
                          __smtx_typeof
                              (__eo_to_smt_exists a (SmtTerm.not B)) =
                            SmtType.Bool :=
                        smtx_typeof_exists_tail_bool_of_cons_bool s T a
                          (SmtTerm.not B) hB
                      have hWF :
                          __smtx_type_wf (__eo_to_smt_type T) = true :=
                        smtx_type_wf_of_exists_cons_bool s T a
                          (SmtTerm.not A) hA
                      classical
                      let P : Prop :=
                        ∃ v : SmtValue,
                          __smtx_typeof_value v = __eo_to_smt_type T ∧
                            __smtx_value_canonical v = true ∧
                            __smtx_model_eval
                                (native_model_push M s (__eo_to_smt_type T) v)
                                (__eo_to_smt_exists a
                                  (SmtTerm.not (SmtTerm.and A B))) =
                              SmtValue.Boolean true
                      let Q : Prop :=
                        ∃ v : SmtValue,
                          __smtx_typeof_value v = __eo_to_smt_type T ∧
                            __smtx_value_canonical v = true ∧
                            __smtx_model_eval
                                (native_model_push M s (__eo_to_smt_type T) v)
                                (__eo_to_smt_exists a (SmtTerm.not A)) =
                              SmtValue.Boolean true
                      let R : Prop :=
                        ∃ v : SmtValue,
                          __smtx_typeof_value v = __eo_to_smt_type T ∧
                            __smtx_value_canonical v = true ∧
                            __smtx_model_eval
                                (native_model_push M s (__eo_to_smt_type T) v)
                                (__eo_to_smt_exists a (SmtTerm.not B)) =
                              SmtValue.Boolean true
                      have hPQR : P ↔ Q ∨ R := by
                        constructor
                        · intro hSat
                          rcases hSat with ⟨v, hv, hCan, hEval⟩
                          have hPush :
                              model_wf
                                (native_model_push M s (__eo_to_smt_type T) v) :=
                            model_total_typed_push hM s (__eo_to_smt_type T) v hWF
                              hv (by
                                rw [value_canonical_bool_eq_true]
                                exact hCan)
                          have hRec :=
                            smtx_model_eval_exists_not_and_true_iff
                              (native_model_push M s (__eo_to_smt_type T) v)
                              hPush a A B hTailA hTailB
                          rcases hRec.1 hEval with hLeft | hRight
                          · exact Or.inl ⟨v, hv, hCan, hLeft⟩
                          · exact Or.inr ⟨v, hv, hCan, hRight⟩
                        · intro hSat
                          rcases hSat with hLeft | hRight
                          · rcases hLeft with ⟨v, hv, hCan, hEval⟩
                            refine ⟨v, hv, hCan, ?_⟩
                            have hPush :
                                model_wf
                                  (native_model_push M s (__eo_to_smt_type T) v) :=
                              model_total_typed_push hM s (__eo_to_smt_type T) v hWF
                                hv (by
                                  rw [value_canonical_bool_eq_true]
                                  exact hCan)
                            have hRec :=
                              smtx_model_eval_exists_not_and_true_iff
                                (native_model_push M s (__eo_to_smt_type T) v)
                                hPush a A B hTailA hTailB
                            exact hRec.2 (Or.inl hEval)
                          · rcases hRight with ⟨v, hv, hCan, hEval⟩
                            refine ⟨v, hv, hCan, ?_⟩
                            have hPush :
                                model_wf
                                  (native_model_push M s (__eo_to_smt_type T) v) :=
                              model_total_typed_push hM s (__eo_to_smt_type T) v hWF
                                hv (by
                                  rw [value_canonical_bool_eq_true]
                                  exact hCan)
                            have hRec :=
                              smtx_model_eval_exists_not_and_true_iff
                                (native_model_push M s (__eo_to_smt_type T) v)
                                hPush a A B hTailA hTailB
                            exact hRec.2 (Or.inr hEval)
                      have hQR : ((¬ Q) -> R) ↔ Q ∨ R := by
                        constructor
                        · intro h
                          by_cases hq : Q
                          · exact Or.inl hq
                          · exact Or.inr (h hq)
                        · intro h hq
                          rcases h with hq' | hr
                          · exact False.elim (hq hq')
                          · exact hr
                      simpa [P, Q, R, __eo_to_smt_exists, __smtx_model_eval,
                        hPQR] using hQR
                  | _ =>
                      exact False.elim (false_of_smtx_typeof_none_bool
                        (by simpa [__eo_to_smt_exists] using hA))
              | _ =>
                  exact False.elim (false_of_smtx_typeof_none_bool
                    (by simpa [__eo_to_smt_exists] using hA))
          | _ =>
              exact False.elim (false_of_smtx_typeof_none_bool
                (by simpa [__eo_to_smt_exists] using hA))
      | _ =>
          exact False.elim (false_of_smtx_typeof_none_bool
            (by simpa [__eo_to_smt_exists] using hA))
  | Term.UOp _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.UOp1 _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.UOp2 _ _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.UOp3 _ _ _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.__eo_List, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.__eo_List_cons, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.Bool, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.Boolean _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.Numeral _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.Rational _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.String _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.Binary _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.Type, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.Stuck, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.FunType, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.Var _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.DatatypeType _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.DatatypeTypeRef _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.DtcAppType _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.DtCons _ _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.DtSel _ _ _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.USort _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))
  | Term.UConst _ _, A, B => by
      intro hA _hB
      exact False.elim (false_of_smtx_typeof_none_bool
        (by simpa [__eo_to_smt_exists] using hA))

private theorem smtx_model_eval_forall_and
    (M : SmtModel) (hM : model_wf M)
    (xs : Term) (A B : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs (SmtTerm.not A)) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs (SmtTerm.not B)) = SmtType.Bool ->
    __smtx_model_eval M
        (SmtTerm.not
          (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.and A B)))) =
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not A)))
          (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not B)))) := by
  intro hA hB
  have hIff :=
    smtx_model_eval_exists_not_and_true_iff M hM xs A B hA hB
  have hANotTy : __smtx_typeof (SmtTerm.not A) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool xs
      (SmtTerm.not A) hA
  have hBNotTy : __smtx_typeof (SmtTerm.not B) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool xs
      (SmtTerm.not B) hB
  have hATy : __smtx_typeof A = SmtType.Bool :=
    smtx_typeof_not_arg_of_bool A hANotTy
  have hBTy : __smtx_typeof B = SmtType.Bool :=
    smtx_typeof_not_arg_of_bool B hBNotTy
  have hAndTy : __smtx_typeof (SmtTerm.and A B) = SmtType.Bool := by
    rw [typeof_and_eq]
    simp [hATy, hBTy, native_ite, native_Teq]
  have hNotAndTy :
      __smtx_typeof (SmtTerm.not (SmtTerm.and A B)) = SmtType.Bool :=
    smtx_typeof_not_bool_of_arg_bool (SmtTerm.and A B) hAndTy
  have hLeftTy :
      __smtx_typeof
          (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.and A B))) =
        SmtType.Bool :=
    smtx_typeof_eo_to_smt_exists_same_binders xs (SmtTerm.not A)
      (SmtTerm.not (SmtTerm.and A B)) hA hNotAndTy
  rcases smt_model_eval_bool_is_boolean M hM
      (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.and A B))) hLeftTy with
    ⟨bl, hLeftEval⟩
  rcases smt_model_eval_bool_is_boolean M hM
      (__eo_to_smt_exists xs (SmtTerm.not A)) hA with
    ⟨ba, hAEval⟩
  rcases smt_model_eval_bool_is_boolean M hM
      (__eo_to_smt_exists xs (SmtTerm.not B)) hB with
    ⟨bb, hBEval⟩
  cases bl <;> cases ba <;> cases bb <;>
    simp [__smtx_model_eval, hLeftEval, hAEval, hBEval,
      __smtx_model_eval_not, __smtx_model_eval_and, SmtEval.native_not,
      SmtEval.native_and] at hIff ⊢

private theorem smtx_model_eval_exists_not_true_true_iff
    (M : SmtModel) (xs : Term) :
    __smtx_model_eval M
        (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.Boolean true))) =
        SmtValue.Boolean true ↔ False := by
  cases hxs : xs
  case __eo_List_nil =>
      subst hxs
      simp [__eo_to_smt_exists, __smtx_model_eval,
        __smtx_model_eval_not, SmtEval.native_not]
  case Apply f a =>
      subst hxs
      cases hf : f
      case Apply g y =>
          subst hf
          cases hg : g
          case __eo_List_cons =>
              subst hg
              cases hy : y
              case Var name T =>
                  subst hy
                  cases hname : name
                  case String s =>
                      subst hname
                      classical
                      let P : Prop :=
                        ∃ v : SmtValue,
                          __smtx_typeof_value v = __eo_to_smt_type T ∧
                            __smtx_value_canonical v = true ∧
                            __smtx_model_eval
                                (native_model_push M s (__eo_to_smt_type T) v)
                                (__eo_to_smt_exists a
                                  (SmtTerm.not (SmtTerm.Boolean true))) =
                              SmtValue.Boolean true
                      have hPFalse : P ↔ False := by
                        constructor
                        · intro hSat
                          rcases hSat with ⟨v, _hv, _hCan, hEval⟩
                          exact
                            (smtx_model_eval_exists_not_true_true_iff
                              (native_model_push M s (__eo_to_smt_type T) v)
                              a).1 hEval
                        · intro hFalse
                          exact False.elim hFalse
                      have hPropEq : P = False := propext hPFalse
                      simp [P, __eo_to_smt_exists, __smtx_model_eval, hPropEq]
                  all_goals
                    subst hname
                    simp [__eo_to_smt_exists, __smtx_model_eval]
              all_goals
                subst hy
                simp [__eo_to_smt_exists, __smtx_model_eval]
          all_goals
            subst hg
            simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        subst hf
        simp [__eo_to_smt_exists, __smtx_model_eval]
  all_goals
    subst hxs
    simp [__eo_to_smt_exists, __smtx_model_eval]

private theorem smtx_model_eval_exists_not_true_false
    (M : SmtModel) (hM : model_wf M) (xs : Term) :
    __smtx_typeof
        (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.Boolean true))) =
      SmtType.Bool ->
    __smtx_model_eval M
        (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.Boolean true))) =
      SmtValue.Boolean false := by
  intro hTy
  rcases smt_model_eval_bool_is_boolean M hM
      (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.Boolean true))) hTy with
    ⟨b, hb⟩
  cases b
  · exact hb
  · exact False.elim
      ((smtx_model_eval_exists_not_true_true_iff M xs).1 hb)

private theorem smtx_model_eval_qforall_true
    (M : SmtModel) (hM : model_wf M) (x : Term) :
    RuleProofs.eo_has_bool_type (qforall x (Term.Boolean true)) ->
    __smtx_model_eval M (__eo_to_smt (qforall x (Term.Boolean true))) =
      SmtValue.Boolean true := by
  intro hBool
  have hNN :
      __smtx_typeof (__eo_to_smt (qforall x (Term.Boolean true))) ≠
        SmtType.None := by
    unfold RuleProofs.eo_has_bool_type at hBool
    rw [hBool]
    simp
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x (Term.Boolean true) hNN
  have hExistsTy :
      __smtx_typeof
          (__eo_to_smt_exists x
            (SmtTerm.not (__eo_to_smt (Term.Boolean true)))) =
        SmtType.Bool :=
    qforall_exists_type_bool_of_non_none x (Term.Boolean true) hNN
  have hExistsFalse :
      __smtx_model_eval M
          (__eo_to_smt_exists x (SmtTerm.not (SmtTerm.Boolean true))) =
        SmtValue.Boolean false :=
    smtx_model_eval_exists_not_true_false M hM x (by
      simpa using hExistsTy)
  rw [eo_to_smt_forall_eq x (Term.Boolean true) hx]
  simp [__smtx_model_eval, hExistsFalse, __smtx_model_eval_not,
    SmtEval.native_not]

private theorem qeq_rhs_non_none_of_has_bool_type
    (A B : Term) :
    RuleProofs.eo_has_bool_type (qeq A B) ->
    __smtx_typeof (__eo_to_smt B) ≠ SmtType.None := by
  intro hBool hNone
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      A B hBool with
    ⟨hSame, hLeftNN⟩
  apply hLeftNN
  rw [hSame, hNone]

private theorem mk_quant_miniscope_and_and_tail_ne_stuck
    (x f fs : Term) :
    x ≠ Term.Stuck ->
    __smtx_typeof
        (__eo_to_smt (__mk_quant_miniscope_and x (qand f fs))) ≠
      SmtType.None ->
    __mk_quant_miniscope_and x fs ≠ Term.Stuck := by
  intro hx hNN hTail
  apply hNN
  cases x <;>
    simp [qand, __mk_quant_miniscope_and, __eo_mk_apply,
      hTail] at hx ⊢
  all_goals
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem mk_quant_miniscope_and_and_eq
    (x f fs : Term) :
    x ≠ Term.Stuck ->
    __mk_quant_miniscope_and x fs ≠ Term.Stuck ->
    __mk_quant_miniscope_and x (qand f fs) =
      qand (qforall x f) (__mk_quant_miniscope_and x fs) := by
  intro hx hTail
  cases x <;>
    simp [qand, qforall, __mk_quant_miniscope_and, __eo_mk_apply] at hx ⊢

private theorem mk_quant_miniscope_and_invalid_type_none
    (x F : Term) :
    F ≠ Term.Boolean true ->
    (∀ f fs : Term, F ≠ qand f fs) ->
    __smtx_typeof (__eo_to_smt (__mk_quant_miniscope_and x F)) =
      SmtType.None := by
  intro hTrue hAnd
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__mk_quant_miniscope_and, smtx_typeof_eo_to_smt_stuck_none]
  · cases F with
    | Boolean b =>
        cases b
        · cases x <;>
            simp [__mk_quant_miniscope_and,
              smtx_typeof_eo_to_smt_stuck_none] at hx ⊢
        · exact False.elim (hTrue rfl)
    | Apply lhs fs =>
        cases lhs with
        | Apply op f =>
            cases op with
            | UOp u =>
                cases u with
                | and =>
                    exact False.elim (hAnd f fs rfl)
                | _ =>
                    cases x <;>
                      simp [__mk_quant_miniscope_and,
                        smtx_typeof_eo_to_smt_stuck_none] at hx ⊢
            | _ =>
                cases x <;>
                  simp [__mk_quant_miniscope_and,
                    smtx_typeof_eo_to_smt_stuck_none] at hx ⊢
        | _ =>
            cases x <;>
              simp [__mk_quant_miniscope_and,
                smtx_typeof_eo_to_smt_stuck_none] at hx ⊢
    | _ =>
        cases x <;>
          simp [__mk_quant_miniscope_and,
            smtx_typeof_eo_to_smt_stuck_none] at hx ⊢

private theorem smtx_model_eval_quant_miniscope_and_invalid
    (M : SmtModel) (hM : model_wf M) (x F : Term) :
    F ≠ Term.Boolean true ->
    (∀ f fs : Term, F ≠ qand f fs) ->
    RuleProofs.eo_has_bool_type
      (qeq (qforall x F) (__mk_quant_miniscope_and x F)) ->
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      __smtx_model_eval M (__eo_to_smt (__mk_quant_miniscope_and x F)) := by
  intro hTrue hAnd hBool
  have hRhsNN :=
    qeq_rhs_non_none_of_has_bool_type
      (qforall x F) (__mk_quant_miniscope_and x F) hBool
  exact False.elim
    (hRhsNN
      (mk_quant_miniscope_and_invalid_type_none x F hTrue hAnd))

private theorem smtx_model_eval_quant_miniscope_and_mk
    (M : SmtModel) (hM : model_wf M) (x : Term) :
    ∀ (F : Term),
    RuleProofs.eo_has_bool_type
      (qeq (qforall x F) (__mk_quant_miniscope_and x F)) ->
    __smtx_model_eval M (__eo_to_smt (qforall x F)) =
      __smtx_model_eval M (__eo_to_smt (__mk_quant_miniscope_and x F))
  | Term.Boolean true => by
      intro hBool
      by_cases hx : x = Term.Stuck
      · subst x
        have hRhsNN :=
          qeq_rhs_non_none_of_has_bool_type
            (qforall Term.Stuck (Term.Boolean true))
            (__mk_quant_miniscope_and Term.Stuck (Term.Boolean true))
            hBool
        exact False.elim (hRhsNN (by
          simp [__mk_quant_miniscope_and,
            smtx_typeof_eo_to_smt_stuck_none]))
      · have hMk :
            __mk_quant_miniscope_and x (Term.Boolean true) =
              Term.Boolean true := by
          cases x <;>
            simp [__mk_quant_miniscope_and] at hx ⊢
        have hBool' :
            RuleProofs.eo_has_bool_type
              (qeq (qforall x (Term.Boolean true)) (Term.Boolean true)) := by
          simpa [hMk] using hBool
        rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
            (qforall x (Term.Boolean true)) (Term.Boolean true) hBool' with
          ⟨hSame, _hLeftNN⟩
        have hForallBool :
            RuleProofs.eo_has_bool_type (qforall x (Term.Boolean true)) := by
          unfold RuleProofs.eo_has_bool_type
          rw [hSame]
          exact smtx_typeof_eo_to_smt_true_bool
        rw [hMk]
        rw [smtx_model_eval_eo_true M]
        exact smtx_model_eval_qforall_true M hM x hForallBool
  | Term.Apply lhs fs => by
      intro hBool
      cases lhs with
      | Apply op f =>
          cases op with
          | UOp u =>
              cases u with
              | and =>
                  by_cases hxStuck : x = Term.Stuck
                  · subst x
                    have hRhsNN :=
                      qeq_rhs_non_none_of_has_bool_type
                        (qforall Term.Stuck (qand f fs))
                        (__mk_quant_miniscope_and Term.Stuck (qand f fs))
                        (by simpa [qand] using hBool)
                    exact False.elim (hRhsNN (by
                      simp [__mk_quant_miniscope_and,
                        smtx_typeof_eo_to_smt_stuck_none]))
                  · have hRhsNN :=
                      qeq_rhs_non_none_of_has_bool_type
                        (qforall x (qand f fs))
                        (__mk_quant_miniscope_and x (qand f fs))
                        (by simpa [qand] using hBool)
                    have hTailNe :
                        __mk_quant_miniscope_and x fs ≠ Term.Stuck :=
                      mk_quant_miniscope_and_and_tail_ne_stuck
                        x f fs hxStuck hRhsNN
                    have hMk :
                        __mk_quant_miniscope_and x (qand f fs) =
                          qand (qforall x f)
                            (__mk_quant_miniscope_and x fs) :=
                      mk_quant_miniscope_and_and_eq x f fs
                        hxStuck hTailNe
                    have hBool' :
                        RuleProofs.eo_has_bool_type
                          (qeq (qforall x (qand f fs))
                            (qand (qforall x f)
                              (__mk_quant_miniscope_and x fs))) := by
                      have hBoolMk :
                          RuleProofs.eo_has_bool_type
                            (qeq (qforall x (qand f fs))
                              (__mk_quant_miniscope_and x (qand f fs))) := by
                        simpa [qand] using hBool
                      simpa [hMk] using hBoolMk
                    rcases
                        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                          (qforall x (qand f fs))
                          (qand (qforall x f)
                            (__mk_quant_miniscope_and x fs))
                          hBool' with
                      ⟨hSame, hLhsNN⟩
                    have hxNonNil : x ≠ Term.__eo_List_nil :=
                      qforall_non_nil_of_non_none x (qand f fs) hLhsNN
                    have hLhsBool :
                        RuleProofs.eo_has_bool_type
                          (qforall x (qand f fs)) :=
                      qforall_bool_of_non_none x (qand f fs) hLhsNN
                    have hRhsBool :
                        RuleProofs.eo_has_bool_type
                          (qand (qforall x f)
                            (__mk_quant_miniscope_and x fs)) := by
                      unfold RuleProofs.eo_has_bool_type at hLhsBool ⊢
                      rw [← hSame]
                      exact hLhsBool
                    have hQfBool :
                        RuleProofs.eo_has_bool_type (qforall x f) :=
                      RuleProofs.eo_has_bool_type_and_left
                        (qforall x f) (__mk_quant_miniscope_and x fs)
                        hRhsBool
                    have hTailBool :
                        RuleProofs.eo_has_bool_type
                          (__mk_quant_miniscope_and x fs) :=
                      RuleProofs.eo_has_bool_type_and_right
                        (qforall x f) (__mk_quant_miniscope_and x fs)
                        hRhsBool
                    have hExistsAnd :
                        __smtx_typeof
                            (__eo_to_smt_exists x
                              (SmtTerm.not
                                (SmtTerm.and (__eo_to_smt f)
                                  (__eo_to_smt fs)))) =
                          SmtType.Bool := by
                      simpa [qand] using
                        qforall_exists_type_bool_of_non_none
                          x (qand f fs) hLhsNN
                    have hNotAndBody :
                        __smtx_typeof
                            (SmtTerm.not
                              (SmtTerm.and (__eo_to_smt f)
                                (__eo_to_smt fs))) = SmtType.Bool :=
                      TranslationProofs.eo_to_smt_exists_body_bool_of_bool
                        x
                        (SmtTerm.not
                          (SmtTerm.and (__eo_to_smt f) (__eo_to_smt fs)))
                        hExistsAnd
                    have hAndTy :
                        __smtx_typeof
                            (SmtTerm.and (__eo_to_smt f)
                              (__eo_to_smt fs)) = SmtType.Bool :=
                      smtx_typeof_not_arg_of_bool
                        (SmtTerm.and (__eo_to_smt f) (__eo_to_smt fs))
                        hNotAndBody
                    rcases smtx_typeof_and_args_of_bool
                        (__eo_to_smt f) (__eo_to_smt fs) hAndTy with
                      ⟨hFTy, hFsTy⟩
                    have hNotFTy :
                        __smtx_typeof (SmtTerm.not (__eo_to_smt f)) =
                          SmtType.Bool :=
                      smtx_typeof_not_bool_of_arg_bool
                        (__eo_to_smt f) hFTy
                    have hNotFsTy :
                        __smtx_typeof (SmtTerm.not (__eo_to_smt fs)) =
                          SmtType.Bool :=
                      smtx_typeof_not_bool_of_arg_bool
                        (__eo_to_smt fs) hFsTy
                    have hExistsF :
                        __smtx_typeof
                            (__eo_to_smt_exists x
                              (SmtTerm.not (__eo_to_smt f))) =
                          SmtType.Bool :=
                      smtx_typeof_eo_to_smt_exists_same_binders x
                        (SmtTerm.not
                          (SmtTerm.and (__eo_to_smt f) (__eo_to_smt fs)))
                        (SmtTerm.not (__eo_to_smt f)) hExistsAnd hNotFTy
                    have hExistsFs :
                        __smtx_typeof
                            (__eo_to_smt_exists x
                              (SmtTerm.not (__eo_to_smt fs))) =
                          SmtType.Bool :=
                      smtx_typeof_eo_to_smt_exists_same_binders x
                        (SmtTerm.not
                          (SmtTerm.and (__eo_to_smt f) (__eo_to_smt fs)))
                        (SmtTerm.not (__eo_to_smt fs)) hExistsAnd hNotFsTy
                    have hQfsBool :
                        RuleProofs.eo_has_bool_type (qforall x fs) :=
                      qforall_bool_of_exists_type_bool x fs
                        hxNonNil hExistsFs
                    have hTailEqBool :
                        RuleProofs.eo_has_bool_type
                          (qeq (qforall x fs)
                            (__mk_quant_miniscope_and x fs)) := by
                      apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                      · unfold RuleProofs.eo_has_bool_type at hQfsBool hTailBool
                        rw [hQfsBool, hTailBool]
                      · unfold RuleProofs.eo_has_bool_type at hQfsBool
                        rw [hQfsBool]
                        simp
                    have hTailEval :=
                      smtx_model_eval_quant_miniscope_and_mk M hM
                        x fs hTailEqBool
                    have hForallAnd :=
                      smtx_model_eval_forall_and M hM x
                        (__eo_to_smt f) (__eo_to_smt fs)
                        hExistsF hExistsFs
                    have hLeft :
                        __smtx_model_eval M
                            (__eo_to_smt (qforall x (qand f fs))) =
                        __smtx_model_eval M
                            (SmtTerm.and
                              (SmtTerm.not
                                (__eo_to_smt_exists x
                                  (SmtTerm.not (__eo_to_smt f))))
                              (SmtTerm.not
                                (__eo_to_smt_exists x
                                  (SmtTerm.not (__eo_to_smt fs))))) := by
                      rw [eo_to_smt_forall_eq x (qand f fs) hxNonNil]
                      simpa [qand] using hForallAnd
                    have hRight :
                        __smtx_model_eval M
                            (__eo_to_smt
                              (qand (qforall x f)
                                (__mk_quant_miniscope_and x fs))) =
                          __smtx_model_eval M
                            (SmtTerm.and
                              (SmtTerm.not
                                (__eo_to_smt_exists x
                                  (SmtTerm.not (__eo_to_smt f))))
                              (SmtTerm.not
                                (__eo_to_smt_exists x
                                  (SmtTerm.not (__eo_to_smt fs))))) := by
                      rw [eo_to_smt_and_eq]
                      rw [eo_to_smt_forall_eq x f hxNonNil]
                      simp [__smtx_model_eval, hTailEval.symm,
                        eo_to_smt_forall_eq x fs hxNonNil]
                    have hEval :
                        __smtx_model_eval M
                            (__eo_to_smt (qforall x (qand f fs))) =
                        __smtx_model_eval M
                            (__eo_to_smt
                              (qand (qforall x f)
                                (__mk_quant_miniscope_and x fs))) :=
                      hLeft.trans hRight.symm
                    have hEvalMk :
                        __smtx_model_eval M
                            (__eo_to_smt (qforall x (qand f fs))) =
                          __smtx_model_eval M
                            (__eo_to_smt
                              (__mk_quant_miniscope_and x (qand f fs))) := by
                      rw [hMk]
                      exact hEval
                    simpa [qand] using hEvalMk
              | _ =>
                  have hRhsNN :=
                    qeq_rhs_non_none_of_has_bool_type _ _ hBool
                  exact False.elim (hRhsNN (by
                    cases x <;>
                      simp [__mk_quant_miniscope_and,
                        smtx_typeof_eo_to_smt_stuck_none]))
          | _ =>
              have hRhsNN :=
                qeq_rhs_non_none_of_has_bool_type _ _ hBool
              exact False.elim (hRhsNN (by
                cases x <;>
                  simp [__mk_quant_miniscope_and,
                    smtx_typeof_eo_to_smt_stuck_none]))
      | _ =>
          have hRhsNN :=
            qeq_rhs_non_none_of_has_bool_type _ _ hBool
          exact False.elim (hRhsNN (by
            cases x <;>
              simp [__mk_quant_miniscope_and,
                smtx_typeof_eo_to_smt_stuck_none]))
  | Term.Boolean false => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.Boolean false) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.UOp op => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.UOp op) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.UOp1 op a => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.UOp1 op a) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.UOp2 op a b => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.UOp2 op a b) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.UOp3 op a b c => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.UOp3 op a b c) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.__eo_List => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        Term.__eo_List (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.__eo_List_nil => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        Term.__eo_List_nil (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.__eo_List_cons => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        Term.__eo_List_cons (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.Bool => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        Term.Bool (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.Numeral n => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.Numeral n) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.Rational q => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.Rational q) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.String s => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.String s) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.Binary w n => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.Binary w n) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.Type => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        Term.Type (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.Stuck => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        Term.Stuck (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.FunType => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        Term.FunType (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.Var name T => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.Var name T) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.DatatypeType s d => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.DatatypeType s d) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.DatatypeTypeRef s => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.DatatypeTypeRef s) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.DtcAppType a b => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.DtcAppType a b) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.DtCons s d i => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.DtCons s d i) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.DtSel s d i j => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.DtSel s d i j) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.USort i => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.USort i) (by simp)
        (by intro f fs hEq; cases hEq) hBool
  | Term.UConst i T => by
      intro hBool
      exact smtx_model_eval_quant_miniscope_and_invalid M hM x
        (Term.UConst i T) (by simp)
        (by intro f fs hEq; cases hEq) hBool

private theorem eq_of_requires_same_not_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · exfalso
    apply hReq
    simp [__eo_requires, native_ite, native_teq, hxy]

private theorem requires_same_eq_body
    {x y B : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    __eo_requires x y B = B := by
  intro hxy hx
  subst y
  simp [__eo_requires, native_ite, native_teq, hx, native_not,
    SmtEval.native_not]

private theorem quant_miniscope_and_shape_of_not_stuck
    (a1 : Term) :
    __eo_prog_quant_miniscope_and a1 ≠ Term.Stuck ->
    ∃ x F G,
      a1 = quantMiniscopeAndFormula x F G ∧
      __eo_prog_quant_miniscope_and a1 =
        quantMiniscopeAndFormula x F G ∧
      __mk_quant_miniscope_and x F = G := by
  intro hProg
  cases a1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply forallHead F =>
                      cases forallHead with
                      | Apply forallOp x =>
                          cases forallOp with
                          | UOp opForall =>
                              cases opForall with
                              | «forall» =>
                                  have hReq :
                                      __eo_requires
                                          (__mk_quant_miniscope_and x F) G
                                          (quantMiniscopeAndFormula x F G) ≠
                                        Term.Stuck := by
                                    simpa [quantMiniscopeAndFormula, qeq,
                                      qforall,
                                      __eo_prog_quant_miniscope_and] using hProg
                                  have hMkEq :
                                      __mk_quant_miniscope_and x F = G :=
                                    eq_of_requires_same_not_stuck hReq
                                  have hMkNe :
                                      __mk_quant_miniscope_and x F ≠
                                        Term.Stuck := by
                                    intro hStuck
                                    have hG : G = Term.Stuck := by
                                      rw [← hMkEq, hStuck]
                                    subst G
                                    simp [hStuck, __eo_requires, native_ite,
                                      native_teq, native_not,
                                      SmtEval.native_not] at hReq
                                  refine ⟨x, F, G, rfl, ?_, hMkEq⟩
                                  change __eo_prog_quant_miniscope_and
                                      (quantMiniscopeAndFormula x F G) =
                                    quantMiniscopeAndFormula x F G
                                  simpa [quantMiniscopeAndFormula, qeq,
                                    qforall,
                                    __eo_prog_quant_miniscope_and,
                                    requires_same_eq_body hMkEq hMkNe]
                              | _ =>
                                  simp [__eo_prog_quant_miniscope_and] at hProg
                          | _ =>
                              simp [__eo_prog_quant_miniscope_and] at hProg
                      | _ =>
                          simp [__eo_prog_quant_miniscope_and] at hProg
                  | _ =>
                      simp [__eo_prog_quant_miniscope_and] at hProg
              | _ =>
                  simp [__eo_prog_quant_miniscope_and] at hProg
          | _ =>
              simp [__eo_prog_quant_miniscope_and] at hProg
      | _ =>
          simp [__eo_prog_quant_miniscope_and] at hProg
  | _ =>
      simp [__eo_prog_quant_miniscope_and] at hProg

public theorem cmd_step_quant_miniscope_and_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_miniscope_and args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_miniscope_and args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_miniscope_and args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_miniscope_and args premises ≠
        Term.Stuck :=
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
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using
                  hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_miniscope_and a1 ≠ Term.Stuck := by
                change __eo_prog_quant_miniscope_and a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_miniscope_and_shape_of_not_stuck a1 hProgQuant with
                ⟨x, F, G, ha1, hProgEq, hMkEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (quantMiniscopeAndFormula x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quantMiniscopeAndFormula x F G) =
                    Term.Bool := by
                change __eo_typeof (__eo_prog_quant_miniscope_and a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (quantMiniscopeAndFormula x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quantMiniscopeAndFormula x F G)
                  hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_miniscope_and a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (qforall x F) G
                · exact hFormulaBool
                · have hMkBool :
                      RuleProofs.eo_has_bool_type
                        (qeq (qforall x F)
                          (__mk_quant_miniscope_and x F)) := by
                    simpa [quantMiniscopeAndFormula, qeq, hMkEq] using
                      hFormulaBool
                  have hEvalEq :=
                    smtx_model_eval_quant_miniscope_and_mk M hM x F
                      hMkBool
                  rw [hMkEq] at hEvalEq
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt G))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_miniscope_and a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
