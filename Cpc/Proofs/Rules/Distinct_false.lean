module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def typedListElems : Term -> List Term
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs =>
      x :: typedListElems xs
  | Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) _ => []
  | _ => []

private noncomputable def typedListEvalElems (M : SmtModel) (xs : Term) : List SmtValue :=
  (typedListElems xs).map (fun x => __smtx_model_eval M (__eo_to_smt x))

private theorem smt_eval_and_eq_true
    {v₁ v₂ : SmtValue} :
    __smtx_model_eval_and v₁ v₂ = SmtValue.Boolean true ->
    v₁ = SmtValue.Boolean true ∧ v₂ = SmtValue.Boolean true := by
  intro h
  cases v₁ <;> cases v₂ <;> simp [__smtx_model_eval_and] at h
  case Boolean.Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [SmtEval.native_and] at h ⊢

private theorem smt_eval_not_eq_true
    {v : SmtValue} :
    __smtx_model_eval_not v = SmtValue.Boolean true ->
    v = SmtValue.Boolean false := by
  intro h
  cases v <;> simp [__smtx_model_eval_not] at h
  case Boolean b =>
    cases b <;> simp [SmtEval.native_not] at h ⊢

private theorem smt_eval_eq_false_implies_ne
    {v₁ v₂ : SmtValue} :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false ->
    v₁ ≠ v₂ := by
  intro hEq hSame
  subst v₂
  have hRefl : __smtx_model_eval_eq v₁ v₁ = SmtValue.Boolean true :=
    RuleProofs.smtx_model_eval_eq_refl v₁
  rw [hRefl] at hEq
  cases hEq

private theorem distinct_pairs_true_not_mem
    (M : SmtModel) (s : SmtTerm) :
    ∀ xs,
      __smtx_model_eval M (__eo_to_smt_distinct_pairs s xs) =
        SmtValue.Boolean true ->
      __smtx_model_eval M s ∉ typedListEvalElems M xs
  | Term.Apply f a, h => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [typedListEvalElems, typedListElems]
          | _ =>
              change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
              simp [__smtx_model_eval] at h
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  change
                    __smtx_model_eval M
                        (SmtTerm.and
                          (SmtTerm.not (SmtTerm.eq s (__eo_to_smt x)))
                          (__eo_to_smt_distinct_pairs s a)) =
                      SmtValue.Boolean true at h
                  rw [__smtx_model_eval.eq_9] at h
                  rcases smt_eval_and_eq_true h with ⟨hHead, hTail⟩
                  rw [__smtx_model_eval.eq_7, smtx_eval_eq_term_eq] at hHead
                  have hEqFalse :
                      __smtx_model_eval_eq
                          (__smtx_model_eval M s)
                          (__smtx_model_eval M (__eo_to_smt x)) =
                        SmtValue.Boolean false :=
                    smt_eval_not_eq_true hHead
                  have hNe :
                      __smtx_model_eval M s ≠
                        __smtx_model_eval M (__eo_to_smt x) :=
                    smt_eval_eq_false_implies_ne hEqFalse
                  have hNotTail :
                      __smtx_model_eval M s ∉ typedListEvalElems M a :=
                    distinct_pairs_true_not_mem M s a hTail
                  simp [typedListEvalElems, typedListElems, hNe]
                  intro y hy hEq
                  apply hNotTail
                  rw [typedListEvalElems]
                  have hyMap :
                      __smtx_model_eval M (__eo_to_smt y) ∈
                        (typedListElems a).map
                          (fun x => __smtx_model_eval M (__eo_to_smt x)) :=
                    List.mem_map_of_mem hy
                  rw [hEq] at hyMap
                  exact hyMap
              | _ =>
                  change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
                  simp [__smtx_model_eval] at h
          | _ =>
              change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
              simp [__smtx_model_eval] at h
      | _ =>
          change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
          simp [__smtx_model_eval] at h
  | Term.Stuck, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UOp _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UOp1 _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UOp2 _ _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UOp3 _ _ _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.__eo_List, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.__eo_List_nil, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.__eo_List_cons, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Bool, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Boolean _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Numeral _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Rational _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.String _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Binary _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Type, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.FunType, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Var _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DatatypeType _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DatatypeTypeRef _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DtcAppType _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DtCons _ _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DtSel _ _ _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.USort _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UConst _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h

private theorem distinct_true_nodup
    (M : SmtModel) :
    ∀ xs,
      __smtx_model_eval M (__eo_to_smt_distinct xs) =
        SmtValue.Boolean true ->
      (typedListEvalElems M xs).Nodup
  | Term.Apply f a, h => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [typedListEvalElems, typedListElems]
          | _ =>
              change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
              simp [__smtx_model_eval] at h
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  change
                    __smtx_model_eval M
                        (SmtTerm.and
                          (__eo_to_smt_distinct_pairs (__eo_to_smt x) a)
                          (__eo_to_smt_distinct a)) =
                      SmtValue.Boolean true at h
                  rw [__smtx_model_eval.eq_9] at h
                  rcases smt_eval_and_eq_true h with ⟨hPairs, hTail⟩
                  have hNotMem :
                      __smtx_model_eval M (__eo_to_smt x) ∉
                        typedListEvalElems M a :=
                    distinct_pairs_true_not_mem M (__eo_to_smt x) a hPairs
                  have hTailNodup : (typedListEvalElems M a).Nodup :=
                    distinct_true_nodup M a hTail
                  rw [typedListEvalElems, typedListElems]
                  exact (Iff.mpr List.nodup_cons ⟨hNotMem, hTailNodup⟩)
              | _ =>
                  change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
                  simp [__smtx_model_eval] at h
          | _ =>
              change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
              simp [__smtx_model_eval] at h
      | _ =>
          change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
          simp [__smtx_model_eval] at h
  | Term.Stuck, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UOp _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UOp1 _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UOp2 _ _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UOp3 _ _ _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.__eo_List, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.__eo_List_nil, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.__eo_List_cons, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Bool, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Boolean _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Numeral _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Rational _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.String _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Binary _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Type, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.FunType, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.Var _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DatatypeType _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DatatypeTypeRef _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DtcAppType _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DtCons _ _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.DtSel _ _ _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.USort _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h
  | Term.UConst _ _, h => by
      change __smtx_model_eval M SmtTerm.None = SmtValue.Boolean true at h
      simp [__smtx_model_eval] at h

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

private theorem typed_list_cons_is_list_true_get_nil_ne_stuck
    {a : Term} :
    __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) a =
      Term.Boolean true ->
    __eo_get_nil_rec (Term.UOp UserOp._at__at_TypedList_cons) a ≠
      Term.Stuck := by
  intro hList hStuck
  cases a <;> simp [__eo_is_list, __eo_is_ok, hStuck, native_teq,
    native_not, SmtEval.native_not] at hList

private theorem typed_list_is_list_true
    : ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) xs =
        Term.Boolean true
  | Term.Apply f a, hNN => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
              simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
                __eo_requires, __eo_is_list_nil,
                __eo_is_list_nil__at__at_TypedList_cons, native_teq,
                native_ite, native_not, SmtEval.native_not]
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hNN with
                    ⟨_hHeadTail, _hHeadNN, hTailNN, _hConsEq⟩
                  have hTailList := typed_list_is_list_true a hTailNN
                  have hTailGetNN :
                      __eo_get_nil_rec
                        (Term.UOp UserOp._at__at_TypedList_cons) a ≠
                        Term.Stuck :=
                    typed_list_cons_is_list_true_get_nil_ne_stuck hTailList
                  simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
                    __eo_requires, hTailGetNN, native_teq, native_ite,
                    native_not, SmtEval.native_not]
              | _ =>
                  simp [__eo_to_smt_typed_list_elem_type] at hNN
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | _ =>
          simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Stuck, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp1 _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp2 _ _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp3 _ _ _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List_nil, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List_cons, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Bool, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Boolean _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Numeral _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Rational _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.String _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Binary _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Type, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.FunType, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Var _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DatatypeType _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DatatypeTypeRef _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtcAppType _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtCons _ _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtSel _ _ _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.USort _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UConst _ _, hNN => by simp [__eo_to_smt_typed_list_elem_type] at hNN

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem term_ne_stuck_of_smt_type_non_none
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl] at hTy
  exact hTy TranslationProofs.smtx_typeof_none

private theorem nodup_of_map_nodup
    {α β : Type} (f : α -> β) :
    ∀ xs : List α, (xs.map f).Nodup -> xs.Nodup
  | [], _h => by simp
  | x :: xs, h => by
      rw [List.map_cons] at h
      rcases List.nodup_cons.mp h with ⟨hNotMem, hTail⟩
      rw [List.nodup_cons]
      exact ⟨(fun hx => hNotMem (List.mem_map_of_mem (f := f) hx)),
        nodup_of_map_nodup f xs hTail⟩

private theorem typed_list_erase_all_rec_eq_self_of_not_mem
    (x : Term) (hXNe : x ≠ Term.Stuck) :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      x ∉ typedListElems xs ->
      __eo_list_erase_all_rec xs x = xs
  | Term.Apply f a, hNN, hNotMem => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [__eo_list_erase_all_rec]
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts y a hNN with
                    ⟨_hHeadTail, hHeadNN, hTailNN, _hConsEq⟩
                  have hYNe : y ≠ Term.Stuck :=
                    term_ne_stuck_of_smt_type_non_none y hHeadNN
                  have hTailNe : a ≠ Term.Stuck := by
                    intro hA
                    subst a
                    simp [__eo_to_smt_typed_list_elem_type] at hTailNN
                  have hxy : x ≠ y := by
                    intro hEq
                    apply hNotMem
                    simp [typedListElems, hEq]
                  have hyx : y ≠ x := by
                    intro hEq
                    exact hxy hEq.symm
                  have hTailNotMem : x ∉ typedListElems a := by
                    intro hx
                    apply hNotMem
                    simp [typedListElems, hx]
                  have hTail :=
                    typed_list_erase_all_rec_eq_self_of_not_mem x hXNe
                      a hTailNN hTailNotMem
                  simp [__eo_list_erase_all_rec, __eo_eq,
                    __eo_not, __eo_prepend_if,
                    hyx, hTail, native_teq,
                    native_not, SmtEval.native_not]
              | _ =>
                  simp [__eo_to_smt_typed_list_elem_type] at hNN
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | _ =>
          simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Stuck, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp1 _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp2 _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp3 _ _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List_nil, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List_cons, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Bool, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Boolean _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Numeral _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Rational _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.String _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Binary _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Type, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.FunType, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Var _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DatatypeType _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DatatypeTypeRef _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtcAppType _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtCons _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtSel _ _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.USort _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UConst _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN

private theorem typed_list_setof_rec_eq_self_of_nodup :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      (typedListElems xs).Nodup ->
      __eo_list_setof_rec xs = xs
  | Term.Apply f a, hNN, hNodup => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [__eo_list_setof_rec]
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hNN with
                    ⟨_hHeadTail, hHeadNN, hTailNN, _hConsEq⟩
                  rcases List.nodup_cons.mp (by
                    simpa [typedListElems] using hNodup) with
                    ⟨hNotMem, hTailNodup⟩
                  have hXNe : x ≠ Term.Stuck :=
                    term_ne_stuck_of_smt_type_non_none x hHeadNN
                  have hTailNe : a ≠ Term.Stuck := by
                    intro hA
                    subst a
                    simp [__eo_to_smt_typed_list_elem_type] at hTailNN
                  have hSetTail :=
                    typed_list_setof_rec_eq_self_of_nodup a hTailNN
                      (by simpa [typedListElems] using hTailNodup)
                  have hErase :
                      __eo_list_erase_all_rec (__eo_list_setof_rec a) x = a := by
                    rw [hSetTail]
                    exact typed_list_erase_all_rec_eq_self_of_not_mem x hXNe
                      a hTailNN hNotMem
                  simp [__eo_list_setof_rec, __eo_mk_apply,
                    hErase]
              | _ =>
                  simp [__eo_to_smt_typed_list_elem_type] at hNN
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | _ =>
          simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Stuck, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp1 _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp2 _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp3 _ _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List_nil, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List_cons, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Bool, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Boolean _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Numeral _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Rational _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.String _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Binary _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Type, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.FunType, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Var _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DatatypeType _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DatatypeTypeRef _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtcAppType _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtCons _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtSel _ _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.USort _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UConst _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN

private theorem typed_list_setof_eq_self_of_nodup
    (xs : Term)
    (hNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None)
    (hNodup : (typedListElems xs).Nodup) :
    __eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) xs = xs := by
  have hList := typed_list_is_list_true xs hNN
  have hSetRec := typed_list_setof_rec_eq_self_of_nodup xs hNN hNodup
  rw [__eo_list_setof, hList, hSetRec]
  simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]

private theorem distinct_false_shape_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_distinct_false a1) = Term.Bool ->
  ∃ xs,
    a1 =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (Term.Boolean false) ∧
    __eo_eq (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) xs) xs =
      Term.Boolean false ∧
    __eo_eq (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) xs) xs ≠
      Term.Stuck := by
  intro hTy
  have hProg : __eo_prog_distinct_false a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f rhs =>
      cases rhs with
      | Boolean b =>
          cases b with
          | false =>
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
                                        __eo_eq
                                          (__eo_list_setof
                                            (Term.UOp UserOp._at__at_TypedList_cons) xs)
                                          xs
                                      have hReq :
                                          __eo_requires guard (Term.Boolean false)
                                            (Term.Apply
                                              (Term.Apply (Term.UOp UserOp.eq)
                                                (Term.Apply (Term.UOp UserOp.distinct) xs))
                                              (Term.Boolean false)) ≠
                                            Term.Stuck := by
                                        simpa [__eo_prog_distinct_false, guard] using hProg
                                      have hGuard : guard = Term.Boolean false :=
                                        eo_requires_arg_eq_of_ne_stuck hReq
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
          | true =>
              exfalso
              apply hProg
              cases f <;> simp [__eo_prog_distinct_false]
      | _ =>
          exfalso
          apply hProg
          cases f <;> simp [__eo_prog_distinct_false]
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_distinct_false_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_distinct_false a1) = Term.Bool ->
  __eo_prog_distinct_false a1 = a1 := by
  intro hTy
  rcases distinct_false_shape_of_typeof_bool a1 hTy with
    ⟨xs, rfl, hGuard, _hGuardNe⟩
  simp [__eo_prog_distinct_false, hGuard, __eo_requires, native_teq,
    native_ite, native_not, SmtEval.native_not]

private theorem typed___eo_prog_distinct_false_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_distinct_false a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_distinct_false a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_distinct_false a1 = a1 :=
    prog_distinct_false_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem distinct_false_sound
    (M : SmtModel) (hM : model_wf M) (xs : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (Term.Boolean false)) ->
  __eo_eq (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) xs) xs =
    Term.Boolean false ->
  eo_interprets M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (Term.Boolean false)) true := by
  intro hFormulaBool hGuard
  let distinctTerm := Term.Apply (Term.UOp UserOp.distinct) xs
  have hDistinctBool : RuleProofs.eo_has_bool_type distinctTerm := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        distinctTerm (Term.Boolean false) hFormulaBool with
      ⟨hTyEq, _hDistinctNN⟩
    unfold RuleProofs.eo_has_bool_type
    rw [hTyEq]
    change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
    rw [__smtx_typeof.eq_1]
  have hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        distinctTerm (Term.Boolean false) hFormulaBool with
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
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM distinctTerm
      hDistinctBool with
    ⟨bd, hDistinctEval⟩
  cases bd with
  | false =>
      apply RuleProofs.eo_interprets_eq_of_rel M distinctTerm (Term.Boolean false)
      · exact hFormulaBool
      · rw [hDistinctEval]
        rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by rfl,
          __smtx_model_eval.eq_1]
        exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)
  | true =>
      have hDistinctEvalTrue :
          __smtx_model_eval M (__eo_to_smt_distinct xs) =
            SmtValue.Boolean true := by
        simpa [distinctTerm, hDistinctSmt] using hDistinctEval
      have hEvalNodup :
          (typedListEvalElems M xs).Nodup :=
        distinct_true_nodup M xs hDistinctEvalTrue
      have hTermNodup : (typedListElems xs).Nodup := by
        simpa [typedListEvalElems] using
          nodup_of_map_nodup
            (fun x => __smtx_model_eval M (__eo_to_smt x))
            (typedListElems xs) hEvalNodup
      have hSetEq := typed_list_setof_eq_self_of_nodup xs hElemNN hTermNodup
      have hXsNe : xs ≠ Term.Stuck := by
        intro hXs
        subst xs
        simp [__eo_to_smt_typed_list_elem_type] at hElemNN
      have hGuardTrue :
          __eo_eq (__eo_list_setof (Term.UOp UserOp._at__at_TypedList_cons) xs) xs =
            Term.Boolean true := by
        rw [hSetEq]
        simp [__eo_eq, native_teq]
      rw [hGuard] at hGuardTrue
      cases hGuardTrue

private theorem facts___eo_prog_distinct_false_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_distinct_false a1) = Term.Bool ->
  eo_interprets M (__eo_prog_distinct_false a1) true := by
  intro hA1Trans hResultTy
  rcases distinct_false_shape_of_typeof_bool a1 hResultTy with
    ⟨xs, rfl, hGuard, _hGuardNe⟩
  have hProgEq :
      __eo_prog_distinct_false
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean false)) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean false) :=
    prog_distinct_false_eq_arg_of_typeof_bool
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (Term.Boolean false)) hResultTy
  have hFormulaTy :
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean false)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hFormulaBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean false)) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (Term.Boolean false))
      hA1Trans hFormulaTy
  rw [hProgEq]
  exact distinct_false_sound M hM xs hFormulaBool hGuard

public theorem cmd_step_distinct_false_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.distinct_false args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_false args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.distinct_false args premises ≠ Term.Stuck :=
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
              change __eo_typeof (__eo_prog_distinct_false A1) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_distinct_false A1) true
                exact facts___eo_prog_distinct_false_impl M hM A1
                  hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_distinct_false A1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_distinct_false A1)
                  (typed___eo_prog_distinct_false_impl A1 hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
