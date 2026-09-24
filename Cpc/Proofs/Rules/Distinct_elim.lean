module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem smt_eval_and_assoc_bool
    {a b c : Bool} :
    __smtx_model_eval_and (SmtValue.Boolean a)
      (__smtx_model_eval_and (SmtValue.Boolean b) (SmtValue.Boolean c)) =
    __smtx_model_eval_and
      (__smtx_model_eval_and (SmtValue.Boolean a) (SmtValue.Boolean b))
      (SmtValue.Boolean c) := by
  cases a <;> cases b <;> cases c <;>
    simp [__smtx_model_eval_and, SmtEval.native_and]

private theorem smt_eval_and_true_right_eq_of_boolean
    {v : SmtValue} {b : Bool} :
    __smtx_model_eval_and v (SmtValue.Boolean true) = SmtValue.Boolean b ->
    v = __smtx_model_eval_and v (SmtValue.Boolean true) := by
  intro h
  cases v <;> simp [__smtx_model_eval_and] at h ⊢
  case Boolean bv =>
    cases bv <;> simp [SmtEval.native_and] at h ⊢

private theorem smt_eval_eq_bool
    (v₁ v₂ : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean b := by
  cases v₁ <;> cases v₂ <;> simp [__smtx_model_eval_eq, native_veq]

private theorem smt_eval_not_eq_bool
    (M : SmtModel) (s t : SmtTerm) :
    ∃ b : Bool,
      __smtx_model_eval M
        (SmtTerm.not (SmtTerm.eq s t)) =
        SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_7, smtx_eval_eq_term_eq]
  rcases smt_eval_eq_bool (__smtx_model_eval M s) (__smtx_model_eval M t) with
    ⟨b, hEq⟩
  rw [hEq]
  cases b <;> simp [__smtx_model_eval_not, SmtEval.native_not]

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

private theorem eo_requires_result_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro hReq
  have hxy : x = y := eo_requires_arg_eq_of_ne_stuck hReq
  subst y
  have hx : x ≠ Term.Stuck := by
    intro hx
    subst x
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]
      at hReq
  cases x <;> simp [__eo_requires, native_teq, native_ite, native_not,
    SmtEval.native_not] at hx ⊢

private theorem term_ne_stuck_of_eval_boolean
    (M : SmtModel) (t : Term) :
    (∃ b : Bool, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b) ->
    t ≠ Term.Stuck := by
  intro hBool hStuck
  subst t
  rcases hBool with ⟨b, hBool⟩
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl] at hBool
  simp [__smtx_model_eval] at hBool

private theorem term_ne_stuck_of_smt_type_non_none
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl] at hTy
  simp at hTy

private theorem list_singleton_elim_stuck
    (f : Term) :
    __eo_list_singleton_elim f Term.Stuck = Term.Stuck := by
  cases f <;> rfl

private theorem distinct_pairs_eval_bool
    (M : SmtModel) (s : SmtTerm) :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      ∃ b : Bool,
        __smtx_model_eval M (__eo_to_smt_distinct_pairs s xs) =
          SmtValue.Boolean b
  | Term.Apply f a, hNN => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              exact ⟨true, by simp [__eo_to_smt_distinct_pairs, __smtx_model_eval]⟩
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hNN with
                    ⟨_hHeadTail, _hHeadNN, hTailNN, _hConsEq⟩
                  rcases distinct_pairs_eval_bool M s a hTailNN with
                    ⟨bt, hTail⟩
                  rw [__eo_to_smt_distinct_pairs, __smtx_model_eval.eq_9]
                  rcases smt_eval_not_eq_bool M s (__eo_to_smt x) with
                    ⟨bh, hHead⟩
                  rw [hHead, hTail]
                  exact ⟨native_and bh bt, by simp [__smtx_model_eval_and]⟩
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

private theorem distinct_eval_bool
    (M : SmtModel) :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      ∃ b : Bool,
        __smtx_model_eval M (__eo_to_smt_distinct xs) =
          SmtValue.Boolean b
  | Term.Apply f a, hNN => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              exact ⟨true, by simp [__eo_to_smt_distinct, __smtx_model_eval]⟩
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hNN with
                    ⟨_hHeadTail, _hHeadNN, hTailNN, _hConsEq⟩
                  rcases distinct_pairs_eval_bool M (__eo_to_smt x) a hTailNN with
                    ⟨bp, hPairs⟩
                  rcases distinct_eval_bool M a hTailNN with ⟨bt, hTail⟩
                  rw [__eo_to_smt_distinct, __smtx_model_eval.eq_9, hPairs, hTail]
                  exact ⟨native_and bp bt, by simp [__smtx_model_eval_and]⟩
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

private theorem mk_distinct_elim_rec_eval
    (M : SmtModel) (x b : Term) :
    x ≠ Term.Stuck ->
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      (∃ bb : Bool, __smtx_model_eval M (__eo_to_smt b) =
        SmtValue.Boolean bb) ->
      __smtx_model_eval M (__eo_to_smt (__mk_distinct_elim_rec x xs b)) =
        __smtx_model_eval M
          (SmtTerm.and (__eo_to_smt_distinct_pairs (__eo_to_smt x) xs)
            (__eo_to_smt b))
  | hXNe, Term.Apply f a, hNN, hB => by
      rcases hB with ⟨bb, hB⟩
      have hBEx :
          ∃ bb : Bool, __smtx_model_eval M (__eo_to_smt b) =
            SmtValue.Boolean bb := ⟨bb, hB⟩
      have hBNe : b ≠ Term.Stuck :=
        term_ne_stuck_of_eval_boolean M b hBEx
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [__mk_distinct_elim_rec, __eo_to_smt_distinct_pairs,
                __smtx_model_eval.eq_9, __smtx_model_eval.eq_1,
                hB, __smtx_model_eval_and]
              cases bb <;> simp [SmtEval.native_and]
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts y a hNN with
                    ⟨_hHeadTail, _hHeadNN, hTailNN, _hConsEq⟩
                  have hIH :=
                    mk_distinct_elim_rec_eval M x b hXNe a hTailNN hBEx
                  rcases distinct_pairs_eval_bool M (__eo_to_smt x) a hTailNN with
                    ⟨bp, hPairs⟩
                  rcases smt_eval_not_eq_bool M (__eo_to_smt x) (__eo_to_smt y) with
                    ⟨bh, hHead⟩
                  have hRecBool :
                      ∃ br : Bool,
                        __smtx_model_eval M
                          (__eo_to_smt (__mk_distinct_elim_rec x a b)) =
                          SmtValue.Boolean br := by
                    refine ⟨native_and bp bb, ?_⟩
                    rw [hIH, __smtx_model_eval.eq_9, hPairs, hB]
                    simp [__smtx_model_eval_and]
                  have hRecNe :
                      __mk_distinct_elim_rec x a b ≠ Term.Stuck :=
                    term_ne_stuck_of_eval_boolean M
                      (__mk_distinct_elim_rec x a b) hRecBool
                  simp [__mk_distinct_elim_rec, __eo_mk_apply
                    ]
                  rw [__eo_to_smt_distinct_pairs, __smtx_model_eval.eq_9]
                  change
                    __smtx_model_eval M
                        (SmtTerm.and
                          (SmtTerm.not
                            (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)))
                          (__eo_to_smt (__mk_distinct_elim_rec x a b))) =
                      __smtx_model_eval_and
                        (__smtx_model_eval M
                          (SmtTerm.and
                            (SmtTerm.not
                              (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)))
                            (__eo_to_smt_distinct_pairs (__eo_to_smt x) a)))
                        (__smtx_model_eval M (__eo_to_smt b))
                  rw [__smtx_model_eval.eq_9, hIH, __smtx_model_eval.eq_9,
                    __smtx_model_eval.eq_9, hHead, hPairs, hB]
                  exact smt_eval_and_assoc_bool
              | _ =>
                  simp [__eo_to_smt_typed_list_elem_type] at hNN
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | _ =>
          simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.Stuck, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.UOp _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.UOp1 _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.UOp2 _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.UOp3 _ _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.__eo_List, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.__eo_List_nil, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.__eo_List_cons, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.Bool, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.Boolean _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.Numeral _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.Rational _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.String _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.Binary _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.Type, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.FunType, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.Var _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.DatatypeType _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.DatatypeTypeRef _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.DtcAppType _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.DtCons _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.DtSel _ _ _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.USort _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN
  | _hXNe, Term.UConst _ _, hNN, _ => by simp [__eo_to_smt_typed_list_elem_type] at hNN

private theorem mk_distinct_elim_eval
    (M : SmtModel) :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __smtx_model_eval M
          (__eo_to_smt (__mk_distinct_elim
            (Term.Apply (Term.UOp UserOp.distinct) xs))) =
        __smtx_model_eval M (__eo_to_smt_distinct xs)
  | Term.Apply f a, hNN => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [__mk_distinct_elim, __eo_to_smt_distinct, __smtx_model_eval]
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hNN with
                    ⟨_hHeadTail, hHeadNN, hTailNN, _hConsEq⟩
                  have hXNe : x ≠ Term.Stuck :=
                    term_ne_stuck_of_smt_type_non_none x hHeadNN
                  have hTailEval := mk_distinct_elim_eval M a hTailNN
                  rcases distinct_eval_bool M a hTailNN with ⟨bt, hTailBool⟩
                  have hB :
                      ∃ bb : Bool,
                        __smtx_model_eval M
                          (__eo_to_smt (__mk_distinct_elim
                            (Term.Apply (Term.UOp UserOp.distinct) a))) =
                          SmtValue.Boolean bb := by
                    refine ⟨bt, ?_⟩
                    rw [hTailEval, hTailBool]
                  have hRec :=
                    mk_distinct_elim_rec_eval M x
                      (__mk_distinct_elim
                        (Term.Apply (Term.UOp UserOp.distinct) a))
                      hXNe a hTailNN hB
                  rw [__mk_distinct_elim, __eo_to_smt_distinct, hRec]
                  rw [__smtx_model_eval.eq_9, __smtx_model_eval.eq_9,
                    hTailEval]
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

private theorem singleton_elim_and_eval_eq
    (M : SmtModel) (c : Term) :
    (∃ b : Bool, __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean b) ->
    __eo_is_list (Term.UOp UserOp.and) c = Term.Boolean true ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.and) c)) =
      __smtx_model_eval M (__eo_to_smt c) := by
  intro hBool hList
  cases c with
  | Boolean b =>
      cases b <;>
        simp [__eo_list_singleton_elim, __eo_list_singleton_elim_2,
          __eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_list_nil,
          __eo_is_ok, native_ite, native_teq, native_not, SmtEval.native_not]
          at hList ⊢
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | and =>
                  by_cases hNil :
                      __eo_is_list_nil (Term.UOp UserOp.and) a =
                        Term.Boolean true
                  · have haTrue : a = Term.Boolean true := by
                      cases a <;>
                        simp [__eo_is_list_nil] at hNil ⊢
                      case Boolean b =>
                        cases b <;> simp at hNil ⊢
                    subst a
                    rcases hBool with ⟨bc, hBool⟩
                    change
                        __smtx_model_eval M
                          (SmtTerm.and (__eo_to_smt x) (SmtTerm.Boolean true)) =
                          SmtValue.Boolean bc at hBool
                    rw [__smtx_model_eval.eq_9, __smtx_model_eval.eq_1] at hBool
                    have hRight :=
                      smt_eval_and_true_right_eq_of_boolean hBool
                    simp [__eo_list_singleton_elim, hList,
                      __eo_list_singleton_elim_2, __eo_is_list_nil,
                      __eo_ite, native_ite, native_teq,
                      __eo_requires, native_not, SmtEval.native_not]
                    change
                      __smtx_model_eval M (__eo_to_smt x) =
                        __smtx_model_eval M
                          (SmtTerm.and (__eo_to_smt x) (SmtTerm.Boolean true))
                    rw [__smtx_model_eval.eq_9, __smtx_model_eval.eq_1]
                    exact hRight
                  · rw [__eo_list_singleton_elim, hList,
                      __eo_list_singleton_elim_2]
                    cases a <;>
                      simp [__eo_is_list_nil, __eo_ite, __eo_is_list,
                        __eo_get_nil_rec, __eo_is_ok, __eo_requires,
                        native_ite, native_teq, native_not, SmtEval.native_not]
                        at hNil hList ⊢
                    all_goals
                      rename_i bv
                      cases bv <;> simp at hNil ⊢
              | _ =>
                  simp [__eo_is_list, __eo_get_nil_rec, __eo_requires,
                    __eo_is_ok, native_ite, native_teq,
                    native_not, SmtEval.native_not] at hList
          | _ =>
              simp [__eo_is_list, __eo_get_nil_rec, __eo_requires,
                __eo_is_ok, native_ite, native_teq,
                native_not, SmtEval.native_not] at hList
      | _ =>
          simp [__eo_is_list, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
  | _ =>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_list_nil,
        __eo_is_ok, native_ite, native_teq, native_not, SmtEval.native_not]
        at hList

private theorem prog_distinct_elim_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_distinct_elim a1) = Term.Bool ->
  __eo_prog_distinct_elim a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_distinct_elim a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f b2 =>
      cases f with
      | Apply g b1 =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  let guard :=
                    __eo_list_singleton_elim (Term.UOp UserOp.and)
                      (__mk_distinct_elim b1)
                  have hReq :
                      __eo_requires guard b2
                        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2) ≠
                        Term.Stuck := by
                    simpa [__eo_prog_distinct_elim, guard] using hProg
                  simpa [__eo_prog_distinct_elim, guard]
                    using eo_requires_result_eq_of_ne_stuck hReq
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

private theorem typed___eo_prog_distinct_elim_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_distinct_elim a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_distinct_elim a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_distinct_elim a1 = a1 :=
    prog_distinct_elim_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem distinct_elim_shape_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_distinct_elim a1) = Term.Bool ->
  ∃ b1 b2,
    a1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2 ∧
    __eo_list_singleton_elim (Term.UOp UserOp.and)
      (__mk_distinct_elim b1) = b2 ∧
    __eo_list_singleton_elim (Term.UOp UserOp.and)
      (__mk_distinct_elim b1) ≠ Term.Stuck := by
  intro hTy
  have hProg : __eo_prog_distinct_elim a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f b2 =>
      cases f with
      | Apply g b1 =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  let guard :=
                    __eo_list_singleton_elim (Term.UOp UserOp.and)
                      (__mk_distinct_elim b1)
                  have hReq :
                      __eo_requires guard b2
                        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2) ≠
                        Term.Stuck := by
                    simpa [__eo_prog_distinct_elim, guard] using hProg
                  have hGuard : guard = b2 :=
                    eo_requires_arg_eq_of_ne_stuck hReq
                  refine ⟨b1, b2, rfl, ?_, ?_⟩
                  · simpa [guard] using hGuard
                  · intro hStuck
                    have hGuardStuck : guard = Term.Stuck := by
                      simpa [guard] using hStuck
                    have hb2Stuck : b2 = Term.Stuck := by
                      rw [← hGuard, hGuardStuck]
                    apply hReq
                    simp [__eo_requires, hGuardStuck, hb2Stuck, native_teq,
                      native_ite, native_not, SmtEval.native_not]
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

private theorem distinct_elim_sound
    (M : SmtModel) (hM : model_wf M) (b1 b2 : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2) ->
  __eo_list_singleton_elim (Term.UOp UserOp.and)
    (__mk_distinct_elim b1) = b2 ->
  __eo_list_singleton_elim (Term.UOp UserOp.and)
    (__mk_distinct_elim b1) ≠ Term.Stuck ->
  eo_interprets M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2) true := by
  intro hFormulaBool hGuard hGuardNe
  cases b1 with
  | Apply d xs =>
      cases d with
      | UOp op =>
          cases op with
          | distinct =>
              let distinctTerm := Term.Apply (Term.UOp UserOp.distinct) xs
              have hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
                rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    distinctTerm b2 hFormulaBool with
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
              have hMkEval := mk_distinct_elim_eval M xs hElemNN
              rcases distinct_eval_bool M xs hElemNN with ⟨bd, hDistinctEval⟩
              have hMkBool :
                  ∃ b : Bool,
                    __smtx_model_eval M
                      (__eo_to_smt (__mk_distinct_elim distinctTerm)) =
                      SmtValue.Boolean b := by
                refine ⟨bd, ?_⟩
                simpa [distinctTerm] using hMkEval.trans hDistinctEval
              have hMkList :
                  __eo_is_list (Term.UOp UserOp.and)
                    (__mk_distinct_elim distinctTerm) = Term.Boolean true := by
                have hReq :
                    __eo_requires
                      (__eo_is_list (Term.UOp UserOp.and)
                        (__mk_distinct_elim distinctTerm))
                      (Term.Boolean true)
                      (__eo_list_singleton_elim_2
                        (__mk_distinct_elim distinctTerm)) ≠ Term.Stuck := by
                  simpa [distinctTerm, __eo_list_singleton_elim] using hGuardNe
                exact eo_requires_arg_eq_of_ne_stuck hReq
              have hSingletonEval :=
                singleton_elim_and_eval_eq M (__mk_distinct_elim distinctTerm)
                  hMkBool hMkList
              have hB2Eval :
                  __smtx_model_eval M (__eo_to_smt b2) =
                    __smtx_model_eval M (__eo_to_smt distinctTerm) := by
                rw [← hGuard, hSingletonEval, hMkEval, hDistinctSmt]
              apply RuleProofs.eo_interprets_eq_of_rel M distinctTerm b2
              · exact hFormulaBool
              · rw [hB2Eval]
                exact RuleProofs.smt_value_rel_refl
                  (__smtx_model_eval M (__eo_to_smt distinctTerm))
          | _ =>
              exfalso
              exact hGuardNe (by
                simp [__mk_distinct_elim, list_singleton_elim_stuck])
      | _ =>
          exfalso
          exact hGuardNe (by
            simp [__mk_distinct_elim, list_singleton_elim_stuck])
  | _ =>
      exfalso
      exact hGuardNe (by
        simp [__mk_distinct_elim, list_singleton_elim_stuck])

private theorem facts___eo_prog_distinct_elim_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_distinct_elim a1) = Term.Bool ->
  eo_interprets M (__eo_prog_distinct_elim a1) true := by
  intro hA1Trans hResultTy
  rcases distinct_elim_shape_of_typeof_bool a1 hResultTy with
    ⟨b1, b2, rfl, hGuard, hGuardNe⟩
  have hProgEq :
      __eo_prog_distinct_elim
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2) =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2 :=
    prog_distinct_elim_eq_arg_of_typeof_bool
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2) hResultTy
  have hFormulaTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hFormulaBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b1) b2)
      hA1Trans hFormulaTy
  rw [hProgEq]
  exact distinct_elim_sound M hM b1 b2 hFormulaBool hGuard hGuardNe

public theorem cmd_step_distinct_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.distinct_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.distinct_elim args premises ≠ Term.Stuck :=
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
              change __eo_typeof (__eo_prog_distinct_elim A1) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_distinct_elim A1) true
                exact facts___eo_prog_distinct_elim_impl M hM A1
                  hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_distinct_elim A1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_distinct_elim A1)
                  (typed___eo_prog_distinct_elim_impl A1 hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
