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

private theorem nodup_length_le_of_mem
    {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (xs us : List α),
      xs.Nodup ->
      (∀ x, x ∈ xs -> x ∈ us) ->
      xs.length ≤ us.length
  | [], us, _hNodup, _hSub => by
      simp
  | a :: xs, us, hNodup, hSub => by
      rcases (List.nodup_cons.mp hNodup) with ⟨hNotMem, hTailNodup⟩
      have ha : a ∈ us := hSub a (by simp)
      have hSubErase : ∀ x, x ∈ xs -> x ∈ us.erase a := by
        intro x hx
        have hxus : x ∈ us := hSub x (by simp [hx])
        have hxa : x ≠ a := by
          intro hEq
          subst x
          exact hNotMem hx
        exact (List.mem_erase_of_ne hxa).mpr hxus
      have hTailLen :
          xs.length ≤ (us.erase a).length :=
        nodup_length_le_of_mem xs (us.erase a) hTailNodup hSubErase
      have hEraseLen : (us.erase a).length = us.length - 1 :=
        List.length_erase_of_mem ha
      have hUsPos : 0 < us.length := List.length_pos_of_mem ha
      rw [hEraseLen] at hTailLen
      change Nat.succ xs.length ≤ us.length
      omega

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private def boolValues : List SmtValue :=
  [SmtValue.Boolean false, SmtValue.Boolean true]

private def bitvecValues (w : Nat) : List SmtValue :=
  (List.range (2 ^ w)).map
    (fun n => SmtValue.Binary (native_nat_to_int w) (Int.ofNat n))

private theorem bitvecValues_length (w : Nat) :
    (bitvecValues w).length = 2 ^ w := by
  simp [bitvecValues]

private theorem bool_value_mem_universe
    {v : SmtValue} :
    __smtx_typeof_value v = SmtType.Bool ->
    v ∈ boolValues := by
  intro hTy
  rcases bool_value_canonical hTy with ⟨b, rfl⟩
  cases b <;> simp [boolValues]

private theorem bitvec_value_mem_universe
    {w : Nat} {v : SmtValue} :
    __smtx_typeof_value v = SmtType.BitVec w ->
    v ∈ bitvecValues w := by
  intro hTy
  rcases bitvec_value_canonical hTy with ⟨n, rfl⟩
  have hWidthBool :
      native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, native_nat_to_int]
  have hMod :
      native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true :=
    bitvec_payload_canonical hTy
  have hRange := bitvec_payload_range_of_canonical hWidthBool hMod
  have hLtInt : n < (2 ^ w : Int) := by
    simpa [native_int_pow2_nat] using hRange.2
  have hNatLt : Int.toNat n < 2 ^ w :=
    (Int.toNat_lt hRange.1).mpr hLtInt
  rw [bitvecValues, List.mem_map]
  refine ⟨Int.toNat n, ?_, ?_⟩
  · simpa [List.mem_range] using hNatLt
  · simp [Int.toNat_of_nonneg hRange.1]

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

private theorem typed_list_eval_elem_type
    (M : SmtModel) (hM : model_wf M) :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      ∀ v, v ∈ typedListEvalElems M xs ->
        __smtx_typeof_value v = __eo_to_smt_typed_list_elem_type xs
  | Term.Apply f a, hNN, v, hv => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [typedListEvalElems, typedListElems] at hv
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hNN with
                    ⟨hHeadTail, hHeadNN, hTailNN, hConsEq⟩
                  simp [typedListEvalElems, typedListElems] at hv
                  rcases hv with hHead | hTail
                  · subst v
                    have hHeadNNTerm :
                        term_has_non_none_type (__eo_to_smt x) := by
                      simpa [term_has_non_none_type] using hHeadNN
                    have hPres :=
                      smt_model_eval_preserves_type_of_non_none M hM
                        (__eo_to_smt x) hHeadNNTerm
                    simpa [hConsEq] using hPres
                  · have hTailMem : v ∈ typedListEvalElems M a := by
                      simpa [typedListEvalElems] using hTail
                    have hTailTy :=
                      typed_list_eval_elem_type M hM a hTailNN v hTailMem
                    simpa [hConsEq, hHeadTail] using hTailTy
              | _ =>
                  simp [__eo_to_smt_typed_list_elem_type] at hNN
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | _ =>
          simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Stuck, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp1 _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp2 _ _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UOp3 _ _ _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List_nil, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.__eo_List_cons, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Bool, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Boolean _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Numeral _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Rational _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.String _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Binary _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Type, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.FunType, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.Var _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DatatypeType _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DatatypeTypeRef _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtcAppType _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtCons _ _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.DtSel _ _ _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.USort _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN
  | Term.UConst _ _, hNN, _v, _hv => by
      simp [__eo_to_smt_typed_list_elem_type] at hNN

private theorem typed_list_len_rec_eq
    : ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __eo_list_len_rec xs = Term.Numeral (Int.ofNat (typedListElems xs).length)
  | Term.Apply f a, hNN => by
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              simp [typedListElems, __eo_list_len_rec]
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  rcases typed_list_cons_type_parts x a hNN with
                    ⟨_hHeadTail, _hHeadNN, hTailNN, _hConsEq⟩
                  have hTailLen := typed_list_len_rec_eq a hTailNN
                  simp [typedListElems, __eo_list_len_rec, __eo_add,
                    hTailLen, native_zplus]
                  rw [Int.add_comm]
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

private theorem typed_list_len_eq
    (xs : Term)
    (hNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    __eo_list_len (Term.UOp UserOp._at__at_TypedList_cons) xs =
      Term.Numeral (Int.ofNat (typedListElems xs).length) := by
  have hList := typed_list_is_list_true xs hNN
  have hLenRec := typed_list_len_rec_eq xs hNN
  simp [__eo_list_len, __eo_requires, hList, hLenRec, native_teq,
    native_ite, native_not, SmtEval.native_not]

private theorem compute_card_guard_cases
    {len : Nat} {elemTy : SmtType} {ty : Term} :
    elemTy = __eo_to_smt_type ty ->
    elemTy ≠ SmtType.None ->
    __eo_gt (Term.Numeral (Int.ofNat len)) (__compute_card ty) =
      Term.Boolean true ->
    (elemTy = SmtType.Bool ∧ 2 < len) ∨
      (∃ w : Nat, elemTy = SmtType.BitVec w ∧ 2 ^ w < len) := by
  intro hElemEq hElemNN hGuard
  cases ty with
  | Bool =>
      left
      constructor
      · simpa [__eo_to_smt_type] using hElemEq
      · have hInt : (2 : Int) < Int.ofNat len := by
          simpa [__compute_card, __eo_gt, native_zlt] using hGuard
        exact Int.ofNat_lt.mp hInt
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases a with
              | Numeral w =>
                  have hWidthBool : native_zleq 0 w = true := by
                    cases hWidth : native_zleq 0 w
                    · have hNone : elemTy = SmtType.None := by
                        simpa [__eo_to_smt_type, native_ite, hWidth]
                          using hElemEq
                      exact False.elim (hElemNN hNone)
                    · rfl
                  have hWidth : 0 ≤ w := by
                    simpa [native_zleq] using hWidthBool
                  have hnot : ¬ w < 0 := Int.not_lt_of_ge hWidth
                  have hElemTy :
                      elemTy = SmtType.BitVec (native_int_to_nat w) := by
                    simpa [__eo_to_smt_type, native_ite, hWidthBool]
                      using hElemEq
                  have hGuardInt :
                      native_int_pow2 w < Int.ofNat len := by
                    simpa [__compute_card, __eo_gt, __eo_ite, __eo_is_z,
                      __eo_is_z_internal, __eo_is_neg, __eo_pow, native_ite,
                      native_teq, native_and, native_not, SmtEval.native_not,
                      native_zlt, native_zexp_total, native_int_pow2, hnot]
                      using hGuard
                  have hWidthEq :
                      w = native_nat_to_int (native_int_to_nat w) := by
                    calc
                      w = Int.ofNat (Int.toNat w) := by
                        exact (Int.toNat_of_nonneg hWidth).symm
                      _ = native_nat_to_int (native_int_to_nat w) := by
                        rfl
                  have hPowEq :
                      native_int_pow2 w =
                        (2 ^ native_int_to_nat w : Int) := by
                    calc
                      native_int_pow2 w =
                          native_int_pow2
                            (native_nat_to_int (native_int_to_nat w)) := by
                        rw [← hWidthEq]
                      _ = (2 ^ native_int_to_nat w : Int) :=
                        native_int_pow2_nat (native_int_to_nat w)
                  have hLenGt : 2 ^ native_int_to_nat w < len := by
                    have hInt :
                        (2 ^ native_int_to_nat w : Int) < Int.ofNat len := by
                      simpa [hPowEq] using hGuardInt
                    exact Int.ofNat_lt.mp hInt
                  right
                  exact ⟨native_int_to_nat w, hElemTy, hLenGt⟩
              | _ =>
                  have hNone : elemTy = SmtType.None := by
                    simpa [__eo_to_smt_type] using hElemEq
                  exact False.elim (hElemNN hNone)
          | _ =>
              simp [__compute_card, __eo_gt] at hGuard
      | _ =>
          simp [__compute_card, __eo_gt] at hGuard
  | _ =>
      simp [__compute_card, __eo_gt] at hGuard

private theorem distinct_true_guard_contradiction
    (M : SmtModel) (hM : model_wf M) (xs : Term) :
  __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
  __eo_gt
    (__eo_list_len (Term.UOp UserOp._at__at_TypedList_cons) xs)
    (__compute_card
      (__assoc_nil_nth_type (Term.UOp UserOp._at__at_TypedList_cons) xs
        (Term.Numeral 0))) = Term.Boolean true ->
  (typedListEvalElems M xs).Nodup ->
  False := by
  intro hElemNN hGuard hNodup
  have hLenEq := typed_list_len_eq xs hElemNN
  cases xs with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              rw [hLenEq] at hGuard
              simp [typedListElems, __assoc_nil_nth_type,
                __eo_l_1___assoc_nil_nth_type, __compute_card, __eo_gt]
                at hGuard
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hElemNN
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  let consTerm :=
                    Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x)
                      a
                  rcases typed_list_cons_type_parts x a hElemNN with
                    ⟨_hHeadTail, hHeadNN, _hTailNN, hConsEq⟩
                  have hAssoc :
                      __assoc_nil_nth_type
                        (Term.UOp UserOp._at__at_TypedList_cons) consTerm
                        (Term.Numeral 0) = __eo_typeof x := by
                    simp [consTerm, __assoc_nil_nth_type, __eo_eq, __eo_ite,
                      native_teq, native_ite]
                  have hGuard' :
                      __eo_gt
                        (Term.Numeral
                          (Int.ofNat (typedListElems consTerm).length))
                        (__compute_card (__eo_typeof x)) = Term.Boolean true := by
                    simpa [consTerm, hLenEq, hAssoc] using hGuard
                  have hHeadNNTerm :
                      term_has_non_none_type (__eo_to_smt x) := by
                    simpa [term_has_non_none_type] using hHeadNN
                  have hMatch :=
                    TranslationProofs.eo_to_smt_typeof_matches_translation
                      x hHeadNNTerm
                  have hElemEq :
                      __eo_to_smt_typed_list_elem_type consTerm =
                        __eo_to_smt_type (__eo_typeof x) := by
                    simpa [consTerm] using hConsEq.trans hMatch
                  have hCardCases :=
                    compute_card_guard_cases
                      (len := (typedListElems consTerm).length)
                      (elemTy := __eo_to_smt_typed_list_elem_type consTerm)
                      (ty := __eo_typeof x) hElemEq hElemNN hGuard'
                  rcases hCardCases with hBool | hBv
                  ·
                      rcases hBool with ⟨hElemBool, hLenGt⟩
                      have hAllMem :
                          ∀ v, v ∈ typedListEvalElems M consTerm ->
                            v ∈ boolValues := by
                        intro v hv
                        exact bool_value_mem_universe (by
                          simpa [hElemBool] using
                            typed_list_eval_elem_type M hM consTerm hElemNN
                              v hv)
                      have hLenLe :
                          (typedListEvalElems M consTerm).length ≤
                            boolValues.length :=
                        nodup_length_le_of_mem
                          (typedListEvalElems M consTerm) boolValues hNodup
                          hAllMem
                      have hEvalLen :
                          (typedListEvalElems M consTerm).length =
                            (typedListElems consTerm).length := by
                        simp [typedListEvalElems]
                      have hBoolLen : boolValues.length = 2 := by
                        simp [boolValues]
                      rw [hEvalLen, hBoolLen] at hLenLe
                      omega
                  ·
                      rcases hBv with ⟨w, hElemBv, hLenGt⟩
                      have hAllMem :
                          ∀ v, v ∈ typedListEvalElems M consTerm ->
                            v ∈ bitvecValues w := by
                        intro v hv
                        exact bitvec_value_mem_universe (by
                          simpa [hElemBv] using
                            typed_list_eval_elem_type M hM consTerm hElemNN
                              v hv)
                      have hLenLe :
                          (typedListEvalElems M consTerm).length ≤
                            (bitvecValues w).length :=
                        nodup_length_le_of_mem
                          (typedListEvalElems M consTerm) (bitvecValues w)
                          hNodup hAllMem
                      have hEvalLen :
                          (typedListEvalElems M consTerm).length =
                            (typedListElems consTerm).length := by
                        simp [typedListEvalElems]
                      have hBvLen := bitvecValues_length w
                      rw [hEvalLen, hBvLen] at hLenLe
                      omega
              | _ =>
                  simp [__eo_to_smt_typed_list_elem_type] at hElemNN
          | _ =>
              simp [__eo_to_smt_typed_list_elem_type] at hElemNN
      | _ =>
          simp [__eo_to_smt_typed_list_elem_type] at hElemNN
  | _ =>
      simp [__eo_to_smt_typed_list_elem_type] at hElemNN

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

private theorem prog_distinct_card_conflict_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_distinct_card_conflict a1) = Term.Bool ->
  __eo_prog_distinct_card_conflict a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_distinct_card_conflict a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f b =>
      cases f with
      | Apply g a =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases a with
                  | Apply d xs =>
                      cases d with
                      | UOp dop =>
                          cases dop with
                          | distinct =>
                              cases b with
                              | Boolean bv =>
                                  cases bv with
                                  | false =>
                                      let guard :=
                                        __eo_gt
                                          (__eo_list_len
                                            (Term.UOp UserOp._at__at_TypedList_cons) xs)
                                          (__compute_card
                                            (__assoc_nil_nth_type
                                              (Term.UOp UserOp._at__at_TypedList_cons) xs
                                              (Term.Numeral 0)))
                                      have hReq :
                                          __eo_requires guard (Term.Boolean true)
                                            (Term.Apply
                                              (Term.Apply (Term.UOp UserOp.eq)
                                                (Term.Apply (Term.UOp UserOp.distinct) xs))
                                              (Term.Boolean false)) ≠ Term.Stuck := by
                                        simpa [__eo_prog_distinct_card_conflict, guard]
                                          using hProg
                                      simpa [__eo_prog_distinct_card_conflict, guard]
                                        using eo_requires_result_eq_of_ne_stuck hReq
                                  | true =>
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
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed___eo_prog_distinct_card_conflict_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_distinct_card_conflict a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_distinct_card_conflict a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_distinct_card_conflict a1 = a1 :=
    prog_distinct_card_conflict_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem distinct_card_conflict_shape_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_distinct_card_conflict a1) = Term.Bool ->
  ∃ xs,
    a1 =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (Term.Boolean false) ∧
    __eo_gt
      (__eo_list_len (Term.UOp UserOp._at__at_TypedList_cons) xs)
      (__compute_card
        (__assoc_nil_nth_type (Term.UOp UserOp._at__at_TypedList_cons) xs
          (Term.Numeral 0))) = Term.Boolean true := by
  intro hTy
  have hProg : __eo_prog_distinct_card_conflict a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f b =>
      cases f with
      | Apply g a =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases a with
                  | Apply d xs =>
                      cases d with
                      | UOp dop =>
                          cases dop with
                          | distinct =>
                              cases b with
                              | Boolean bv =>
                                  cases bv with
                                  | false =>
                                      let guard :=
                                        __eo_gt
                                          (__eo_list_len
                                            (Term.UOp UserOp._at__at_TypedList_cons) xs)
                                          (__compute_card
                                            (__assoc_nil_nth_type
                                              (Term.UOp UserOp._at__at_TypedList_cons) xs
                                              (Term.Numeral 0)))
                                      have hReq :
                                          __eo_requires guard (Term.Boolean true)
                                            (Term.Apply
                                              (Term.Apply (Term.UOp UserOp.eq)
                                                (Term.Apply (Term.UOp UserOp.distinct) xs))
                                              (Term.Boolean false)) ≠ Term.Stuck := by
                                        simpa [__eo_prog_distinct_card_conflict, guard]
                                          using hProg
                                      have hGuard : guard = Term.Boolean true :=
                                        eo_requires_arg_eq_of_ne_stuck hReq
                                      refine ⟨xs, rfl, ?_⟩
                                      simpa [guard] using hGuard
                                  | true =>
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
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem distinct_card_conflict_cardinality_sound
    (M : SmtModel) (hM : model_wf M) (xs : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (Term.Boolean false)) ->
  __eo_gt
    (__eo_list_len (Term.UOp UserOp._at__at_TypedList_cons) xs)
    (__compute_card
      (__assoc_nil_nth_type (Term.UOp UserOp._at__at_TypedList_cons) xs
        (Term.Numeral 0))) = Term.Boolean true ->
  eo_interprets M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.distinct) xs))
      (Term.Boolean false)) true := by
  intro hFormulaBool hGuard
  let distinctTerm := Term.Apply (Term.UOp UserOp.distinct) xs
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      distinctTerm (Term.Boolean false) hFormulaBool with
    ⟨hDistinctTyEq, _hDistinctNN⟩
  have hFalseTy :
      __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool := by
    rw [__smtx_typeof.eq_1]
  have hDistinctTy :
      __smtx_typeof (__eo_to_smt distinctTerm) = SmtType.Bool := by
    simpa [hFalseTy] using hDistinctTyEq
  have hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    intro hNone
    have hDistinctNone :
        __smtx_typeof (__eo_to_smt distinctTerm) = SmtType.None := by
      change __smtx_typeof
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct xs)) = SmtType.None
      simp [hNone, native_Teq, native_ite]
    simp [hDistinctNone] at hDistinctTy
  have hDistinctSmt :
      __eo_to_smt distinctTerm = __eo_to_smt_distinct xs := by
    change native_ite
      (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) = __eo_to_smt_distinct xs
    simp [native_Teq, native_ite, hElemNN]
  rcases smt_model_eval_bool_is_boolean M hM
      (__eo_to_smt distinctTerm) hDistinctTy with
    ⟨b, hDistinctEval⟩
  cases b with
  | false =>
      have hEval :
          __smtx_model_eval M
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq) distinctTerm)
                (Term.Boolean false))) = SmtValue.Boolean true := by
        change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt distinctTerm) (SmtTerm.Boolean false)) =
            SmtValue.Boolean true
        rw [smtx_eval_eq_term_eq, hDistinctEval, __smtx_model_eval.eq_1]
        exact RuleProofs.smtx_model_eval_eq_refl (SmtValue.Boolean false)
      exact RuleProofs.eo_interprets_of_bool_eval M
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) distinctTerm)
          (Term.Boolean false)) true hFormulaBool hEval
  | true =>
      have hRawEval :
          __smtx_model_eval M (__eo_to_smt_distinct xs) =
            SmtValue.Boolean true := by
        simpa [hDistinctSmt] using hDistinctEval
      have hNodup := distinct_true_nodup M xs hRawEval
      exact False.elim
        (distinct_true_guard_contradiction M hM xs hElemNN hGuard hNodup)

private theorem facts___eo_prog_distinct_card_conflict_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_distinct_card_conflict a1) = Term.Bool ->
  eo_interprets M (__eo_prog_distinct_card_conflict a1) true := by
  intro hA1Trans hResultTy
  rcases distinct_card_conflict_shape_of_typeof_bool a1 hResultTy with
    ⟨xs, rfl, hGuard⟩
  have hProgEq :
      __eo_prog_distinct_card_conflict
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean false)) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean false) :=
    prog_distinct_card_conflict_eq_arg_of_typeof_bool
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.distinct) xs))
        (Term.Boolean false)) hResultTy
  have hFormulaTy :
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.distinct) xs))
          (Term.Boolean false)) = Term.Bool := by
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
        (Term.Boolean false)) hA1Trans hFormulaTy
  rw [hProgEq]
  exact distinct_card_conflict_cardinality_sound M hM xs hFormulaBool hGuard

public theorem cmd_step_distinct_card_conflict_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_card_conflict args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.distinct_card_conflict args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_card_conflict args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.distinct_card_conflict args premises ≠ Term.Stuck :=
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
              change __eo_typeof (__eo_prog_distinct_card_conflict A1) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_distinct_card_conflict A1) true
                exact facts___eo_prog_distinct_card_conflict_impl M hM A1
                  hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_distinct_card_conflict A1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_distinct_card_conflict A1)
                  (typed___eo_prog_distinct_card_conflict_impl A1
                    hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
