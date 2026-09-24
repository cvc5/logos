module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.SetsMemberSupport
import all Cpc.Proofs.RuleSupport.SetsMemberSupport
public import Cpc.Proofs.RuleSupport.DtConsEqSupport
import all Cpc.Proofs.RuleSupport.DtConsEqSupport

public section

open Eo
open SmtEval
open Smtm
open SetsMemberSupport

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

theorem eo_ite_eq_false_guard_true {a b d : Term} :
    __eo_ite (__eo_eq a b) (Term.Boolean false) d = Term.Boolean true ->
    __eo_eq a b = Term.Boolean false ∧ d = Term.Boolean true := by
  intro h
  unfold __eo_ite at h
  by_cases ht : native_teq (__eo_eq a b) (Term.Boolean true) = true
  · simp [ht, native_ite] at h
  · by_cases hf : native_teq (__eo_eq a b) (Term.Boolean false) = true
    · have hEq : __eo_eq a b = Term.Boolean false := by
        simpa [native_teq] using hf
      simp [ht, hf, native_ite] at h
      exact ⟨hEq, h⟩
    · simp [ht, hf, native_ite] at h

private theorem eo_ite_eq_true_cases (c t e : Term) :
    __eo_ite c t e = Term.Boolean true ->
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h
  case Boolean b =>
    cases b <;> simp at h
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl ⟨rfl, h⟩

private theorem dt_ite_is_ok_self_true {v : Term} :
    __eo_ite (__eo_is_ok v) v (Term.Boolean false) = Term.Boolean true ->
    v = Term.Boolean true := by
  intro h
  rcases eo_ite_eq_true_cases _ _ _ h with ⟨_, hv⟩ | ⟨_, hFalse⟩
  · exact hv
  · simp at hFalse

private theorem eo_eq_false_ne {a b : Term} :
    __eo_eq a b = Term.Boolean false -> a ≠ b := by
  intro h hEq
  subst b
  cases a <;> simp [__eo_eq, native_teq] at h

private theorem eo_and_true {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;> simp [__eo_and, __eo_requires, native_teq,
    native_ite, SmtEval.native_and, SmtEval.native_not] at h ⊢
  · exact h
  · split at h <;> simp at h

private theorem eo_or_true {a b : Term} :
    __eo_or a b = Term.Boolean true ->
    a = Term.Boolean true ∨ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_or, native_or, __eo_requires, native_teq, native_ite,
      SmtEval.native_not] at h ⊢
  case Boolean.Boolean x y =>
    cases x <;> cases y <;> simp at h ⊢
  case Binary.Binary w₁ n₁ w₂ n₂ =>
    by_cases hw : w₁ = w₂
    · subst w₂
      simp at h
    · simp [hw] at h

private theorem map_native_ssm_char_char :
    ∀ s : native_String,
      List.map (impl_native_ssm_char_of_value ∘ SmtValue.Char) s = s
  | [] => rfl
  | _ :: cs => by
      simp [Function.comp_def, impl_native_ssm_char_of_value]

private theorem are_distinct_int_true {a b : Term} :
    __are_distinct_terms_type a b (Term.UOp UserOp.Int) = Term.Boolean true ->
    ∃ m n, a = Term.Numeral m ∧ b = Term.Numeral n := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_z,
      __eo_is_z_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i m n
    exact ⟨m, n, rfl, rfl⟩

private theorem are_distinct_real_true {a b : Term} :
    __are_distinct_terms_type a b (Term.UOp UserOp.Real) = Term.Boolean true ->
    ∃ q r, a = Term.Rational q ∧ b = Term.Rational r := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_q,
      __eo_is_q_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i q r
    exact ⟨q, r, rfl, rfl⟩

private theorem are_distinct_string_true {a b : Term} :
    __are_distinct_terms_type a b
        (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) =
      Term.Boolean true ->
    ∃ s t, a = Term.String s ∧ b = Term.String t := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_str,
      __eo_is_str_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i s t
    exact ⟨s, t, rfl, rfl⟩

private theorem are_distinct_bin_true {a b n : Term} :
    __are_distinct_terms_type a b (Term.Apply (Term.UOp UserOp.BitVec) n) =
      Term.Boolean true ->
    ∃ w k w' k', a = Term.Binary w k ∧ b = Term.Binary w' k' := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_bin,
      __eo_is_bin_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i w k w' k'
    exact ⟨w, k, w', k', rfl, rfl⟩

private theorem are_distinct_bool_true {a b : Term} :
    __are_distinct_terms_type a b Term.Bool = Term.Boolean true ->
    ∃ x y, a = Term.Boolean x ∧ b = Term.Boolean y := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_bool,
      __eo_is_bool_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i x y
    exact ⟨x, y, rfl, rfl⟩

private theorem model_eval_eq_false_of_literal_ne
    (M : SmtModel) {a b : Term}
    (ha : a ≠ b)
    (hLit :
      (∃ m n, a = Term.Numeral m ∧ b = Term.Numeral n) ∨
      (∃ q r, a = Term.Rational q ∧ b = Term.Rational r) ∨
      (∃ s t, a = Term.String s ∧ b = Term.String t) ∨
      (∃ w n w' n', a = Term.Binary w n ∧ b = Term.Binary w' n') ∨
      (∃ x y, a = Term.Boolean x ∧ b = Term.Boolean y)) :
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  rcases hLit with ⟨m, n, rfl, rfl⟩
    | ⟨q, r, rfl, rfl⟩
    | ⟨s, t, rfl, rfl⟩
    | ⟨w, n, w', n', rfl, rfl⟩
    | ⟨x, y, rfl, rfl⟩
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Numeral m))
        (__smtx_model_eval M (SmtTerm.Numeral n)) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_2, __smtx_model_eval.eq_2]
    simpa [__smtx_model_eval_eq, native_veq] using ha
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Rational q))
        (__smtx_model_eval M (SmtTerm.Rational r)) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_3, __smtx_model_eval.eq_3]
    simpa [__smtx_model_eval_eq, native_veq] using ha
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.String s))
        (__smtx_model_eval M (SmtTerm.String t)) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_4, __smtx_model_eval.eq_4]
    simp [__smtx_model_eval_eq, native_veq]
    intro hPack
    apply ha
    have hUnpack := congrArg native_unpack_string hPack
    simpa [native_unpack_string, native_pack_string, Smtm.native_unpack_pack_seq,
      map_native_ssm_char_char] using hUnpack
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Binary w n))
        (__smtx_model_eval M (SmtTerm.Binary w' n')) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_5, __smtx_model_eval.eq_5]
    simpa [__smtx_model_eval_eq, native_veq] using ha
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Boolean x))
        (__smtx_model_eval M (SmtTerm.Boolean y)) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_1, __smtx_model_eval.eq_1]
    simpa [__smtx_model_eval_eq, native_veq] using ha

private theorem are_distinct_terms_type_primitive_model_eval_eq_false
    (M : SmtModel) (a b T : Term) :
    __eo_eq a b = Term.Boolean false ->
    __are_distinct_terms_type a b T = Term.Boolean true ->
    (T = Term.UOp UserOp.Int ∨
      T = Term.UOp UserOp.Real ∨
      T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∨
      (∃ n, T = Term.Apply (Term.UOp UserOp.BitVec) n) ∨
      T = Term.Bool) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro hEq hDistinct hT
  have hNe : a ≠ b := eo_eq_false_ne hEq
  rcases hT with rfl | rfl | rfl | ⟨n, rfl⟩ | rfl
  · rcases are_distinct_int_true hDistinct with ⟨m, n, rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe (Or.inl ⟨m, n, rfl, rfl⟩)
  · rcases are_distinct_real_true hDistinct with ⟨q, r, rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe (Or.inr <| Or.inl ⟨q, r, rfl, rfl⟩)
  · rcases are_distinct_string_true hDistinct with ⟨s, t, rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe
      (Or.inr <| Or.inr <| Or.inl ⟨s, t, rfl, rfl⟩)
  · rcases are_distinct_bin_true hDistinct with ⟨w, k, w', k', rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe
      (Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨w, k, w', k', rfl, rfl⟩)
  · rcases are_distinct_bool_true hDistinct with ⟨x, y, rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe
      (Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨x, y, rfl, rfl⟩)

private theorem smtx_model_eval_eq_false_of_ne_not_reglan
    {v₁ v₂ : SmtValue}
    (hNe : v₁ ≠ v₂)
    (hReg :
      ¬ ∃ r₁ r₂, v₁ = SmtValue.RegLan r₁ ∧ v₂ = SmtValue.RegLan r₂) :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false := by
  cases v₁ <;> cases v₂ <;>
    simp [__smtx_model_eval_eq, native_veq] at hNe hReg ⊢
  all_goals exact hNe

private theorem smtx_model_eval_eq_false_of_type_ne
    (M : SmtModel) (hM : model_wf M) (x y : SmtTerm) :
    __smtx_typeof x ≠ SmtType.None ->
    __smtx_typeof y ≠ SmtType.None ->
    __smtx_typeof x ≠ __smtx_typeof y ->
    __smtx_model_eval_eq (__smtx_model_eval M x)
        (__smtx_model_eval M y) =
      SmtValue.Boolean false := by
  intro hxNN hyNN hTyNe
  have hxTy :
      __smtx_typeof_value (__smtx_model_eval M x) =
        __smtx_typeof x :=
    smt_model_eval_preserves_type_of_non_none M hM x
      (by
        unfold term_has_non_none_type
        exact hxNN)
  have hyTy :
      __smtx_typeof_value (__smtx_model_eval M y) =
        __smtx_typeof y :=
    smt_model_eval_preserves_type_of_non_none M hM y
      (by
        unfold term_has_non_none_type
        exact hyNN)
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hEq
      apply hTyNe
      rw [← hxTy, ← hyTy, hEq])
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, hxReg, hyReg⟩
      apply hTyNe
      rw [← hxTy, ← hyTy, hxReg, hyReg]
      rfl)

private theorem set_value_model_eval_eq_false_of_lookup_witness
    {v₁ v₂ : SmtValue} :
    (∃ m₁ m₂ w,
      v₁ = SmtValue.Set m₁ ∧
      v₂ = SmtValue.Set m₂ ∧
      __smtx_map_lookup m₁ w = SmtValue.Boolean true ∧
      __smtx_map_lookup m₂ w = SmtValue.Boolean false) ->
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false := by
  rintro ⟨m₁, m₂, w, rfl, rfl, hLookup₁, hLookup₂⟩
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    injection hEq with hMapEq
    have hLookupEq :
        __smtx_map_lookup m₁ w = __smtx_map_lookup m₂ w := by
      rw [hMapEq]
    rw [hLookup₁, hLookup₂] at hLookupEq
    cases hLookupEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    cases hReg₁

private theorem set_singleton_set_singleton_lookup_witness_of_head
    (M : SmtModel) (e₁ e₂ : Term) :
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    ∃ m₁ m₂ w,
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₁)) =
        SmtValue.Set m₁ ∧
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₂)) =
        SmtValue.Set m₂ ∧
      __smtx_map_lookup m₁ w = SmtValue.Boolean true ∧
      __smtx_map_lookup m₂ w = SmtValue.Boolean false := by
  intro hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hVeq : native_veq v₂ v₁ = false :=
    native_veq_false_symm
      (RuleProofs.native_veq_false_of_model_eval_eq_false
        (v1 := v₁) (v2 := v₂) hHeadEqFalse)
  refine
    ⟨SmtMap.cons v₁ (SmtValue.Boolean true)
        (SmtMap.default (__smtx_typeof_value v₁) (SmtValue.Boolean false)),
      SmtMap.cons v₂ (SmtValue.Boolean true)
        (SmtMap.default (__smtx_typeof_value v₂) (SmtValue.Boolean false)),
      v₁, ?_, ?_, ?_, ?_⟩
  · change __smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e₁)) =
      SmtValue.Set
        (SmtMap.cons v₁ (SmtValue.Boolean true)
          (SmtMap.default (__smtx_typeof_value v₁) (SmtValue.Boolean false)))
    rw [smtx_eval_set_singleton_term_eq]
    rfl
  · change __smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e₂)) =
      SmtValue.Set
        (SmtMap.cons v₂ (SmtValue.Boolean true)
          (SmtMap.default (__smtx_typeof_value v₂) (SmtValue.Boolean false)))
    rw [smtx_eval_set_singleton_term_eq]
    rfl
  · simp [__smtx_map_lookup, native_veq, native_ite]
  · simp [__smtx_map_lookup, hVeq, native_ite]

private theorem set_singleton_set_empty_lookup_witness
    (M : SmtModel) (e U : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)) ->
    ∃ m₁ m₂ w,
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e)) =
        SmtValue.Set m₁ ∧
      __smtx_model_eval M
          (__eo_to_smt
            (Term.UOp1 UserOp1.set_empty
              (Term.Apply (Term.UOp UserOp.Set) U))) =
        SmtValue.Set m₂ ∧
      __smtx_map_lookup m₁ w = SmtValue.Boolean true ∧
      __smtx_map_lookup m₂ w = SmtValue.Boolean false := by
  intro hEmptyTrans
  have hSetTy :
      ∃ T, __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U) =
        SmtType.Set T := by
    cases hTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U)
    case Set T =>
      exact ⟨T, rfl⟩
    all_goals
      exfalso
      apply hEmptyTrans
      change __smtx_typeof
          (__eo_to_smt_set_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U))) =
        SmtType.None
      rw [hTy]
      simp [__eo_to_smt_set_empty]
  rcases hSetTy with ⟨T, hTy⟩
  let v := __smtx_model_eval M (__eo_to_smt e)
  refine
    ⟨SmtMap.cons v (SmtValue.Boolean true)
        (SmtMap.default (__smtx_typeof_value v) (SmtValue.Boolean false)),
      SmtMap.default T (SmtValue.Boolean false), v, ?_, ?_, ?_, ?_⟩
  · change __smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e)) =
      SmtValue.Set
        (SmtMap.cons v (SmtValue.Boolean true)
          (SmtMap.default (__smtx_typeof_value v) (SmtValue.Boolean false)))
    rw [smtx_eval_set_singleton_term_eq]
    rfl
  · change __smtx_model_eval M
        (__eo_to_smt_set_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U))) =
      SmtValue.Set (SmtMap.default T (SmtValue.Boolean false))
    rw [hTy]
    change __smtx_model_eval M (SmtTerm.set_empty T) =
      SmtValue.Set (SmtMap.default T (SmtValue.Boolean false))
    rw [smtx_eval_set_empty_term_eq]
  · simp [__smtx_map_lookup, native_veq, native_ite]
  · simp [__smtx_map_lookup]

private theorem set_union_lookup_true_of_left_true
    {m₁ m₂ : SmtMap} {A : SmtType} {w : SmtValue}
    (hm₁Ty : __smtx_typeof_map_value m₁ = SmtType.Map A SmtType.Bool)
    (hm₂Ty : __smtx_typeof_map_value m₂ = SmtType.Map A SmtType.Bool)
    (hm₁Can : __smtx_map_canonical m₁ = true)
    (hm₂Can : __smtx_map_canonical m₂ = true)
    (hm₁Def : __smtx_map_get_default m₁ = SmtValue.Boolean false)
    (hLeft : __smtx_map_lookup m₁ w = SmtValue.Boolean true) :
    __smtx_map_lookup
        (__smtx_set_op_rec false m₁
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m₁))
            (SmtValue.Boolean false))
          m₂) w =
      SmtValue.Boolean true := by
  let empty :=
    SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m₁))
      (SmtValue.Boolean false)
  have hEmptyTy :
      __smtx_typeof_map_value empty = SmtType.Map A SmtType.Bool := by
    dsimp [empty]
    simp [__smtx_typeof_map_value, __smtx_index_typeof_map, hm₁Ty,
      __smtx_typeof_value]
  have hEmptyLookup :
      __smtx_map_lookup empty w = SmtValue.Boolean false := by
    simp [empty, __smtx_map_lookup]
  have hUnion :=
    mss_op_lookup_acc false (m1 := m₁) (m2 := empty) (acc := m₂)
      (A := A) (i := w) hm₁Ty hEmptyTy hm₂Ty hm₁Can hm₂Can hm₁Def
  simpa [empty, hLeft, hEmptyLookup, native_veq, native_iff,
    SmtEval.native_and, native_ite] using hUnion

private theorem set_union_lookup_false_of_both_false
    {m₁ m₂ : SmtMap} {A : SmtType} {w : SmtValue}
    (hm₁Ty : __smtx_typeof_map_value m₁ = SmtType.Map A SmtType.Bool)
    (hm₂Ty : __smtx_typeof_map_value m₂ = SmtType.Map A SmtType.Bool)
    (hm₁Can : __smtx_map_canonical m₁ = true)
    (hm₂Can : __smtx_map_canonical m₂ = true)
    (hm₁Def : __smtx_map_get_default m₁ = SmtValue.Boolean false)
    (hLeft : __smtx_map_lookup m₁ w = SmtValue.Boolean false)
    (hRight : __smtx_map_lookup m₂ w = SmtValue.Boolean false) :
    __smtx_map_lookup
        (__smtx_set_op_rec false m₁
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m₁))
            (SmtValue.Boolean false))
          m₂) w =
      SmtValue.Boolean false := by
  let empty :=
    SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m₁))
      (SmtValue.Boolean false)
  have hEmptyTy :
      __smtx_typeof_map_value empty = SmtType.Map A SmtType.Bool := by
    dsimp [empty]
    simp [__smtx_typeof_map_value, __smtx_index_typeof_map, hm₁Ty,
      __smtx_typeof_value]
  have hEmptyLookup :
      __smtx_map_lookup empty w = SmtValue.Boolean false := by
    simp [empty, __smtx_map_lookup]
  have hUnion :=
    mss_op_lookup_acc false (m1 := m₁) (m2 := empty) (acc := m₂)
      (A := A) (i := w) hm₁Ty hEmptyTy hm₂Ty hm₁Can hm₂Can hm₁Def
  simpa [empty, hLeft, hRight, native_veq, native_iff,
    SmtEval.native_and, native_ite] using hUnion

private theorem set_union_lookup_true_of_right_true
    {m₁ m₂ : SmtMap} {A : SmtType} {w : SmtValue}
    (hm₁Ty : __smtx_typeof_map_value m₁ = SmtType.Map A SmtType.Bool)
    (hm₂Ty : __smtx_typeof_map_value m₂ = SmtType.Map A SmtType.Bool)
    (hm₁Can : __smtx_map_canonical m₁ = true)
    (hm₂Can : __smtx_map_canonical m₂ = true)
    (hm₁Def : __smtx_map_get_default m₁ = SmtValue.Boolean false)
    (hRight : __smtx_map_lookup m₂ w = SmtValue.Boolean true) :
    __smtx_map_lookup
        (__smtx_set_op_rec false m₁
          (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m₁))
            (SmtValue.Boolean false))
          m₂) w =
      SmtValue.Boolean true := by
  let empty :=
    SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m₁))
      (SmtValue.Boolean false)
  have hEmptyTy :
      __smtx_typeof_map_value empty = SmtType.Map A SmtType.Bool := by
    dsimp [empty]
    simp [__smtx_typeof_map_value, __smtx_index_typeof_map, hm₁Ty,
      __smtx_typeof_value]
  have hUnion :=
    mss_op_lookup_acc false (m1 := m₁) (m2 := empty) (acc := m₂)
      (A := A) (i := w) hm₁Ty hEmptyTy hm₂Ty hm₁Can hm₂Can hm₁Def
  simpa [empty, hRight, native_ite] using hUnion

private theorem set_singleton_lookup_true_key_eq
    {v w : SmtValue} {T : SmtType} :
    __smtx_map_lookup
        (SmtMap.cons v (SmtValue.Boolean true)
          (SmtMap.default T (SmtValue.Boolean false))) w =
      SmtValue.Boolean true ->
    w = v := by
  intro hLookup
  by_cases hVeq : native_veq v w = true
  · exact (eq_of_native_veq_true hVeq).symm
  · have hVeqFalse : native_veq v w = false := by
      cases h : native_veq v w
      · rfl
      · exact False.elim (hVeq h)
    simp [__smtx_map_lookup, hVeqFalse, native_ite] at hLookup

private theorem set_singleton_lookup_false_of_other_singleton
    {v₁ v₂ w : SmtValue} {T₁ T₂ : SmtType} :
    __smtx_map_lookup
        (SmtMap.cons v₁ (SmtValue.Boolean true)
          (SmtMap.default T₁ (SmtValue.Boolean false))) w =
      SmtValue.Boolean true ->
    native_veq v₂ v₁ = false ->
    __smtx_map_lookup
        (SmtMap.cons v₂ (SmtValue.Boolean true)
          (SmtMap.default T₂ (SmtValue.Boolean false))) w =
      SmtValue.Boolean false := by
  intro hLookup hNe
  have hw : w = v₁ :=
    set_singleton_lookup_true_key_eq (T := T₁) hLookup
  subst w
  simp [__smtx_map_lookup, hNe, native_ite]

private theorem set_eval_map_info
    (M : SmtModel) (hM : model_wf M) (t : Term) (A : SmtType) :
    RuleProofs.eo_has_smt_translation t ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Set A ->
    ∃ m,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Set m ∧
      __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool ∧
      __smtx_map_canonical m = true ∧
      __smtx_map_get_default m = SmtValue.Boolean false := by
  intro hTrans hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Set A := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by
          simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation]
            using hTrans)
  rcases set_value_canonical (v := __smtx_model_eval M (__eo_to_smt t))
      (A := A) hEvalTy with
    ⟨m, hEval⟩
  have hMapTy :
      __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool :=
    set_map_value_typed (by simpa [hEval] using hEvalTy)
  have hCanEval :
      value_canonical (__smtx_model_eval M (__eo_to_smt t)) :=
    RuleProofs.model_eval_eo_to_smt_canonical M hM t hTrans
  have hCanSet : value_canonical (SmtValue.Set m) := by
    simpa [hEval] using hCanEval
  have hMapCan : __smtx_map_canonical m = true := by
    have hParts := hCanSet
    simp [value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact hParts.1
  have hDef : __smtx_map_get_default m = SmtValue.Boolean false := by
    have hParts := hCanSet
    simp [value_canonical, __smtx_value_canonical,
      SmtEval.native_and] at hParts
    exact eq_of_native_veq_true hParts.2
  exact ⟨m, hEval, hMapTy, hMapCan, hDef⟩

private theorem set_union_eval_maps
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y) ->
    ∃ A mx my,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Set mx ∧
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Set my ∧
      __smtx_typeof_map_value mx = SmtType.Map A SmtType.Bool ∧
      __smtx_typeof_map_value my = SmtType.Map A SmtType.Bool ∧
      __smtx_map_canonical mx = true ∧
      __smtx_map_canonical my = true ∧
      __smtx_map_get_default mx = SmtValue.Boolean false ∧
      __smtx_map_get_default my = SmtValue.Boolean false ∧
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y)) =
        SmtValue.Set
          (__smtx_set_op_rec false mx
            (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
              (SmtValue.Boolean false))
            my) := by
  intro hTrans
  have hUnionNN :
      __smtx_typeof (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None := by
    exact hTrans
  rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
      (typeof_set_union_eq (__eo_to_smt x) (__eo_to_smt y)) hUnionNN with
    ⟨A, hxTy, hyTy⟩
  have hxTrans : RuleProofs.eo_has_smt_translation x := by
    intro hNone
    rw [hxTy] at hNone
    cases hNone
  have hyTrans : RuleProofs.eo_has_smt_translation y := by
    intro hNone
    rw [hyTy] at hNone
    cases hNone
  rcases set_eval_map_info M hM x A hxTrans hxTy with
    ⟨mx, hxEval, hmxTy, hmxCan, hmxDef⟩
  rcases set_eval_map_info M hM y A hyTrans hyTy with
    ⟨my, hyEval, hmyTy, hmyCan, hmyDef⟩
  refine ⟨A, mx, my, hxEval, hyEval, hmxTy, hmyTy, hmxCan, hmyCan,
    hmxDef, hmyDef, ?_⟩
  change __smtx_model_eval M
      (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y)) =
    SmtValue.Set
      (__smtx_set_op_rec false mx
        (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value mx))
          (SmtValue.Boolean false))
        my)
  rw [smtx_eval_set_union_term_eq]
  simp [__smtx_model_eval_set_union, __smtx_set_union, hxEval, hyEval]

private theorem seq_is_non_empty_shape {t : Term} :
    __seq_is_non_empty t = Term.Boolean true ->
    (∃ e, t = Term.Apply (Term.UOp UserOp.seq_unit) e) ∨
      (∃ e ts,
        t =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.Apply (Term.UOp UserOp.seq_unit) e))
            ts) := by
  intro h
  cases t <;> simp [__seq_is_non_empty] at h
  case Apply f x =>
    cases f <;> try simp at h
    case UOp op =>
      cases op <;> simp at h
      exact Or.inl ⟨x, rfl⟩
    case Apply g y =>
      cases g <;> try simp at h
      case UOp op =>
        cases op <;> try simp at h
        case str_concat =>
          cases y <;> try simp at h
          case Apply u e =>
            cases u <;> try simp at h
            case UOp op =>
              cases op <;> simp at h
              exact Or.inr ⟨e, x, rfl⟩

private theorem native_pack_seq_ne_empty_of_length_pos_any
    (T U : SmtType) {xs : List SmtValue} (hPos : 0 < xs.length) :
    native_pack_seq T xs ≠ SmtSeq.empty U := by
  intro hEq
  have hUnpack := congrArg native_unpack_seq hEq
  have hLenZero : xs.length = 0 := by
    have hLen := congrArg List.length hUnpack
    simpa [Smtm.native_unpack_pack_seq, native_unpack_seq] using hLen
  omega

private theorem seq_is_non_empty_model_eval
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __seq_is_non_empty t = Term.Boolean true ->
    ∃ T xs,
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Seq (native_pack_seq T xs) ∧
      0 < xs.length := by
  intro hTrans hNonEmpty
  rcases seq_is_non_empty_shape hNonEmpty with
    ⟨e, rfl⟩ | ⟨e, ts, rfl⟩
  · let v := __smtx_model_eval M (__eo_to_smt e)
    refine ⟨__smtx_typeof_value v, [v], ?_, by simp⟩
    change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
      SmtValue.Seq (native_pack_seq (__smtx_typeof_value v) [v])
    simp [__smtx_model_eval, v, native_pack_seq]
  · let unit := Term.Apply (Term.UOp UserOp.seq_unit) e
    let v := __smtx_model_eval M (__eo_to_smt e)
    have hUnitEval :
        __smtx_model_eval M (__eo_to_smt unit) =
          SmtValue.Seq (native_pack_seq (__smtx_typeof_value v) [v]) := by
      change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
        SmtValue.Seq (native_pack_seq (__smtx_typeof_value v) [v])
      simp [__smtx_model_eval, v, native_pack_seq]
    have hConcatNN :
        __smtx_typeof (__eo_to_smt (mkConcat unit ts)) ≠ SmtType.None := by
      exact hTrans
    rcases str_concat_args_of_non_none unit ts hConcatNN with
      ⟨T, _hUnitTy, hTsTy⟩
    have hTailTy :=
      smt_model_eval_preserves_type M hM (__eo_to_smt ts) (SmtType.Seq T)
        hTsTy (seq_ne_none T) (type_inhabited_seq T)
    rcases seq_value_canonical hTailTy with ⟨tail, hTailEval⟩
    refine
      ⟨__smtx_typeof_value v, v :: native_unpack_seq tail, ?_, by simp⟩
    rw [smtx_model_eval_str_concat_term_eq, hUnitEval, hTailEval]
    change
      __smtx_model_eval_str_concat
        (SmtValue.Seq (native_pack_seq (__smtx_typeof_value v) [v]))
        (SmtValue.Seq tail) =
      SmtValue.Seq
        (native_pack_seq (__smtx_typeof_value v) (v :: native_unpack_seq tail))
    simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
      native_unpack_seq, __smtx_elem_typeof_seq_value]

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

private theorem smtx_model_eval_eq_false_symm
    {v₁ v₂ : SmtValue} :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false ->
    __smtx_model_eval_eq v₂ v₁ = SmtValue.Boolean false := by
  intro hEq
  by_cases hReg :
      ∃ r₁ r₂, v₁ = SmtValue.RegLan r₁ ∧ v₂ = SmtValue.RegLan r₂
  · rcases hReg with ⟨r₁, r₂, rfl, rfl⟩
    change SmtValue.Boolean (native_re_ext_eq r₂ r₁) = SmtValue.Boolean false
    change SmtValue.Boolean (native_re_ext_eq r₁ r₂) = SmtValue.Boolean false at hEq
    simp at hEq ⊢
    rcases hEq with ⟨s, hs, hNe⟩
    exact ⟨s, hs, fun hEq => hNe hEq.symm⟩
  · cases v₁ <;> cases v₂ <;>
      simp [__smtx_model_eval_eq] at hEq hReg ⊢
    all_goals
      exact native_veq_false_symm hEq

private theorem eval_seq_unit_pack (M : SmtModel) (e : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
      SmtValue.Seq
        (native_pack_seq
          (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
          [__smtx_model_eval M (__eo_to_smt e)]) := by
  change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
    SmtValue.Seq
      (native_pack_seq
        (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
        [__smtx_model_eval M (__eo_to_smt e)])
  simp [__smtx_model_eval, native_pack_seq]

private theorem eval_concat_seq_unit_pack
    (M : SmtModel) (hM : model_wf M) (e tail : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail) ->
    ∃ ss,
      __smtx_model_eval M
          (__eo_to_smt (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)) =
        SmtValue.Seq
          (native_pack_seq
            (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
            (__smtx_model_eval M (__eo_to_smt e) :: native_unpack_seq ss)) := by
  intro hTrans
  let unit := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat unit tail)) ≠ SmtType.None := by
    exact hTrans
  rcases str_concat_args_of_non_none unit tail hConcatNN with
    ⟨T, _hUnitTy, hTailTy⟩
  have hTailValTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt tail) (SmtType.Seq T)
      hTailTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hTailValTy with ⟨ss, hTailEval⟩
  refine ⟨ss, ?_⟩
  rw [smtx_model_eval_str_concat_term_eq, eval_seq_unit_pack, hTailEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
    native_unpack_seq, __smtx_elem_typeof_seq_value]

private theorem eval_concat_seq_unit_pack_with_tail
    (M : SmtModel) (hM : model_wf M) (e tail : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail) ->
    ∃ ss,
      __smtx_model_eval M (__eo_to_smt tail) = SmtValue.Seq ss ∧
        __smtx_elem_typeof_seq_value ss =
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)) ∧
        __smtx_model_eval M
            (__eo_to_smt
              (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)) =
          SmtValue.Seq
            (native_pack_seq
              (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
              (__smtx_model_eval M (__eo_to_smt e) ::
                native_unpack_seq ss)) := by
  intro hTrans
  let unit := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat unit tail)) ≠ SmtType.None := by
    exact hTrans
  rcases str_concat_args_of_non_none unit tail hConcatNN with
    ⟨T, hUnitTy, hTailTy⟩
  have hArgTyInfo :=
    seq_unit_type_eq_arg_of_eq
      (t := __eo_to_smt e) (A := T) (by
        exact hUnitTy)
  have hArgNonNone :
      term_has_non_none_type (__eo_to_smt e) := by
    unfold term_has_non_none_type
    rw [hArgTyInfo.1]
    exact hArgTyInfo.2
  have hHeadValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)) = T :=
    (smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt e)
      hArgNonNone).trans hArgTyInfo.1
  have hTailValTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt tail) (SmtType.Seq T)
      hTailTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hTailValTy with ⟨ss, hTailEval⟩
  have hTailElemTy :
      __smtx_elem_typeof_seq_value ss = T := by
    have hValTy := hTailValTy
    rw [hTailEval] at hValTy
    exact elem_typeof_seq_value_of_typeof_seq_value
      (by simpa [__smtx_typeof_value] using hValTy)
  refine ⟨ss, hTailEval, hTailElemTy.trans hHeadValTy.symm, ?_⟩
  rw [smtx_model_eval_str_concat_term_eq, eval_seq_unit_pack, hTailEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
    native_unpack_seq, __smtx_elem_typeof_seq_value]

private theorem eval_seq_empty_seq
    (M : SmtModel) (U : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))) =
      SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U)) := by
  intro hTrans
  by_cases hU : __eo_to_smt_type U = SmtType.None
  · exfalso
    apply hTrans
    change
      __smtx_typeof
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
        SmtType.None
    rw [TranslationProofs.eo_to_smt_type_seq]
    simp [__smtx_typeof_guard, hU, native_ite, native_Teq,
      __eo_to_smt_seq_empty]
  · change
      __smtx_model_eval M
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U))
    rw [TranslationProofs.eo_to_smt_type_seq]
    simp [__smtx_typeof_guard, hU, native_ite, native_Teq,
      __eo_to_smt_seq_empty, __smtx_model_eval]

private theorem seq_is_non_empty_ne_seq_empty_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (t U : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    __seq_is_non_empty t = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)))) =
      SmtValue.Boolean false := by
  intro htTrans hEmptyTrans hNonEmpty
  rcases seq_is_non_empty_model_eval M hM t htTrans hNonEmpty with
    ⟨T, xs, hEvalT, hPos⟩
  have hEvalEmpty := eval_seq_empty_seq M U hEmptyTrans
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalT, hEvalEmpty] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_ne_empty_of_length_pos_any T
      (__eo_to_smt_type U) hPos hSeqEq
  · rintro ⟨r₁, r₂, hR1, _hR2⟩
    rw [hEvalT] at hR1
    cases hR1

private theorem seq_empty_ne_seq_is_non_empty_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (U t : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    RuleProofs.eo_has_smt_translation t ->
    __seq_is_non_empty t = Term.Boolean true ->
    __smtx_model_eval_eq
      (__smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))))
      (__smtx_model_eval M (__eo_to_smt t)) =
      SmtValue.Boolean false := by
  intro hEmptyTrans htTrans hNonEmpty
  rcases seq_is_non_empty_model_eval M hM t htTrans hNonEmpty with
    ⟨T, xs, hEvalT, hPos⟩
  have hEvalEmpty := eval_seq_empty_seq M U hEmptyTrans
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalT, hEvalEmpty] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_ne_empty_of_length_pos_any T
      (__eo_to_smt_type U) hPos hSeqEq.symm
  · rintro ⟨r₁, r₂, hR1, _hR2⟩
    rw [hEvalEmpty] at hR1
    cases hR1

private theorem seq_distinct_terms_right_empty_non_empty
    {t U T : Term} :
    __seq_distinct_terms t
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) T =
      Term.Boolean true ->
    __seq_is_non_empty t = Term.Boolean true := by
  intro hDistinct
  change __seq_distinct_terms t
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) T =
      Term.Boolean true at hDistinct
  cases T <;> cases t <;> simp [__seq_distinct_terms] at hDistinct ⊢
  all_goals exact hDistinct

private theorem seq_distinct_terms_left_empty_non_empty
    {U t T : Term} :
    __seq_distinct_terms
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) t T =
      Term.Boolean true ->
    __seq_is_non_empty t = Term.Boolean true := by
  intro hDistinct
  change __seq_distinct_terms
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) t T =
      Term.Boolean true at hDistinct
  cases t <;> try
    (cases T <;> simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
     all_goals exact hDistinct)
  case UOp1 op arg =>
    cases op
    case seq_empty =>
      cases arg <;> try
        (cases T <;> simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
         all_goals exact hDistinct)
      case Apply f x =>
        cases f <;> try
          (cases T <;> simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
           all_goals exact hDistinct)
        case UOp fop =>
          cases fop <;>
            cases T <;>
              simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
          all_goals exact hDistinct
    all_goals
      cases T <;> simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
      all_goals exact hDistinct

private theorem seq_distinct_terms_right_empty_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (t U T : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    __seq_distinct_terms t
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) T =
      Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)))) =
      SmtValue.Boolean false := by
  intro htTrans hEmptyTrans hDistinct
  exact seq_is_non_empty_ne_seq_empty_model_eval_eq_false
    M hM t U htTrans hEmptyTrans
    (seq_distinct_terms_right_empty_non_empty hDistinct)

private theorem seq_distinct_terms_left_empty_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (U t T : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    RuleProofs.eo_has_smt_translation t ->
    __seq_distinct_terms
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) t T =
      Term.Boolean true ->
    __smtx_model_eval_eq
      (__smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))))
      (__smtx_model_eval M (__eo_to_smt t)) =
      SmtValue.Boolean false := by
  intro hEmptyTrans htTrans hDistinct
  exact seq_empty_ne_seq_is_non_empty_model_eval_eq_false
    M hM U t hEmptyTrans htTrans
    (seq_distinct_terms_left_empty_non_empty hDistinct)

private theorem are_distinct_terms_type_seq_true_seq_distinct
    {a b U : Term} :
    U ≠ Term.UOp UserOp.Char ->
    __are_distinct_terms_type a b
        (Term.Apply (Term.UOp UserOp.Seq) U) =
      Term.Boolean true ->
    __seq_distinct_terms a b U = Term.Boolean true := by
  intro hU hDistinct
  by_cases ha : a = Term.Stuck
  · subst a
    simp [__are_distinct_terms_type.eq_def] at hDistinct
  by_cases hb : b = Term.Stuck
  · subst b
    simp [__are_distinct_terms_type.eq_def] at hDistinct
  have hSeq :
      __are_distinct_terms_type a b
          (Term.Apply (Term.UOp UserOp.Seq) U) =
        __seq_distinct_terms a b U := by
    rw [__are_distinct_terms_type.eq_def]
    split <;> simp_all
  rwa [hSeq] at hDistinct

private theorem are_distinct_terms_type_set_true_not_subset
    {a b U : Term} :
    __are_distinct_terms_type a b
        (Term.Apply (Term.UOp UserOp.Set) U) =
      Term.Boolean true ->
    __set_is_not_subset a b U = Term.Boolean true ∨
      __set_is_not_subset b a U = Term.Boolean true := by
  intro hDistinct
  have hOr :
      __eo_or (__set_is_not_subset a b U)
          (__set_is_not_subset b a U) =
        Term.Boolean true := by
    by_cases ha : a = Term.Stuck
    · subst a
      simp [__are_distinct_terms_type.eq_def] at hDistinct
    by_cases hb : b = Term.Stuck
    · subst b
      simp [__are_distinct_terms_type.eq_def] at hDistinct
    have hSet :
        __are_distinct_terms_type a b
            (Term.Apply (Term.UOp UserOp.Set) U) =
          __eo_or (__set_is_not_subset a b U)
            (__set_is_not_subset b a U) := by
      rw [__are_distinct_terms_type.eq_def]
      split <;> simp_all
    rwa [hSet] at hDistinct
  exact eo_or_true hOr

private theorem native_pack_seq_ne_of_length_ne
    (T U : SmtType) {xs ys : List SmtValue}
    (hLen : xs.length ≠ ys.length) :
    native_pack_seq T xs ≠ native_pack_seq U ys := by
  intro hEq
  have hUnpack := congrArg native_unpack_seq hEq
  have hLenEq := congrArg List.length hUnpack
  apply hLen
  simpa [Smtm.native_unpack_pack_seq] using hLenEq

private theorem native_pack_seq_cons_ne_of_head_ne
    (T U : SmtType) {x y : SmtValue} {xs ys : List SmtValue}
    (hHead : x ≠ y) :
    native_pack_seq T (x :: xs) ≠ native_pack_seq U (y :: ys) := by
  intro hEq
  change SmtSeq.cons x (native_pack_seq T xs) =
    SmtSeq.cons y (native_pack_seq U ys) at hEq
  injection hEq with hxy _
  exact hHead hxy

private theorem seq_unit_seq_unit_model_eval_eq_false_of_head
    (M : SmtModel) (e₁ e₂ : Term) :
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hHeadNe : v₁ ≠ v₂ := by
    simpa [v₁, v₂] using smt_eval_eq_false_implies_ne hHeadEqFalse
  have hEval₁ := eval_seq_unit_pack M e₁
  have hEval₂ := eval_seq_unit_pack M e₂
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEval₁, hEval₂] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_cons_ne_of_head_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (x := v₁) (y := v₂) (xs := []) (ys := []) hHeadNe hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEval₁] at hReg₁
    cases hReg₁

private theorem concat_seq_unit_concat_seq_unit_model_eval_eq_false_of_head
    (M : SmtModel) (hM : model_wf M)
    (e₁ tail₁ e₂ tail₂ : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁) ->
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hRightTrans hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hHeadNe : v₁ ≠ v₂ := by
    simpa [v₁, v₂] using smt_eval_eq_false_implies_ne hHeadEqFalse
  rcases eval_concat_seq_unit_pack M hM e₁ tail₁ hLeftTrans with
    ⟨ss₁, hEval₁⟩
  rcases eval_concat_seq_unit_pack M hM e₂ tail₂ hRightTrans with
    ⟨ss₂, hEval₂⟩
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEval₁, hEval₂] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_cons_ne_of_head_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (x := v₁) (y := v₂)
      (xs := native_unpack_seq ss₁) (ys := native_unpack_seq ss₂)
      hHeadNe hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEval₁] at hReg₁
    cases hReg₁

private theorem concat_seq_unit_seq_unit_model_eval_eq_false_of_head
    (M : SmtModel) (hM : model_wf M)
    (e₁ tail e₂ : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hHeadNe : v₁ ≠ v₂ := by
    simpa [v₁, v₂] using smt_eval_eq_false_implies_ne hHeadEqFalse
  rcases eval_concat_seq_unit_pack M hM e₁ tail hLeftTrans with
    ⟨ss, hEvalLeft⟩
  have hEvalRight := eval_seq_unit_pack M e₂
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalLeft, hEvalRight] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_cons_ne_of_head_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (x := v₁) (y := v₂) (xs := native_unpack_seq ss) (ys := [])
      hHeadNe hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEvalLeft] at hReg₁
    cases hReg₁

private theorem seq_unit_concat_seq_unit_model_eval_eq_false_of_head
    (M : SmtModel) (hM : model_wf M)
    (e₁ e₂ tail : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail))) =
      SmtValue.Boolean false := by
  intro hRightTrans hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hHeadNe : v₁ ≠ v₂ := by
    simpa [v₁, v₂] using smt_eval_eq_false_implies_ne hHeadEqFalse
  have hEvalLeft := eval_seq_unit_pack M e₁
  rcases eval_concat_seq_unit_pack M hM e₂ tail hRightTrans with
    ⟨ss, hEvalRight⟩
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalLeft, hEvalRight] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_cons_ne_of_head_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (x := v₁) (y := v₂) (xs := []) (ys := native_unpack_seq ss)
      hHeadNe hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEvalLeft] at hReg₁
    cases hReg₁

private theorem seq_unit_arg_translation_of_translation (e : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.seq_unit) e) ->
    RuleProofs.eo_has_smt_translation e := by
  intro hTrans hArgNone
  apply hTrans
  change __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt e)) = SmtType.None
  simp [__smtx_typeof, __smtx_typeof_guard_wf, __smtx_type_wf,
    __smtx_type_wf_component, __smtx_type_wf_rec, native_inhabited_type,
    __smtx_type_default, native_and, native_ite,
    hArgNone]

private theorem set_singleton_arg_translation_of_translation (e : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.set_singleton) e) ->
    RuleProofs.eo_has_smt_translation e := by
  intro hTrans hArgNone
  apply hTrans
  change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt e)) = SmtType.None
  simp [__smtx_typeof, __smtx_typeof_guard_wf, __smtx_type_wf,
    __smtx_type_wf_component, __smtx_type_wf_rec, native_inhabited_type,
    __smtx_type_default, native_and, native_ite,
    hArgNone]

private theorem set_union_arg_translations_of_translation (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y) ->
    RuleProofs.eo_has_smt_translation x ∧
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  have hUnionNN :
      __smtx_typeof (SmtTerm.set_union (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None := by
    exact hTrans
  rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
      (typeof_set_union_eq (__eo_to_smt x) (__eo_to_smt y)) hUnionNN with
    ⟨T, hxTy, hyTy⟩
  constructor
  · intro hNone
    rw [hxTy] at hNone
    cases hNone
  · intro hNone
    rw [hyTy] at hNone
    cases hNone

private theorem set_is_not_subset_not_true_of_not_shapes {a b U : Term} :
    (¬ ∃ e V,
      a = Term.Apply (Term.UOp UserOp.set_singleton) e ∧
      b = Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) V)) ->
    (¬ ∃ e₁ e₂,
      a = Term.Apply (Term.UOp UserOp.set_singleton) e₁ ∧
      b = Term.Apply (Term.UOp UserOp.set_singleton) e₂) ->
    (¬ ∃ e₁ e₂ ss,
      a = Term.Apply (Term.UOp UserOp.set_singleton) e₁ ∧
      b =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.set_union)
            (Term.Apply (Term.UOp UserOp.set_singleton) e₂)) ss) ->
    (¬ ∃ e₁ ts,
      a =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.set_union)
            (Term.Apply (Term.UOp UserOp.set_singleton) e₁)) ts) ->
    __set_is_not_subset a b U ≠ Term.Boolean true := by
  intro hSingletonEmpty hSingletonSingleton hSingletonUnion hUnionLeft hNotSubset
  rw [__set_is_not_subset.eq_def] at hNotSubset
  split at hNotSubset <;> try cases hNotSubset
  all_goals
    first
    | exact hSingletonEmpty ⟨_, _, rfl, rfl⟩
    | exact hSingletonSingleton ⟨_, _, rfl, rfl⟩
    | exact hSingletonUnion ⟨_, _, _, rfl, rfl⟩
    | exact hUnionLeft ⟨_, _, rfl⟩

private theorem set_is_not_subset_union_left_true_branch
    {e ts s U : Term} :
    __set_is_not_subset
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.set_union)
            (Term.Apply (Term.UOp UserOp.set_singleton) e)) ts) s U =
      Term.Boolean true ->
    __eo_ite
        (__set_is_not_subset (Term.Apply (Term.UOp UserOp.set_singleton) e) s U)
        (Term.Boolean true) (__set_is_not_subset ts s U) =
      Term.Boolean true := by
  intro hNotSubset
  cases U <;> cases s <;>
    simp [__set_is_not_subset] at hNotSubset ⊢
  all_goals exact hNotSubset

private theorem set_is_not_subset_lookup_witness
    (M : SmtModel) (hM : model_wf M) (a b U : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (∀ e₁ e₂,
      sizeOf e₁ + sizeOf e₂ < sizeOf a + sizeOf b ->
      RuleProofs.eo_has_smt_translation e₁ ->
      RuleProofs.eo_has_smt_translation e₂ ->
      __eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __set_is_not_subset a b U = Term.Boolean true ->
    ∃ m₁ m₂ w,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Set m₁ ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Set m₂ ∧
      __smtx_map_lookup m₁ w = SmtValue.Boolean true ∧
      __smtx_map_lookup m₂ w = SmtValue.Boolean false := by
  intro haTrans hbTrans hHeadSound hNotSubset
  by_cases hSingletonEmpty :
      ∃ e V,
        a = Term.Apply (Term.UOp UserOp.set_singleton) e ∧
        b = Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) V)
  · rcases hSingletonEmpty with ⟨e, V, rfl, rfl⟩
    exact set_singleton_set_empty_lookup_witness M e V hbTrans
  · by_cases hSingletonSingleton :
      ∃ e₁ e₂,
        a = Term.Apply (Term.UOp UserOp.set_singleton) e₁ ∧
        b = Term.Apply (Term.UOp UserOp.set_singleton) e₂
    · rcases hSingletonSingleton with ⟨e₁, e₂, rfl, rfl⟩
      have hBranch :
          __eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
              (__are_distinct_terms_type e₁ e₂ U) =
            Term.Boolean true := by
        change __set_is_not_subset
            (Term.Apply (Term.UOp UserOp.set_singleton) e₁)
            (Term.Apply (Term.UOp UserOp.set_singleton) e₂) U =
          Term.Boolean true at hNotSubset
        cases U <;>
          (rw [__set_is_not_subset.eq_def] at hNotSubset
           simp only at hNotSubset)
        all_goals first | exact hNotSubset | cases hNotSubset
      rcases eo_ite_eq_false_guard_true hBranch with
        ⟨hHeadEqFalse, hHeadDistinct⟩
      have he₁Trans :
          RuleProofs.eo_has_smt_translation e₁ :=
        set_singleton_arg_translation_of_translation e₁ haTrans
      have he₂Trans :
          RuleProofs.eo_has_smt_translation e₂ :=
        set_singleton_arg_translation_of_translation e₂ hbTrans
      exact set_singleton_set_singleton_lookup_witness_of_head M e₁ e₂
        (hHeadSound e₁ e₂ (by simp; omega) he₁Trans he₂Trans
          hHeadEqFalse hHeadDistinct)
    · by_cases hSingletonUnion :
        ∃ e₁ e₂ ss,
          a = Term.Apply (Term.UOp UserOp.set_singleton) e₁ ∧
          b =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.set_union)
                (Term.Apply (Term.UOp UserOp.set_singleton) e₂)) ss
      · rcases hSingletonUnion with ⟨e₁, e₂, ss, rfl, rfl⟩
        let head₂ := Term.Apply (Term.UOp UserOp.set_singleton) e₂
        have hBranch :
            __eo_ite
                (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
                  (__are_distinct_terms_type e₁ e₂ U))
                (__set_is_not_subset
                  (Term.Apply (Term.UOp UserOp.set_singleton) e₁) ss U)
                (Term.Boolean false) =
              Term.Boolean true := by
          change __set_is_not_subset
              (Term.Apply (Term.UOp UserOp.set_singleton) e₁)
              (Term.Apply (Term.Apply (Term.UOp UserOp.set_union)
                (Term.Apply (Term.UOp UserOp.set_singleton) e₂)) ss) U =
            Term.Boolean true at hNotSubset
          cases U <;>
            (rw [__set_is_not_subset.eq_def] at hNotSubset
             simp only at hNotSubset)
          all_goals first | exact hNotSubset | cases hNotSubset
        rcases eo_ite_eq_true_cases
            (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
              (__are_distinct_terms_type e₁ e₂ U))
            (__set_is_not_subset
              (Term.Apply (Term.UOp UserOp.set_singleton) e₁) ss U)
            (Term.Boolean false) hBranch with
          ⟨hHeadGuard, hRecNotSubset⟩ | ⟨_, hFalse⟩
        · rcases eo_ite_eq_false_guard_true hHeadGuard with
            ⟨hHeadEqFalse, hHeadDistinct⟩
          have hUnionArgs :=
            set_union_arg_translations_of_translation head₂ ss hbTrans
          have hssTrans :
              RuleProofs.eo_has_smt_translation ss := hUnionArgs.2
          have he₁Trans :
              RuleProofs.eo_has_smt_translation e₁ :=
            set_singleton_arg_translation_of_translation e₁ haTrans
          have he₂Trans :
              RuleProofs.eo_has_smt_translation e₂ :=
            set_singleton_arg_translation_of_translation e₂ hUnionArgs.1
          have hHeadEqFalseEval :=
            hHeadSound e₁ e₂ (by simp; omega) he₁Trans he₂Trans
              hHeadEqFalse hHeadDistinct
          have hRecMeasure :
              sizeOf (Term.Apply (Term.UOp UserOp.set_singleton) e₁) +
                  sizeOf ss <
                sizeOf (Term.Apply (Term.UOp UserOp.set_singleton) e₁) +
                  sizeOf
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.set_union) head₂) ss) := by
            simp [head₂]
            omega
          rcases set_is_not_subset_lookup_witness
              M hM (Term.Apply (Term.UOp UserOp.set_singleton) e₁) ss U
              haTrans hssTrans
              (fun x y hSmall hxTrans hyTrans hEqFalse hDistinct =>
                hHeadSound x y (Nat.lt_trans hSmall hRecMeasure)
                  hxTrans hyTrans hEqFalse hDistinct)
              hRecNotSubset with
            ⟨mSing, mSs, w, hEvalSing, hEvalSs, hLookupSing, hLookupSs⟩
          rcases set_union_eval_maps M hM head₂ ss hbTrans with
            ⟨A, mHead₂, mSs', hEvalHead₂, hEvalSs', hHead₂Ty, hSsTy,
              hHead₂Can, hSsCan, hHead₂Def, _hSsDef, hEvalUnion⟩
          have hmSs' : mSs' = mSs := by
            rw [hEvalSs] at hEvalSs'
            injection hEvalSs' with h
            exact h.symm
          subst mSs'
          let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
          let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
          have hmSing :
              mSing =
                SmtMap.cons v₁ (SmtValue.Boolean true)
                  (SmtMap.default (__smtx_typeof_value v₁)
                    (SmtValue.Boolean false)) := by
            have hActual :
                __smtx_model_eval M
                    (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₁)) =
                  SmtValue.Set
                    (SmtMap.cons v₁ (SmtValue.Boolean true)
                      (SmtMap.default (__smtx_typeof_value v₁)
                        (SmtValue.Boolean false))) := by
              change __smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e₁)) =
                SmtValue.Set
                  (SmtMap.cons v₁ (SmtValue.Boolean true)
                    (SmtMap.default (__smtx_typeof_value v₁)
                      (SmtValue.Boolean false)))
              rw [smtx_eval_set_singleton_term_eq]
              rfl
            rw [hEvalSing] at hActual
            injection hActual with h
          subst mSing
          have hmHead₂ :
              mHead₂ =
                SmtMap.cons v₂ (SmtValue.Boolean true)
                  (SmtMap.default (__smtx_typeof_value v₂)
                    (SmtValue.Boolean false)) := by
            have hActual :
                __smtx_model_eval M (__eo_to_smt head₂) =
                  SmtValue.Set
                    (SmtMap.cons v₂ (SmtValue.Boolean true)
                      (SmtMap.default (__smtx_typeof_value v₂)
                        (SmtValue.Boolean false))) := by
              change __smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e₂)) =
                SmtValue.Set
                  (SmtMap.cons v₂ (SmtValue.Boolean true)
                    (SmtMap.default (__smtx_typeof_value v₂)
                      (SmtValue.Boolean false)))
              rw [smtx_eval_set_singleton_term_eq]
              rfl
            rw [hEvalHead₂] at hActual
            injection hActual with h
          subst mHead₂
          have hVeq : native_veq v₂ v₁ = false :=
            native_veq_false_symm
              (RuleProofs.native_veq_false_of_model_eval_eq_false
                (v1 := v₁) (v2 := v₂) hHeadEqFalseEval)
          have hHeadLookupFalse :
              __smtx_map_lookup
                  (SmtMap.cons v₂ (SmtValue.Boolean true)
                    (SmtMap.default (__smtx_typeof_value v₂)
                      (SmtValue.Boolean false))) w =
                SmtValue.Boolean false :=
            set_singleton_lookup_false_of_other_singleton
              (T₁ := __smtx_typeof_value v₁)
              (T₂ := __smtx_typeof_value v₂) hLookupSing hVeq
          have hUnionLookupFalse :
              __smtx_map_lookup
                  (__smtx_set_op_rec false
                    (SmtMap.cons v₂ (SmtValue.Boolean true)
                      (SmtMap.default (__smtx_typeof_value v₂)
                        (SmtValue.Boolean false)))
                    (SmtMap.default
                      (__smtx_index_typeof_map
                        (__smtx_typeof_map_value
                          (SmtMap.cons v₂ (SmtValue.Boolean true)
                            (SmtMap.default (__smtx_typeof_value v₂)
                              (SmtValue.Boolean false)))))
                      (SmtValue.Boolean false))
                    mSs) w =
                SmtValue.Boolean false :=
            set_union_lookup_false_of_both_false hHead₂Ty hSsTy
              hHead₂Can hSsCan hHead₂Def hHeadLookupFalse hLookupSs
          exact ⟨SmtMap.cons v₁ (SmtValue.Boolean true)
              (SmtMap.default (__smtx_typeof_value v₁) (SmtValue.Boolean false)),
            __smtx_set_op_rec false
              (SmtMap.cons v₂ (SmtValue.Boolean true)
                (SmtMap.default (__smtx_typeof_value v₂) (SmtValue.Boolean false)))
              (SmtMap.default
                (__smtx_index_typeof_map
                  (__smtx_typeof_map_value
                    (SmtMap.cons v₂ (SmtValue.Boolean true)
                      (SmtMap.default (__smtx_typeof_value v₂)
                        (SmtValue.Boolean false)))))
                (SmtValue.Boolean false))
              mSs,
            w, hEvalSing, hEvalUnion, hLookupSing, hUnionLookupFalse⟩
        · cases hFalse
      · by_cases hUnionLeft :
          ∃ e₁ ts,
            a =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.set_union)
                  (Term.Apply (Term.UOp UserOp.set_singleton) e₁)) ts
        · rcases hUnionLeft with ⟨e₁, ts, rfl⟩
          let head₁ := Term.Apply (Term.UOp UserOp.set_singleton) e₁
          have hBranch :
              __eo_ite (__set_is_not_subset head₁ b U)
                  (Term.Boolean true) (__set_is_not_subset ts b U) =
                Term.Boolean true :=
            set_is_not_subset_union_left_true_branch hNotSubset
          have hUnionArgs :=
            set_union_arg_translations_of_translation head₁ ts haTrans
          have htsTrans :
              RuleProofs.eo_has_smt_translation ts := hUnionArgs.2
          rcases set_union_eval_maps M hM head₁ ts haTrans with
            ⟨A, mHead₁, mTs, hEvalHead₁, hEvalTs, hHead₁Ty, hTsTy,
              hHead₁Can, hTsCan, hHead₁Def, _hTsDef, hEvalUnion⟩
          rcases eo_ite_eq_true_cases (__set_is_not_subset head₁ b U)
              (Term.Boolean true) (__set_is_not_subset ts b U) hBranch with
            ⟨hHeadNotSubset, _⟩ | ⟨_, hTailNotSubset⟩
          · have hHeadMeasure :
                sizeOf head₁ + sizeOf b <
                  sizeOf (Term.Apply
                    (Term.Apply (Term.UOp UserOp.set_union) head₁) ts) +
                    sizeOf b := by
              simp [head₁]
              omega
            rcases set_is_not_subset_lookup_witness
                M hM head₁ b U hUnionArgs.1 hbTrans
                (fun x y hSmall hxTrans hyTrans hEqFalse hDistinct =>
                  hHeadSound x y (Nat.lt_trans hSmall hHeadMeasure)
                    hxTrans hyTrans hEqFalse hDistinct)
                hHeadNotSubset with
              ⟨mHeadRec, mS, w, hEvalHeadRec, hEvalS, hLookupHead, hLookupS⟩
            have hmHead : mHead₁ = mHeadRec := by
              rw [hEvalHeadRec] at hEvalHead₁
              injection hEvalHead₁ with h
              exact h.symm
            subst mHead₁
            have hUnionLookupTrue :
                __smtx_map_lookup
                    (__smtx_set_op_rec false mHeadRec
                      (SmtMap.default
                        (__smtx_index_typeof_map (__smtx_typeof_map_value mHeadRec))
                        (SmtValue.Boolean false))
                      mTs) w =
                  SmtValue.Boolean true :=
              set_union_lookup_true_of_left_true hHead₁Ty hTsTy
                hHead₁Can hTsCan hHead₁Def hLookupHead
            exact ⟨__smtx_set_op_rec false mHeadRec
                (SmtMap.default
                  (__smtx_index_typeof_map (__smtx_typeof_map_value mHeadRec))
                  (SmtValue.Boolean false))
                mTs,
              mS, w, hEvalUnion, hEvalS, hUnionLookupTrue, hLookupS⟩
          · have hTailMeasure :
                sizeOf ts + sizeOf b <
                  sizeOf (Term.Apply
                    (Term.Apply (Term.UOp UserOp.set_union) head₁) ts) +
                    sizeOf b := by
              simp [head₁]
              omega
            rcases set_is_not_subset_lookup_witness
                M hM ts b U htsTrans hbTrans
                (fun x y hSmall hxTrans hyTrans hEqFalse hDistinct =>
                  hHeadSound x y (Nat.lt_trans hSmall hTailMeasure)
                    hxTrans hyTrans hEqFalse hDistinct)
                hTailNotSubset with
              ⟨mTsRec, mS, w, hEvalTsRec, hEvalS, hLookupTs, hLookupS⟩
            have hmTs : mTs = mTsRec := by
              rw [hEvalTsRec] at hEvalTs
              injection hEvalTs with h
              exact h.symm
            subst mTs
            have hUnionLookupTrue :
                __smtx_map_lookup
                    (__smtx_set_op_rec false mHead₁
                      (SmtMap.default
                        (__smtx_index_typeof_map (__smtx_typeof_map_value mHead₁))
                        (SmtValue.Boolean false))
                      mTsRec) w =
                  SmtValue.Boolean true :=
              set_union_lookup_true_of_right_true hHead₁Ty hTsTy
                hHead₁Can hTsCan hHead₁Def hLookupTs
            exact ⟨__smtx_set_op_rec false mHead₁
                (SmtMap.default
                  (__smtx_index_typeof_map (__smtx_typeof_map_value mHead₁))
                  (SmtValue.Boolean false))
                mTsRec,
              mS, w, hEvalUnion, hEvalS, hUnionLookupTrue, hLookupS⟩
        · exact False.elim
            (set_is_not_subset_not_true_of_not_shapes hSingletonEmpty
              hSingletonSingleton hSingletonUnion hUnionLeft hNotSubset)
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals try assumption
  all_goals simp_all
  all_goals omega

private theorem set_is_not_subset_model_eval_eq_false_of_head_sound
    (M : SmtModel) (hM : model_wf M) (a b U : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (∀ e₁ e₂,
      sizeOf e₁ + sizeOf e₂ < sizeOf a + sizeOf b ->
      RuleProofs.eo_has_smt_translation e₁ ->
      RuleProofs.eo_has_smt_translation e₂ ->
      __eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __set_is_not_subset a b U = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans hHeadSound hNotSubset
  exact set_value_model_eval_eq_false_of_lookup_witness
    (set_is_not_subset_lookup_witness M hM a b U
      haTrans hbTrans hHeadSound hNotSubset)

private theorem set_is_not_subset_model_eval_eq_false_of_head_sound_symm
    (M : SmtModel) (hM : model_wf M) (a b U : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (∀ e₁ e₂,
      sizeOf e₁ + sizeOf e₂ < sizeOf a + sizeOf b ->
      RuleProofs.eo_has_smt_translation e₁ ->
      RuleProofs.eo_has_smt_translation e₂ ->
      __eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __set_is_not_subset b a U = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans hHeadSound hNotSubset
  exact smtx_model_eval_eq_false_symm
    (set_is_not_subset_model_eval_eq_false_of_head_sound
      M hM b a U hbTrans haTrans
      (fun x y hSmall hxTrans hyTrans hEqFalse hDistinct =>
        hHeadSound x y (by omega) hxTrans hyTrans hEqFalse hDistinct)
      hNotSubset)

private theorem str_concat_arg_translations_of_translation (x y : Term) :
    RuleProofs.eo_has_smt_translation (mkConcat x y) ->
    RuleProofs.eo_has_smt_translation x ∧
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases str_concat_args_of_non_none x y hTrans with ⟨T, hxTy, hyTy⟩
  constructor
  · intro hNone
    rw [hxTy] at hNone
    exact seq_ne_none T hNone
  · intro hNone
    rw [hyTy] at hNone
    exact seq_ne_none T hNone

private theorem concat_seq_unit_seq_unit_model_eval_eq_false_of_tail
    (M : SmtModel) (hM : model_wf M)
    (e₁ tail e₂ : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail) ->
    __seq_is_non_empty tail = Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hTailNonEmpty
  have hTailTrans :
      RuleProofs.eo_has_smt_translation tail :=
    (str_concat_arg_translations_of_translation
      (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail hLeftTrans).2
  rcases seq_is_non_empty_model_eval M hM tail hTailTrans hTailNonEmpty with
    ⟨T, xs, hTailEval, hPos⟩
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hEvalLeft :
      __smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_typeof_value v₁) (v₁ :: xs)) := by
    rw [smtx_model_eval_str_concat_term_eq, eval_seq_unit_pack, hTailEval]
    simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
      native_unpack_seq, Smtm.native_unpack_pack_seq,
      __smtx_elem_typeof_seq_value, v₁]
  have hEvalRight := eval_seq_unit_pack M e₂
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalLeft, hEvalRight] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_ne_of_length_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (xs := v₁ :: xs) (ys := [v₂]) (by
        intro hLen
        have hLeftGt : 1 < (v₁ :: xs).length := by
          simpa using Nat.succ_lt_succ hPos
        have hBad : 1 < [v₂].length := by
          rwa [← hLen]
        simp at hBad) hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEvalLeft] at hReg₁
    cases hReg₁

private theorem seq_unit_concat_seq_unit_model_eval_eq_false_of_tail
    (M : SmtModel) (hM : model_wf M)
    (e₁ e₂ tail : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) ->
    __seq_is_non_empty tail = Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail))) =
      SmtValue.Boolean false := by
  intro hRightTrans hTailNonEmpty
  have hTailTrans :
      RuleProofs.eo_has_smt_translation tail :=
    (str_concat_arg_translations_of_translation
      (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail hRightTrans).2
  rcases seq_is_non_empty_model_eval M hM tail hTailTrans hTailNonEmpty with
    ⟨T, xs, hTailEval, hPos⟩
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hEvalLeft := eval_seq_unit_pack M e₁
  have hEvalRight :
      __smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_typeof_value v₂) (v₂ :: xs)) := by
    rw [smtx_model_eval_str_concat_term_eq, eval_seq_unit_pack, hTailEval]
    simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
      native_unpack_seq, Smtm.native_unpack_pack_seq,
      __smtx_elem_typeof_seq_value, v₂]
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalLeft, hEvalRight] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_ne_of_length_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (xs := [v₁]) (ys := v₂ :: xs) (by
        intro hLen
        have hRightGt : 1 < (v₂ :: xs).length := by
          simpa using Nat.succ_lt_succ hPos
        have hBad : 1 < [v₁].length := by
          rwa [hLen]
        simp at hBad) hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEvalLeft] at hReg₁
    cases hReg₁

private theorem concat_seq_unit_concat_seq_unit_model_eval_eq_false_of_tail
    (M : SmtModel) (hM : model_wf M)
    (e₁ tail₁ e₂ tail₂ : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁) ->
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt tail₁))
        (__smtx_model_eval M (__eo_to_smt tail₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hRightTrans hTailEqFalse
  rcases eval_concat_seq_unit_pack_with_tail M hM e₁ tail₁ hLeftTrans with
    ⟨ss₁, hTailEval₁, hElem₁, hEval₁⟩
  rcases eval_concat_seq_unit_pack_with_tail M hM e₂ tail₂ hRightTrans with
    ⟨ss₂, hTailEval₂, hElem₂, hEval₂⟩
  have hTailNe : SmtValue.Seq ss₁ ≠ SmtValue.Seq ss₂ := by
    have hNe :=
      smt_eval_eq_false_implies_ne hTailEqFalse
    intro hEq
    apply hNe
    rw [hTailEval₁, hTailEval₂]
    exact hEq
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEval₁, hEval₂] at hEq
    injection hEq with hSeqEq
    change SmtSeq.cons v₁
        (native_pack_seq (__smtx_typeof_value v₁) (native_unpack_seq ss₁)) =
      SmtSeq.cons v₂
        (native_pack_seq (__smtx_typeof_value v₂) (native_unpack_seq ss₂)) at hSeqEq
    injection hSeqEq with _hHead hTailPackEq
    apply hTailNe
    have hTailEq : ss₁ = ss₂ := by
      calc
        ss₁ =
            native_pack_seq (__smtx_typeof_value v₁)
              (native_unpack_seq ss₁) := by
              rw [← hElem₁]
              exact (native_pack_unpack_seq ss₁).symm
        _ =
            native_pack_seq (__smtx_typeof_value v₂)
              (native_unpack_seq ss₂) := hTailPackEq
        _ = ss₂ := by
              rw [← hElem₂]
              exact native_pack_unpack_seq ss₂
    rw [hTailEq]
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEval₁] at hReg₁
    cases hReg₁

private theorem seq_distinct_seq_unit_seq_unit_model_eval_eq_false
    (M : SmtModel) (e₁ e₂ U : Term) :
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms (Term.Apply (Term.UOp UserOp.seq_unit) e₁)
        (Term.Apply (Term.UOp UserOp.seq_unit) e₂) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hHeadSound hDistinct
  have hBranch :
      __eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
          (__are_distinct_terms_type e₁ e₂ U) =
        Term.Boolean true := by
    change __seq_distinct_terms
        (Term.Apply (Term.UOp UserOp.seq_unit) e₁)
        (Term.Apply (Term.UOp UserOp.seq_unit) e₂) U =
      Term.Boolean true at hDistinct
    cases U <;>
      (rw [__seq_distinct_terms.eq_def] at hDistinct
       simp only at hDistinct)
    all_goals first | exact hDistinct | cases hDistinct
  rcases eo_ite_eq_false_guard_true hBranch with
    ⟨hHeadEqFalse, hHeadDistinct⟩
  exact seq_unit_seq_unit_model_eval_eq_false_of_head M e₁ e₂
    (hHeadSound hHeadEqFalse hHeadDistinct)

private theorem seq_distinct_concat_unit_concat_unit_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M)
    (e₁ tail₁ e₂ tail₂ U : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁) ->
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) ->
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    (__seq_distinct_terms tail₁ tail₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt tail₁))
          (__smtx_model_eval M (__eo_to_smt tail₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁)
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hRightTrans hHeadSound hTailSound hDistinct
  have hBranch :
      __eo_ite
          (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
            (__are_distinct_terms_type e₁ e₂ U))
          (Term.Boolean true) (__seq_distinct_terms tail₁ tail₂ U) =
        Term.Boolean true := by
    change __seq_distinct_terms
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e₁)) tail₁)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e₂)) tail₂) U =
      Term.Boolean true at hDistinct
    cases U <;>
      (rw [__seq_distinct_terms.eq_def] at hDistinct
       simp only at hDistinct)
    all_goals first | exact hDistinct | cases hDistinct
  rcases eo_ite_eq_true_cases
      (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
        (__are_distinct_terms_type e₁ e₂ U))
      (Term.Boolean true) (__seq_distinct_terms tail₁ tail₂ U) hBranch with
    ⟨hHeadGuard, _⟩ | ⟨_hHeadGuardFalse, hTailDistinct⟩
  · rcases eo_ite_eq_false_guard_true hHeadGuard with
      ⟨hHeadEqFalse, hHeadDistinct⟩
    exact concat_seq_unit_concat_seq_unit_model_eval_eq_false_of_head
      M hM e₁ tail₁ e₂ tail₂ hLeftTrans hRightTrans
      (hHeadSound hHeadEqFalse hHeadDistinct)
  · exact concat_seq_unit_concat_seq_unit_model_eval_eq_false_of_tail
      M hM e₁ tail₁ e₂ tail₂ hLeftTrans hRightTrans
      (hTailSound hTailDistinct)

private theorem seq_distinct_concat_unit_seq_unit_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M)
    (e₁ tail e₂ U : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail) ->
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)
        (Term.Apply (Term.UOp UserOp.seq_unit) e₂) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hHeadSound hDistinct
  have hBranch :
      __eo_ite
          (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
            (__are_distinct_terms_type e₁ e₂ U))
          (Term.Boolean true) (__seq_is_non_empty tail) =
        Term.Boolean true := by
    change __seq_distinct_terms
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e₁)) tail)
        (Term.Apply (Term.UOp UserOp.seq_unit) e₂) U =
      Term.Boolean true at hDistinct
    cases U <;>
      (rw [__seq_distinct_terms.eq_def] at hDistinct
       simp only at hDistinct)
    all_goals first | exact hDistinct | cases hDistinct
  rcases eo_ite_eq_true_cases
      (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
        (__are_distinct_terms_type e₁ e₂ U))
      (Term.Boolean true) (__seq_is_non_empty tail) hBranch with
    ⟨hHeadGuard, _⟩ | ⟨_hHeadGuardFalse, hTailNonEmpty⟩
  · rcases eo_ite_eq_false_guard_true hHeadGuard with
      ⟨hHeadEqFalse, hHeadDistinct⟩
    exact concat_seq_unit_seq_unit_model_eval_eq_false_of_head
      M hM e₁ tail e₂ hLeftTrans
      (hHeadSound hHeadEqFalse hHeadDistinct)
  · exact concat_seq_unit_seq_unit_model_eval_eq_false_of_tail
      M hM e₁ tail e₂ hLeftTrans hTailNonEmpty

private theorem seq_distinct_seq_unit_concat_unit_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M)
    (e₁ e₂ tail U : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) ->
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms (Term.Apply (Term.UOp UserOp.seq_unit) e₁)
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail))) =
      SmtValue.Boolean false := by
  intro hRightTrans hHeadSound hDistinct
  have hBranch :
      __eo_ite
          (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
            (__are_distinct_terms_type e₁ e₂ U))
          (Term.Boolean true) (__seq_is_non_empty tail) =
        Term.Boolean true := by
    change __seq_distinct_terms
        (Term.Apply (Term.UOp UserOp.seq_unit) e₁)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e₂)) tail) U =
      Term.Boolean true at hDistinct
    cases U <;>
      (rw [__seq_distinct_terms.eq_def] at hDistinct
       simp only at hDistinct)
    all_goals first | exact hDistinct | cases hDistinct
  rcases eo_ite_eq_true_cases
      (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
        (__are_distinct_terms_type e₁ e₂ U))
      (Term.Boolean true) (__seq_is_non_empty tail) hBranch with
    ⟨hHeadGuard, _⟩ | ⟨_hHeadGuardFalse, hTailNonEmpty⟩
  · rcases eo_ite_eq_false_guard_true hHeadGuard with
      ⟨hHeadEqFalse, hHeadDistinct⟩
    exact seq_unit_concat_seq_unit_model_eval_eq_false_of_head
      M hM e₁ e₂ tail hRightTrans
      (hHeadSound hHeadEqFalse hHeadDistinct)
  · exact seq_unit_concat_seq_unit_model_eval_eq_false_of_tail
      M hM e₁ e₂ tail hRightTrans hTailNonEmpty

private theorem seq_distinct_terms_not_true_of_not_shapes {a b U : Term} :
    (¬ ∃ V, b = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)) ->
    (¬ ∃ V, a = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)) ->
    (¬ ∃ e₁ tail₁ e₂ tail₂,
      a = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁ ∧
      b = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) ->
    (¬ ∃ e₁ tail e₂,
      a = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail ∧
      b = Term.Apply (Term.UOp UserOp.seq_unit) e₂) ->
    (¬ ∃ e₁ e₂ tail,
      a = Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
      b = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) ->
    (¬ ∃ e₁ e₂,
      a = Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
      b = Term.Apply (Term.UOp UserOp.seq_unit) e₂) ->
    __seq_distinct_terms a b U ≠ Term.Boolean true := by
  intro hbEmpty haEmpty hConcatConcat hConcatUnit hUnitConcat hUnitUnit hDistinct
  rw [__seq_distinct_terms.eq_def] at hDistinct
  split at hDistinct <;> try cases hDistinct
  all_goals
    first
    | exact hbEmpty ⟨_, rfl⟩
    | exact haEmpty ⟨_, rfl⟩
    | exact hConcatConcat ⟨_, _, _, _, rfl, rfl⟩
    | exact hConcatUnit ⟨_, _, _, rfl, rfl⟩
    | exact hUnitConcat ⟨_, _, _, rfl, rfl⟩
    | exact hUnitUnit ⟨_, _, rfl, rfl⟩

private theorem seq_distinct_terms_model_eval_eq_false_of_head_sound
    (M : SmtModel) (hM : model_wf M) (a b U : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (∀ e₁ e₂,
      sizeOf e₁ + sizeOf e₂ < sizeOf a + sizeOf b ->
      RuleProofs.eo_has_smt_translation e₁ ->
      RuleProofs.eo_has_smt_translation e₂ ->
      __eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms a b U = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans hHeadSound hDistinct
  by_cases hbEmpty :
      ∃ V, b = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)
  · rcases hbEmpty with ⟨V, rfl⟩
    exact seq_distinct_terms_right_empty_model_eval_eq_false
      M hM a V U haTrans hbTrans hDistinct
  · by_cases haEmpty :
        ∃ V, a = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)
    · rcases haEmpty with ⟨V, rfl⟩
      exact seq_distinct_terms_left_empty_model_eval_eq_false
        M hM V b U haTrans hbTrans hDistinct
    · by_cases hConcatConcat :
        ∃ e₁ tail₁ e₂ tail₂,
          a = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁ ∧
          b = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂
      · rcases hConcatConcat with ⟨e₁, tail₁, e₂, tail₂, hA, hB⟩
        subst a
        subst b
        have hLeftArgs :=
          str_concat_arg_translations_of_translation
            (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁ haTrans
        have hRightArgs :=
          str_concat_arg_translations_of_translation
            (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂ hbTrans
        have he₁Trans :
            RuleProofs.eo_has_smt_translation e₁ :=
          seq_unit_arg_translation_of_translation e₁ hLeftArgs.1
        have he₂Trans :
            RuleProofs.eo_has_smt_translation e₂ :=
          seq_unit_arg_translation_of_translation e₂ hRightArgs.1
        have hTailMeasure :
            sizeOf tail₁ + sizeOf tail₂ <
              sizeOf (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁) +
                sizeOf (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) := by
          simp [mkConcat]
          omega
        exact seq_distinct_concat_unit_concat_unit_model_eval_eq_false
          M hM e₁ tail₁ e₂ tail₂ U haTrans hbTrans
          (fun hEq hHeadDistinct =>
            hHeadSound e₁ e₂ (by simp [mkConcat]; omega)
              he₁Trans he₂Trans hEq hHeadDistinct)
          (fun hTailDistinct =>
            seq_distinct_terms_model_eval_eq_false_of_head_sound
              M hM tail₁ tail₂ U hLeftArgs.2 hRightArgs.2
              (fun x y hSmall hxTrans hyTrans hEq hDistinct =>
                hHeadSound x y (Nat.lt_trans hSmall hTailMeasure)
                  hxTrans hyTrans hEq hDistinct)
              hTailDistinct)
          hDistinct
      · by_cases hConcatUnit :
          ∃ e₁ tail e₂,
            a = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail ∧
            b = Term.Apply (Term.UOp UserOp.seq_unit) e₂
        · rcases hConcatUnit with ⟨e₁, tail, e₂, hA, hB⟩
          subst a
          subst b
          have hLeftArgs :=
            str_concat_arg_translations_of_translation
              (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail haTrans
          have he₁Trans :
              RuleProofs.eo_has_smt_translation e₁ :=
            seq_unit_arg_translation_of_translation e₁ hLeftArgs.1
          have he₂Trans :
              RuleProofs.eo_has_smt_translation e₂ :=
            seq_unit_arg_translation_of_translation e₂ hbTrans
          exact seq_distinct_concat_unit_seq_unit_model_eval_eq_false
            M hM e₁ tail e₂ U haTrans
            (fun hEq hHeadDistinct =>
              hHeadSound e₁ e₂ (by simp [mkConcat]; omega)
                he₁Trans he₂Trans hEq hHeadDistinct)
            hDistinct
        · by_cases hUnitConcat :
            ∃ e₁ e₂ tail,
              a = Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
              b = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail
          · rcases hUnitConcat with ⟨e₁, e₂, tail, hA, hB⟩
            subst a
            subst b
            have hRightArgs :=
              str_concat_arg_translations_of_translation
                (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail hbTrans
            have he₁Trans :
                RuleProofs.eo_has_smt_translation e₁ :=
              seq_unit_arg_translation_of_translation e₁ haTrans
            have he₂Trans :
                RuleProofs.eo_has_smt_translation e₂ :=
              seq_unit_arg_translation_of_translation e₂ hRightArgs.1
            exact seq_distinct_seq_unit_concat_unit_model_eval_eq_false
              M hM e₁ e₂ tail U hbTrans
              (fun hEq hHeadDistinct =>
                hHeadSound e₁ e₂ (by simp [mkConcat]; omega)
                  he₁Trans he₂Trans hEq hHeadDistinct)
              hDistinct
          · by_cases hUnitUnit :
              ∃ e₁ e₂,
                a = Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
                b = Term.Apply (Term.UOp UserOp.seq_unit) e₂
            · rcases hUnitUnit with ⟨e₁, e₂, hA, hB⟩
              subst a
              subst b
              have he₁Trans :
                  RuleProofs.eo_has_smt_translation e₁ :=
                seq_unit_arg_translation_of_translation e₁ haTrans
              have he₂Trans :
                  RuleProofs.eo_has_smt_translation e₂ :=
                seq_unit_arg_translation_of_translation e₂ hbTrans
              exact seq_distinct_seq_unit_seq_unit_model_eval_eq_false
                M e₁ e₂ U
                (fun hEq hHeadDistinct =>
                  hHeadSound e₁ e₂ (by simp; omega)
                    he₁Trans he₂Trans hEq hHeadDistinct)
                hDistinct
            · -- All remaining shapes make `__seq_distinct_terms` false or stuck.
              exact False.elim
                (seq_distinct_terms_not_true_of_not_shapes
                  hbEmpty haEmpty hConcatConcat hConcatUnit hUnitConcat
                  hUnitUnit hDistinct)
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals try assumption
  all_goals simp_all [mkConcat]
  all_goals omega

private def dtDistinctBaseGuard (c : Term) : Term :=
  __eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
    (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
      (__eo_is_ok (__eo_dt_selectors c)))

private theorem dt_distinct_terms_base_guard_root
    (c : Term) :
    dtDistinctBaseGuard c = Term.Boolean true ->
    c = Term.UOp UserOp.tuple ∨
      c = Term.UOp UserOp.tuple_unit ∨
        ∃ s d i, c = Term.DtCons s d i := by
  intro h
  cases c <;>
    simp [dtDistinctBaseGuard, __eo_is_eq, __eo_ite, __eo_is_ok, __eo_dt_selectors,
      __eo_dt_selectors_main, native_ite, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] at h
  case UOp op =>
    cases op <;> simp at h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  case DtCons s d i =>
    exact Or.inr (Or.inr ⟨s, d, i, rfl⟩)

private theorem eo_not_eq_true_eq_false {x : Term} :
    __eo_not x = Term.Boolean true -> x = Term.Boolean false := by
  intro h
  cases x <;> simp [__eo_not] at h
  case Boolean b =>
    cases b <;> simp [SmtEval.native_not] at h ⊢

private theorem dt_distinct_terms_base_info {c d : Term} :
    __eo_requires (__eo_and (dtDistinctBaseGuard c) (dtDistinctBaseGuard d))
        (Term.Boolean true) (__eo_not (__eo_eq c d)) =
      Term.Boolean true ->
    dtDistinctBaseGuard c = Term.Boolean true ∧
      dtDistinctBaseGuard d = Term.Boolean true ∧
        __eo_eq c d = Term.Boolean false := by
  intro h
  have hReqNe :
      __eo_requires (__eo_and (dtDistinctBaseGuard c) (dtDistinctBaseGuard d))
          (Term.Boolean true) (__eo_not (__eo_eq c d)) ≠
        Term.Stuck := by
    rw [h]
    intro hBad
    cases hBad
  have hGuardAnd :
      __eo_and (dtDistinctBaseGuard c) (dtDistinctBaseGuard d) =
        Term.Boolean true :=
    _root_.eo_requires_arg_eq_of_ne_stuck hReqNe
  have hResult :
      __eo_not (__eo_eq c d) = Term.Boolean true := by
    have hReqResult :=
      _root_.eo_requires_result_eq_of_ne_stuck hReqNe
    simpa [h] using hReqResult.symm
  rcases eo_and_true hGuardAnd with ⟨hc, hd⟩
  exact ⟨hc, hd, eo_not_eq_true_eq_false hResult⟩

private theorem dt_distinct_terms_base_info_of_non_apply {c d : Term} :
    (∀ f x, c ≠ Term.Apply f x) ->
    (∀ f x, d ≠ Term.Apply f x) ->
    __dt_distinct_terms c d = Term.Boolean true ->
    dtDistinctBaseGuard c = Term.Boolean true ∧
      dtDistinctBaseGuard d = Term.Boolean true ∧
        __eo_eq c d = Term.Boolean false := by
  intro hcNotApply hdNotApply hDistinct
  cases c <;> cases d <;>
    try
      (first
        | exact False.elim (hcNotApply _ _ rfl)
        | exact False.elim (hdNotApply _ _ rfl))
  all_goals
    try
      (rw [__dt_distinct_terms.eq_def] at hDistinct
       simp at hDistinct)
  all_goals
    exact dt_distinct_terms_base_info
      (by simpa [dtDistinctBaseGuard] using hDistinct)

private theorem dt_distinct_terms_base_roots_of_non_apply {c c₂ : Term} :
    (∀ f x, c ≠ Term.Apply f x) ->
    (∀ f x, c₂ ≠ Term.Apply f x) ->
    __dt_distinct_terms c c₂ = Term.Boolean true ->
    (c = Term.UOp UserOp.tuple ∨
      c = Term.UOp UserOp.tuple_unit ∨
        ∃ s D i, c = Term.DtCons s D i) ∧
      (c₂ = Term.UOp UserOp.tuple ∨
        c₂ = Term.UOp UserOp.tuple_unit ∨
          ∃ s D i, c₂ = Term.DtCons s D i) ∧
        __eo_eq c c₂ = Term.Boolean false := by
  intro hcNotApply hdNotApply hDistinct
  rcases dt_distinct_terms_base_info_of_non_apply
      hcNotApply hdNotApply hDistinct with
    ⟨hcGuard, hdGuard, hEqFalse⟩
  exact ⟨dt_distinct_terms_base_guard_root c hcGuard,
    dt_distinct_terms_base_guard_root c₂ hdGuard, hEqFalse⟩

private theorem tuple_ctor_head_no_smt_translation :
    ¬ RuleProofs.eo_has_smt_translation (Term.UOp UserOp.tuple) := by
  intro h
  unfold RuleProofs.eo_has_smt_translation at h
  change __smtx_typeof SmtTerm.None ≠ SmtType.None at h
  exact h TranslationProofs.smtx_typeof_none

private theorem native_reserved_datatype_name_tuple :
    __eo_to_smt_reserved_datatype_name (native_string_lit "@Tuple") = true := by
  native_decide

private theorem dtcons_reserved_false_of_translation
    {s : native_String} {d : DatatypeDecl} {i : native_Nat} :
    RuleProofs.eo_has_smt_translation (Term.DtCons s d i) ->
    __eo_to_smt_reserved_datatype_name s = false := by
  intro hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans
  change
    __smtx_typeof
        (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
          (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i)) ≠
      SmtType.None at hTrans
  cases hReserved : __eo_to_smt_reserved_datatype_name s
  · simp
  · exfalso
    rw [hReserved] at hTrans
    simp [native_ite] at hTrans

private theorem dtcons_model_eval_of_translation
    (M : SmtModel) {s : native_String} {d : DatatypeDecl} {i : native_Nat} :
    RuleProofs.eo_has_smt_translation (Term.DtCons s d i) ->
    __smtx_model_eval M (__eo_to_smt (Term.DtCons s d i)) =
      SmtValue.DtCons s (__eo_to_smt_datatype_decl d) i := by
  intro hTrans
  have hReserved : __eo_to_smt_reserved_datatype_name s = false :=
    dtcons_reserved_false_of_translation hTrans
  change
    __smtx_model_eval M
        (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
          (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i)) =
      SmtValue.DtCons s (__eo_to_smt_datatype_decl d) i
  rw [hReserved]
  simp [native_ite, __smtx_model_eval]

private theorem dtcons_smt_datatype_wf_of_translation
    {s : native_String} {d : DatatypeDecl} {i : native_Nat} :
    RuleProofs.eo_has_smt_translation (Term.DtCons s d i) ->
    __smtx_type_wf
        (SmtType.Datatype s (__eo_to_smt_datatype_decl d)) = true := by
  intro hTrans
  have hReserved : __eo_to_smt_reserved_datatype_name s = false :=
    dtcons_reserved_false_of_translation hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans
  change
    __smtx_typeof
        (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
          (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i)) ≠
      SmtType.None at hTrans
  rw [hReserved] at hTrans
  simp [native_ite] at hTrans
  let raw :=
    __smtx_typeof_dt_cons_rec
      (SmtType.Datatype s (__eo_to_smt_datatype_decl d))
      (__smtx_dt_resolve
        (__smtx_dd_lookup s (__eo_to_smt_datatype_decl d))
        (__eo_to_smt_datatype_decl d)) i
  have hGuardNN :
      __smtx_typeof_guard_wf
          (SmtType.Datatype s (__eo_to_smt_datatype_decl d)) raw ≠
        SmtType.None := by
    simpa [Smtm.typeof_dt_cons_eq, raw] using hTrans
  have hBaseWf :
      __smtx_type_wf (SmtType.Datatype s (__eo_to_smt_datatype_decl d)) =
        true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none
      (SmtType.Datatype s (__eo_to_smt_datatype_decl d)) raw hGuardNN
  exact hBaseWf

private theorem tuple_unit_model_eval
    (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.tuple_unit)) =
      SmtValue.DtCons (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
        native_nat_zero := by
  simp [TranslationProofs.eo_to_smt_term_tuple_unit, __smtx_model_eval,
    __eo_to_smt_tuple_decl]

private theorem tuple_unit_dtcons_model_eval_eq_false
    (M : SmtModel) {s : native_String} {d : DatatypeDecl} {i : native_Nat} :
    RuleProofs.eo_has_smt_translation (Term.DtCons s d i) ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.tuple_unit)))
        (__smtx_model_eval M (__eo_to_smt (Term.DtCons s d i))) =
      SmtValue.Boolean false := by
  intro hTrans
  have hReserved : __eo_to_smt_reserved_datatype_name s = false :=
    dtcons_reserved_false_of_translation hTrans
  have hNameNe : s ≠ native_string_lit "@Tuple" := by
    intro hs
    subst s
    rw [native_reserved_datatype_name_tuple] at hReserved
    cases hReserved
  rw [tuple_unit_model_eval M, dtcons_model_eval_of_translation M hTrans]
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hVal
      injection hVal with hs _ _
      exact hNameNe hs.symm)
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, h₁, _h₂⟩
      cases h₁)

private theorem dtcons_tuple_unit_model_eval_eq_false
    (M : SmtModel) {s : native_String} {d : DatatypeDecl} {i : native_Nat} :
    RuleProofs.eo_has_smt_translation (Term.DtCons s d i) ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.DtCons s d i)))
        (__smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.tuple_unit))) =
      SmtValue.Boolean false := by
  intro hTrans
  rw [dtcons_model_eval_of_translation M hTrans, tuple_unit_model_eval M]
  have hReserved : __eo_to_smt_reserved_datatype_name s = false :=
    dtcons_reserved_false_of_translation hTrans
  have hNameNe : s ≠ native_string_lit "@Tuple" := by
    intro hs
    subst s
    rw [native_reserved_datatype_name_tuple] at hReserved
    cases hReserved
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hVal
      injection hVal with hs _ _
      exact hNameNe hs)
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, h₁, _h₂⟩
      cases h₁)

private theorem dtcons_dtcons_model_eval_eq_false
    (M : SmtModel)
    {s₁ s₂ : native_String} {d₁ d₂ : DatatypeDecl}
    {i₁ i₂ : native_Nat} :
    RuleProofs.eo_has_smt_translation (Term.DtCons s₁ d₁ i₁) ->
    RuleProofs.eo_has_smt_translation (Term.DtCons s₂ d₂ i₂) ->
    __eo_eq (Term.DtCons s₁ d₁ i₁) (Term.DtCons s₂ d₂ i₂) =
      Term.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.DtCons s₁ d₁ i₁)))
        (__smtx_model_eval M (__eo_to_smt (Term.DtCons s₂ d₂ i₂))) =
      SmtValue.Boolean false := by
  intro h₁Trans h₂Trans hEqFalse
  rw [dtcons_model_eval_of_translation M h₁Trans,
    dtcons_model_eval_of_translation M h₂Trans]
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hVal
      injection hVal with hs hD hi
      subst s₂
      subst i₂
      have hWF :
          __smtx_type_wf
              (SmtType.Datatype s₁ (__eo_to_smt_datatype_decl d₁)) = true :=
        dtcons_smt_datatype_wf_of_translation h₁Trans
      have hReserved : __eo_to_smt_reserved_datatype_name s₁ = false :=
        dtcons_reserved_false_of_translation h₁Trans
      have hTypeEq :
          Term.DatatypeType s₁ d₁ = Term.DatatypeType s₁ d₂ :=
        TranslationProofs.eo_to_smt_type_injective_of_wf
          (by simp [TranslationProofs.eo_to_smt_type_datatype,
            native_ite, hReserved])
          (by simpa [TranslationProofs.eo_to_smt_type_datatype,
            native_ite, hReserved] using hD.symm)
          hWF
      have hd : d₁ = d₂ := by
        injection hTypeEq
      subst d₂
      exact (eo_eq_false_ne hEqFalse) rfl)
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, h₁, _h₂⟩
      cases h₁)

private theorem dt_distinct_terms_base_model_eval_eq_false_of_non_apply
    (M : SmtModel) {c d : Term} :
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation d ->
    (∀ f x, c ≠ Term.Apply f x) ->
    (∀ f x, d ≠ Term.Apply f x) ->
    __dt_distinct_terms c d = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt c))
      (__smtx_model_eval M (__eo_to_smt d)) = SmtValue.Boolean false := by
  intro hcTrans hdTrans hcNotApply hdNotApply hDistinct
  rcases dt_distinct_terms_base_roots_of_non_apply
      hcNotApply hdNotApply hDistinct with
    ⟨hcRoot, hdRoot, hEqFalse⟩
  rcases hcRoot with hTuple | hUnit | hDt
  · subst c
    exact False.elim (tuple_ctor_head_no_smt_translation hcTrans)
  · subst c
    rcases hdRoot with hTuple | hUnit | hDt
    · subst d
      exact False.elim (tuple_ctor_head_no_smt_translation hdTrans)
    · subst d
      exact False.elim ((eo_eq_false_ne hEqFalse) rfl)
    · rcases hDt with ⟨s, D, i, rfl⟩
      exact tuple_unit_dtcons_model_eval_eq_false M hdTrans
  · rcases hDt with ⟨s₁, D₁, i₁, rfl⟩
    rcases hdRoot with hTuple | hUnit | hDt₂
    · subst d
      exact False.elim (tuple_ctor_head_no_smt_translation hdTrans)
    · subst d
      exact dtcons_tuple_unit_model_eval_eq_false M hcTrans
    · rcases hDt₂ with ⟨s₂, D₂, i₂, rfl⟩
      exact dtcons_dtcons_model_eval_eq_false M hcTrans hdTrans hEqFalse

private theorem dt_distinct_terms_apply_apply_true_cases
    {f a g b : Term} :
    __dt_distinct_terms (Term.Apply f a) (Term.Apply g b) =
      Term.Boolean true ->
    __dt_distinct_terms f g = Term.Boolean true ∨
      (__dt_distinct_terms f g = Term.Boolean false ∧
        __eo_eq a b = Term.Boolean false ∧
        __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true) := by
  intro hDistinct
  rw [__dt_distinct_terms.eq_def] at hDistinct
  change
    __eo_ite (__dt_distinct_terms f g) (Term.Boolean true)
      (__eo_ite (__eo_eq a b) (Term.Boolean false)
        (__are_distinct_terms_type a b (__eo_typeof a))) =
      Term.Boolean true at hDistinct
  rcases eo_ite_eq_true_cases
      (__dt_distinct_terms f g) (Term.Boolean true)
      (__eo_ite (__eo_eq a b) (Term.Boolean false)
        (__are_distinct_terms_type a b (__eo_typeof a)))
      hDistinct with
    hHead | hTail
  · exact Or.inl hHead.1
  · rcases eo_ite_eq_false_guard_true hTail.2 with
      ⟨hEqFalse, hArgDistinct⟩
    exact Or.inr ⟨hTail.1, hEqFalse, hArgDistinct⟩

private theorem tuple_apply_components_have_translation
    {a as : Term} :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as) ->
    RuleProofs.eo_has_smt_translation a ∧
      RuleProofs.eo_has_smt_translation as := by
  intro hTrans
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) ≠
      SmtType.None at hTrans
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      as a hTrans with
    ⟨c, hTailTy⟩
  have hHeadNN :
      __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    TranslationProofs.smtx_tuple_prepend_head_non_none_of_tail_tuple_type
      (__eo_to_smt as) (__eo_to_smt a)
      (__smtx_typeof (__eo_to_smt a)) c hTailTy hTrans
  constructor
  · exact hHeadNN
  · unfold RuleProofs.eo_has_smt_translation
    rw [hTailTy]
    simp

private theorem dt_distinct_terms_model_eval_eq_false_of_head_sound
    (M : SmtModel) (hM : model_wf M) (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (∀ e₁ e₂,
      sizeOf e₁ + sizeOf e₂ < sizeOf a + sizeOf b ->
      RuleProofs.eo_has_smt_translation e₁ ->
      RuleProofs.eo_has_smt_translation e₂ ->
      __eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ (__eo_typeof e₁) = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) = SmtValue.Boolean false) ->
    __dt_distinct_terms a b = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans hHeadSound hDistinct
  by_cases hTyEq :
      __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b)
  ·
    by_cases hApp :
        (∃ f x, a = Term.Apply f x) ∨ (∃ g y, b = Term.Apply g y)
    · -- Application spines need the constructor/tuple lifting step.
      by_cases hTupleTuple :
          ∃ a₀ as b₀ bs,
            a = Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a₀) as ∧
              b = Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b₀) bs
      · rcases hTupleTuple with ⟨a₀, as, b₀, bs, rfl, rfl⟩
        rcases tuple_apply_components_have_translation haTrans with
          ⟨ha₀Trans, hasTrans⟩
        rcases tuple_apply_components_have_translation hbTrans with
          ⟨hb₀Trans, hbsTrans⟩
        rcases dt_distinct_terms_apply_apply_true_cases hDistinct with
          hHeadDistinct | hTailDistinct
        · rcases dt_distinct_terms_apply_apply_true_cases hHeadDistinct with
            hTupleRootDistinct | hHeadArgDistinct
          · change
              __dt_distinct_terms (Term.UOp UserOp.tuple)
                  (Term.UOp UserOp.tuple) = Term.Boolean true at hTupleRootDistinct
            simp [__dt_distinct_terms, __eo_requires, __eo_and, __eo_ite,
              __eo_is_eq, __eo_not, __eo_eq, native_ite,
              native_teq, native_and, native_not, SmtEval.native_and,
              SmtEval.native_not] at hTupleRootDistinct
          · have hHeadEvalFalse :
                __smtx_model_eval_eq
                    (__smtx_model_eval M (__eo_to_smt a₀))
                    (__smtx_model_eval M (__eo_to_smt b₀)) =
                  SmtValue.Boolean false :=
              hHeadSound a₀ b₀ (by simp; omega) ha₀Trans hb₀Trans
                hHeadArgDistinct.2.1 hHeadArgDistinct.2.2
            exact tuple_apply_model_eval_eq_false_of_component
              M hM a₀ as b₀ bs haTrans hbTrans (Or.inl hHeadEvalFalse)
        · have hTailEvalFalse :
              __smtx_model_eval_eq
                  (__smtx_model_eval M (__eo_to_smt as))
                (__smtx_model_eval M (__eo_to_smt bs)) =
                SmtValue.Boolean false :=
            hHeadSound as bs (by simp; omega) hasTrans hbsTrans
              hTailDistinct.2.1 hTailDistinct.2.2
          exact tuple_apply_model_eval_eq_false_of_component
            M hM a₀ as b₀ bs haTrans hbTrans (Or.inr hTailEvalFalse)
      ·
        by_cases haApply : ∃ f x, a = Term.Apply f x
        · rcases haApply with ⟨f, x, rfl⟩
          by_cases hbApply : ∃ g y, b = Term.Apply g y
          · rcases hbApply with ⟨g, y, rfl⟩
            have hNotTuple : ∀ x₀ y₀,
                f = Term.Apply (Term.UOp UserOp.tuple) x₀ ->
                g = Term.Apply (Term.UOp UserOp.tuple) y₀ -> False := by
              intro x₀ y₀ hf hg
              apply hTupleTuple
              exact ⟨x₀, x, y₀, y, by rw [hf], by rw [hg]⟩
            rcases dt_distinct_terms_apply_apply_true_cases hDistinct with
              hHeadDistinct | hTailDistinct
            · by_cases hfTrans : RuleProofs.eo_has_smt_translation f
              · by_cases hgTrans : RuleProofs.eo_has_smt_translation g
                · have hHeadMeasure :
                      sizeOf f + sizeOf g <
                        sizeOf (Term.Apply f x) + sizeOf (Term.Apply g y) := by
                    simp
                    omega
                  have hHeadEvalFalse :
                      __smtx_model_eval_eq
                          (__smtx_model_eval M (__eo_to_smt f))
                          (__smtx_model_eval M (__eo_to_smt g)) =
                        SmtValue.Boolean false :=
                    dt_distinct_terms_model_eval_eq_false_of_head_sound
                      M hM f g hfTrans hgTrans
                      (fun p q hSmall hpTrans hqTrans hEq hDistinct =>
                        hHeadSound p q (Nat.lt_trans hSmall hHeadMeasure)
                          hpTrans hqTrans hEq hDistinct)
                      hHeadDistinct
                  exact
                    dt_distinct_terms_apply_apply_model_eval_eq_false_of_head_component
                      M hM f g x y hfTrans hgTrans haTrans hbTrans
                      hHeadDistinct hHeadEvalFalse
                · rcases
                    dt_distinct_terms_true_nontranslated_right_apply_head_is_tuple
                      f g y hbTrans hHeadDistinct hgTrans with
                    ⟨y₀, hgy⟩
                  subst g
                  exact
                    dt_distinct_terms_apply_apply_model_eval_eq_false_of_right_tuple_head
                      M hM f x y₀ y hfTrans haTrans hbTrans hHeadDistinct
              · rcases
                  dt_distinct_terms_true_nontranslated_left_apply_head_is_tuple
                    f g x haTrans hHeadDistinct hfTrans with
                  ⟨x₀, hfx⟩
                subst f
                by_cases hgTrans : RuleProofs.eo_has_smt_translation g
                · exact
                    dt_distinct_terms_apply_apply_model_eval_eq_false_of_left_tuple_head
                      M hM x₀ x g y haTrans hgTrans hbTrans hHeadDistinct
                · rcases
                    dt_distinct_terms_true_nontranslated_right_apply_head_is_tuple
                      (Term.Apply (Term.UOp UserOp.tuple) x₀) g y
                      hbTrans hHeadDistinct hgTrans with
                    ⟨y₀, hgy⟩
                  subst g
                  exact False.elim (hNotTuple x₀ y₀ rfl rfl)
            · have hxTrans : RuleProofs.eo_has_smt_translation x := by
                rcases
                    CongSupport.eo_apply_arg_has_translation_of_has_translation_or_distinct
                      f x haTrans with
                  hDistinctHead | hxTrans
                · subst f
                  exact False.elim
                    (dt_distinct_terms_distinct_left_ne_false g
                      hTailDistinct.1)
                · exact hxTrans
              have hyTrans : RuleProofs.eo_has_smt_translation y := by
                rcases
                    CongSupport.eo_apply_arg_has_translation_of_has_translation_or_distinct
                      g y hbTrans with
                  hDistinctHead | hyTrans
                · subst g
                  exact False.elim
                    (dt_distinct_terms_distinct_right_ne_false f
                      hTailDistinct.1)
                · exact hyTrans
              have hArgEvalFalse :
                  __smtx_model_eval_eq
                      (__smtx_model_eval M (__eo_to_smt x))
                      (__smtx_model_eval M (__eo_to_smt y)) =
                    SmtValue.Boolean false :=
                hHeadSound x y (by simp; omega) hxTrans hyTrans
                  hTailDistinct.2.1 hTailDistinct.2.2
              exact
                dt_distinct_terms_apply_apply_model_eval_eq_false_of_arg_component
                  M hM f g x y haTrans hbTrans hNotTuple
                  hTailDistinct.1 hArgEvalFalse
          · have hbNotApply : ∀ g y, b ≠ Term.Apply g y := by
              intro g y h
              exact hbApply ⟨g, y, h⟩
            exact dt_distinct_terms_apply_left_nonapply_model_eval_eq_false
              M hM f x b haTrans hbTrans hbNotApply hDistinct
        · rcases hApp with hA | hB
          · exact False.elim (haApply hA)
          · rcases hB with ⟨g, y, rfl⟩
            have haNotApply : ∀ f x, a ≠ Term.Apply f x := by
              intro f x h
              exact haApply ⟨f, x, h⟩
            exact dt_distinct_terms_apply_right_nonapply_model_eval_eq_false
              M hM a g y haTrans hbTrans haNotApply hDistinct
    · have haNotApply : ∀ f x, a ≠ Term.Apply f x := by
        intro f x h
        exact hApp (Or.inl ⟨f, x, h⟩)
      have hbNotApply : ∀ g y, b ≠ Term.Apply g y := by
        intro g y h
        exact hApp (Or.inr ⟨g, y, h⟩)
      exact dt_distinct_terms_base_model_eval_eq_false_of_non_apply
        M haTrans hbTrans haNotApply hbNotApply hDistinct
  · exact smtx_model_eval_eq_false_of_type_ne
      M hM (__eo_to_smt a) (__eo_to_smt b) haTrans hbTrans hTyEq

private theorem are_distinct_terms_type_model_eval_eq_false_of_type
    (M : SmtModel) (hM : model_wf M) (T a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_eq a b = Term.Boolean false ->
    __are_distinct_terms_type a b T = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans hEqFalse hDistinct
  cases T with
  | UOp op =>
      cases op with
      | Int =>
          exact are_distinct_terms_type_primitive_model_eval_eq_false
            M a b (Term.UOp UserOp.Int) hEqFalse hDistinct (by simp)
      | Real =>
          exact are_distinct_terms_type_primitive_model_eval_eq_false
            M a b (Term.UOp UserOp.Real) hEqFalse hDistinct (by simp)
      | _ =>
        -- Non-primitive type heads fall through to the datatype recognizer.
        have hDtDistinct :
            __dt_distinct_terms a b = Term.Boolean true := by
          by_cases ha : a = Term.Stuck
          · subst a
            simp [__are_distinct_terms_type.eq_def] at hDistinct
          by_cases hb : b = Term.Stuck
          · subst b
            simp [__are_distinct_terms_type.eq_def] at hDistinct
          exact dt_ite_is_ok_self_true (by simpa [__are_distinct_terms_type.eq_def, ha, hb] using hDistinct)
        exact dt_distinct_terms_model_eval_eq_false_of_head_sound
          M hM a b haTrans hbTrans
          (fun e₁ e₂ hSmall he₁Trans he₂Trans hHeadEqFalse hHeadDistinct =>
            are_distinct_terms_type_model_eval_eq_false_of_type
              M hM (__eo_typeof e₁) e₁ e₂ he₁Trans he₂Trans
              hHeadEqFalse hHeadDistinct)
          hDtDistinct
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              exact are_distinct_terms_type_primitive_model_eval_eq_false
                M a b (Term.Apply (Term.UOp UserOp.BitVec) x)
                hEqFalse hDistinct (by simp)
          | Seq =>
              by_cases hxChar : x = Term.UOp UserOp.Char
              · subst x
                exact are_distinct_terms_type_primitive_model_eval_eq_false
                  M a b
                  (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                  hEqFalse hDistinct (by simp)
              · have hSeqDistinct :
                    __seq_distinct_terms a b x = Term.Boolean true :=
                  are_distinct_terms_type_seq_true_seq_distinct hxChar hDistinct
                exact seq_distinct_terms_model_eval_eq_false_of_head_sound
                  M hM a b x haTrans hbTrans
                  (fun e₁ e₂ hSmall he₁Trans he₂Trans hHeadEqFalse hHeadDistinct =>
                    are_distinct_terms_type_model_eval_eq_false_of_type
                      M hM x e₁ e₂ he₁Trans he₂Trans
                      hHeadEqFalse hHeadDistinct)
                  hSeqDistinct
          | Set =>
              have hSetWitness :
                  __set_is_not_subset a b x = Term.Boolean true ∨
                    __set_is_not_subset b a x = Term.Boolean true :=
                are_distinct_terms_type_set_true_not_subset hDistinct
              rcases hSetWitness with hAB | hBA
              · exact set_is_not_subset_model_eval_eq_false_of_head_sound
                  M hM a b x haTrans hbTrans
                  (fun e₁ e₂ hSmall he₁Trans he₂Trans hHeadEqFalse hHeadDistinct =>
                    are_distinct_terms_type_model_eval_eq_false_of_type
                      M hM x e₁ e₂ he₁Trans he₂Trans
                      hHeadEqFalse hHeadDistinct)
                  hAB
              · exact set_is_not_subset_model_eval_eq_false_of_head_sound_symm
                  M hM a b x haTrans hbTrans
                  (fun e₁ e₂ hSmall he₁Trans he₂Trans hHeadEqFalse hHeadDistinct =>
                    are_distinct_terms_type_model_eval_eq_false_of_type
                      M hM x e₁ e₂ he₁Trans he₂Trans
                      hHeadEqFalse hHeadDistinct)
                  hBA
          | _ =>
              -- Other applied type heads use datatype spine distinctness.
              have hDtDistinct :
                  __dt_distinct_terms a b = Term.Boolean true := by
                by_cases ha : a = Term.Stuck
                · subst a
                  simp [__are_distinct_terms_type.eq_def] at hDistinct
                by_cases hb : b = Term.Stuck
                · subst b
                  simp [__are_distinct_terms_type.eq_def] at hDistinct
                exact dt_ite_is_ok_self_true (by simpa [__are_distinct_terms_type.eq_def, ha, hb] using hDistinct)
              exact dt_distinct_terms_model_eval_eq_false_of_head_sound
                M hM a b haTrans hbTrans
                (fun e₁ e₂ hSmall he₁Trans he₂Trans hHeadEqFalse hHeadDistinct =>
                  are_distinct_terms_type_model_eval_eq_false_of_type
                    M hM (__eo_typeof e₁) e₁ e₂ he₁Trans he₂Trans
                    hHeadEqFalse hHeadDistinct)
                hDtDistinct
      | _ =>
          -- Non-`UOp` type applications are datatype-style fallthroughs.
          have hDtDistinct :
              __dt_distinct_terms a b = Term.Boolean true := by
            by_cases ha : a = Term.Stuck
            · subst a
              simp [__are_distinct_terms_type.eq_def] at hDistinct
            by_cases hb : b = Term.Stuck
            · subst b
              simp [__are_distinct_terms_type.eq_def] at hDistinct
            exact dt_ite_is_ok_self_true (by simpa [__are_distinct_terms_type.eq_def, ha, hb] using hDistinct)
          exact dt_distinct_terms_model_eval_eq_false_of_head_sound
            M hM a b haTrans hbTrans
            (fun e₁ e₂ hSmall he₁Trans he₂Trans hHeadEqFalse hHeadDistinct =>
              are_distinct_terms_type_model_eval_eq_false_of_type
                M hM (__eo_typeof e₁) e₁ e₂ he₁Trans he₂Trans
                hHeadEqFalse hHeadDistinct)
            hDtDistinct
  | Bool =>
      exact are_distinct_terms_type_primitive_model_eval_eq_false
        M a b Term.Bool hEqFalse hDistinct (by simp)
  | _ =>
      -- All other EO types use datatype spine distinctness.
      have hDtDistinct :
          __dt_distinct_terms a b = Term.Boolean true := by
        by_cases ha : a = Term.Stuck
        · subst a
          simp [__are_distinct_terms_type.eq_def] at hDistinct
        by_cases hb : b = Term.Stuck
        · subst b
          simp [__are_distinct_terms_type.eq_def] at hDistinct
        exact dt_ite_is_ok_self_true (by simpa [__are_distinct_terms_type.eq_def, ha, hb] using hDistinct)
      exact dt_distinct_terms_model_eval_eq_false_of_head_sound
        M hM a b haTrans hbTrans
        (fun e₁ e₂ hSmall he₁Trans he₂Trans hHeadEqFalse hHeadDistinct =>
          are_distinct_terms_type_model_eval_eq_false_of_type
            M hM (__eo_typeof e₁) e₁ e₂ he₁Trans he₂Trans
            hHeadEqFalse hHeadDistinct)
        hDtDistinct
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals try assumption
  all_goals simp_all
  all_goals try assumption
  all_goals omega
theorem are_distinct_terms_type_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M) (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_eq a b = Term.Boolean false ->
    __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans hEqFalse hDistinct
  exact are_distinct_terms_type_model_eval_eq_false_of_type
    M hM (__eo_typeof a) a b haTrans hbTrans hEqFalse hDistinct

theorem are_distinct_terms_type_model_eval_eq_false_of_any_type
    (M : SmtModel) (hM : model_wf M) (T a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_eq a b = Term.Boolean false ->
    __are_distinct_terms_type a b T = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  exact are_distinct_terms_type_model_eval_eq_false_of_type M hM T a b
