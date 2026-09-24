module

public import CpcMini.Proofs.TypePreservation.Base
import all CpcMini.Proofs.TypePreservation.Base

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Lemma about `typeof_map_value_shape`. -/
theorem typeof_map_value_shape :
    ∀ m : SmtMap,
      (∃ T U, __smtx_typeof_map_value m = SmtType.Map T U) ∨
        __smtx_typeof_map_value m = SmtType.None
  | SmtMap.default T e => Or.inl ⟨T, __smtx_typeof_value e, rfl⟩
  | SmtMap.cons i e m => by
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · simpa [__smtx_typeof_map_value, native_ite, hEq] using typeof_map_value_shape m
      · exact Or.inr (by simp [__smtx_typeof_map_value, native_ite, hEq])

/-- Lemma about `typeof_seq_value_shape`. -/
theorem typeof_seq_value_shape :
    ∀ ss : SmtSeq,
      (∃ T, __smtx_typeof_seq_value ss = SmtType.Seq T) ∨
        __smtx_typeof_seq_value ss = SmtType.None
  | SmtSeq.empty T => Or.inl ⟨T, rfl⟩
  | SmtSeq.cons v vs => by
      by_cases hEq : native_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · simpa [__smtx_typeof_seq_value, native_ite, hEq] using typeof_seq_value_shape vs
      · exact Or.inr (by simp [__smtx_typeof_seq_value, native_ite, hEq])

/-- Definition used in the proof development for `dt_cons_chain_result`. -/
def dt_cons_chain_result : SmtType -> Prop
  | SmtType.None => True
  | SmtType.Datatype _ _ => True
  | SmtType.DtcAppType _ U => dt_cons_chain_result U
  | _ => False

/-- Lemma about `typeof_dt_cons_value_rec_chain_result`. -/
theorem typeof_dt_cons_value_rec_chain_result
    (s : native_String)
    (d0 : SmtDatatypeDecl) :
    ∀ d n,
      dt_cons_chain_result (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d n)
  | SmtDatatype.null, n => by
      simp [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero => by
      simp [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero => by
      simpa [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_chain_result s d0 (SmtDatatype.sum c d) native_nat_zero
  | SmtDatatype.sum c d, native_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_chain_result s d0 d n

/-- Removes the datatype well-formedness guard from a non-`None` `dt_cons` value typing equality. -/
theorem typeof_value_dt_cons_inner_eq_of_eq_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    {U : SmtType}
    (h :
      __smtx_typeof_value (SmtValue.DtCons s d i) = U)
    (hU : U ≠ SmtType.None) :
    __smtx_typeof_dt_cons_value_rec
        (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i = U := by
  simpa [__smtx_typeof_value] using h

/-- Raw datatype constructor values always have constructor-chain result types. -/
theorem dt_cons_chain_result_of_dt_cons_value_type
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    {T : SmtType}
    (h : __smtx_typeof_value (SmtValue.DtCons s d i) = T) :
    dt_cons_chain_result T := by
  by_cases hT : T = SmtType.None
  · simp [dt_cons_chain_result, hT]
  · have hShape :=
      typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
    have hInner :
        __smtx_typeof_dt_cons_value_rec
            (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i = T :=
      typeof_value_dt_cons_inner_eq_of_eq_non_none h hT
    rw [hInner] at hShape
    exact hShape

/-- Lemma about datatype-constructor application chains. -/
theorem typeof_value_dt_cons_head_type_chain_result :
    ∀ v : SmtValue, ∀ T U : SmtType,
      (∃ s d i, __smtx_apply_head_value v = SmtValue.DtCons s d i) ->
      __smtx_typeof_value v = SmtType.DtcAppType T U -> dt_cons_chain_result U
  | SmtValue.NotValue, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Boolean _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Numeral _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Rational _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Binary _ _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Map _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Fun _ _ _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Set _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Seq _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Char _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.UValue _ _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.RegLan _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.DtCons s d i, T, U, hHead, h => by
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      have hInner :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i =
            SmtType.DtcAppType T U :=
        typeof_value_dt_cons_inner_eq_of_eq_non_none h (by simp)
      rw [hInner] at hShape
      simpa [dt_cons_chain_result] using hShape
  | SmtValue.Apply f v, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      have hHeadF : __smtx_apply_head_value f = SmtValue.DtCons s d i := by
        simpa [__smtx_apply_head_value] using hHead
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtcAppType A B =>
        cases hNone : native_Teq A SmtType.None <;>
        cases hEq : native_Teq A (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        have hShape :=
          typeof_value_dt_cons_head_type_chain_result f A B ⟨s, d, i, hHeadF⟩ hf
        simpa [h, dt_cons_chain_result] using hShape

/-- Values whose application head is a datatype constructor always have constructor-chain result types. -/
theorem typeof_value_dt_cons_head_chain_result :
    ∀ v : SmtValue, ∀ T : SmtType,
      (∃ s d i, __smtx_apply_head_value v = SmtValue.DtCons s d i) ->
      __smtx_typeof_value v = T -> dt_cons_chain_result T
  | SmtValue.NotValue, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Boolean _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Numeral _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Rational _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Binary _ _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Map _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Fun _ _ _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Set _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Seq _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Char _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.UValue _ _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.RegLan _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.DtCons s d i, T, hHead, h => by
      simpa using dt_cons_chain_result_of_dt_cons_value_type h
  | SmtValue.Apply f v, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      have hHeadF : __smtx_apply_head_value f = SmtValue.DtCons s d i := by
        simpa [__smtx_apply_head_value] using hHead
      change __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v) = T at h
      cases hf : __smtx_typeof_value f
      case None =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Bool =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Int =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Real =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case RegLan =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case BitVec n =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Map A B =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Set A =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Seq A =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Char =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Datatype s' d' =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case TypeRef s' =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case USort u =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case FunType A B =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case DtcAppType A B =>
        cases hNone : native_Teq A SmtType.None
        case false =>
          cases hEq : native_Teq A (__smtx_typeof_value v)
          case false =>
            have hNoneTy : SmtType.None = T := by
              simpa [hf, __smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hNone, hEq] using h
            cases hNoneTy
            simp [dt_cons_chain_result]
          case true =>
            have hBTy : B = T := by
              simpa [hf, __smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hNone, hEq] using h
            have hShape :=
              typeof_value_dt_cons_head_type_chain_result f A B ⟨s, d, i, hHeadF⟩ hf
            cases hBTy
            simpa [dt_cons_chain_result] using hShape
        case true =>
          have hNoneTy : SmtType.None = T := by
            simpa [hf, __smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hNone] using h
          cases hNoneTy
          simp [dt_cons_chain_result]

/-- Raw applications without datatype-constructor heads have type `none`. -/
theorem typeof_value_apply_of_head_ne_dt_cons :
    ∀ v i : SmtValue,
      (∀ s d n, __smtx_apply_head_value v ≠ SmtValue.DtCons s d n) ->
      __smtx_typeof_value (SmtValue.Apply v i) = SmtType.None
  | SmtValue.NotValue, i, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Boolean _, i, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Numeral _, i, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Rational _, i, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Binary w n, i, hDt => by
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, native_ite,
            SmtEval.native_and, hWidth, hMod]
  | SmtValue.Map m, i, hDt => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          change __smtx_typeof_apply_value (__smtx_typeof_map_value m) (__smtx_typeof_value i) = SmtType.None
          rw [hMap]
          simp [__smtx_typeof_apply_value]
      | inr hNone =>
          change __smtx_typeof_apply_value (__smtx_typeof_map_value m) (__smtx_typeof_value i) = SmtType.None
          rw [hNone]
          simp [__smtx_typeof_apply_value]
  | SmtValue.Fun fid A B, i, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Set m, i, hDt => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          change __smtx_typeof_apply_value (__smtx_map_to_set_type (__smtx_typeof_map_value m)) (__smtx_typeof_value i) = SmtType.None
          rw [hMap]
          cases U <;> simp [__smtx_map_to_set_type, __smtx_typeof_apply_value]
      | inr hNone =>
          change __smtx_typeof_apply_value (__smtx_map_to_set_type (__smtx_typeof_map_value m)) (__smtx_typeof_value i) = SmtType.None
          rw [hNone]
          simp [__smtx_map_to_set_type, __smtx_typeof_apply_value]
  | SmtValue.Seq ss, i, hDt => by
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          change __smtx_typeof_apply_value (__smtx_typeof_seq_value ss) (__smtx_typeof_value i) = SmtType.None
          rw [hSeq]
          simp [__smtx_typeof_apply_value]
      | inr hNone =>
          change __smtx_typeof_apply_value (__smtx_typeof_seq_value ss) (__smtx_typeof_value i) = SmtType.None
          rw [hNone]
          simp [__smtx_typeof_apply_value]
  | SmtValue.Char c, i, hDt => by
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, SmtEval.native_ite, hValid]
  | SmtValue.UValue _ _, i, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.RegLan _, i, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.DtCons s d n, i, hDt => by
      exact False.elim (hDt s d n rfl)
  | SmtValue.Apply f a, i, hDt => by
      have hDtF : ∀ s d n, __smtx_apply_head_value f ≠ SmtValue.DtCons s d n := by
        intro s d n hm
        exact hDt s d n (by simpa [__smtx_apply_head_value] using hm)
      have hNone :
          __smtx_typeof_value (SmtValue.Apply f a) = SmtType.None :=
        typeof_value_apply_of_head_ne_dt_cons f a hDtF
      change __smtx_typeof_apply_value (__smtx_typeof_value (SmtValue.Apply f a)) (__smtx_typeof_value i) = SmtType.None
      rw [hNone]
      simp [__smtx_typeof_apply_value]

/--
Proof bridge for the canonical-form lemmas. With the current unguarded value-level
`Apply` typing this is not derivable from `SmtModel`; it remains the open proof
obligation separating the proof skeleton from the reverted model semantics.
-/
theorem apply_value_non_chain_result_impossible
    {f x : SmtValue}
    {U : SmtType}
    (hU : ¬ dt_cons_chain_result U)
    (h : __smtx_typeof_value (SmtValue.Apply f x) = U) :
    False := by
  have hUNone : U ≠ SmtType.None := by
    intro hEq
    exact hU (by simp [dt_cons_chain_result, hEq])
  by_cases hDt : ∃ s d n, __smtx_apply_head_value f = SmtValue.DtCons s d n
  · rcases hDt with ⟨s, d, n, hHead⟩
    have hChain :
        dt_cons_chain_result U :=
      typeof_value_dt_cons_head_chain_result
        (SmtValue.Apply f x) U
        ⟨s, d, n, by simpa [__smtx_apply_head_value] using hHead⟩ h
    exact False.elim (hU hChain)
  · have hNone :
        __smtx_typeof_value (SmtValue.Apply f x) = SmtType.None :=
      typeof_value_apply_of_head_ne_dt_cons f x
        (by
          intro s d n hm
          exact hDt ⟨s, d, n, hm⟩)
    exact hUNone (by simpa [hNone] using h.symm)

/-- Lemma about `typeof_value_ne_type_ref`. -/
theorem typeof_value_ne_type_ref
    (s : native_String) :
    ∀ v : SmtValue, __smtx_typeof_value v ≠ SmtType.TypeRef s
  | SmtValue.NotValue => by
      simp [__smtx_typeof_value]
  | SmtValue.Boolean _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Numeral _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Rational _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Binary w n => by
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod]
  | SmtValue.Map m => by
      intro h
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Fun fid A B => by
      intro h
      simp [__smtx_typeof_value] at h
  | SmtValue.Set m => by
      intro h
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | SmtValue.Seq ss => by
      intro h
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Char c => by
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid]
  | SmtValue.UValue _ _ => by
      simp [__smtx_typeof_value]
  | SmtValue.RegLan _ => by
      simp [__smtx_typeof_value]
  | SmtValue.DtCons s' d i => by
      intro h
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | SmtValue.Apply f v => by
      intro h
      exact apply_value_non_chain_result_impossible
        (U := SmtType.TypeRef s) (by simp [dt_cons_chain_result]) h

/-- Derives `no_value` from `type_ref`. -/
theorem no_value_of_type_ref
    (s : native_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef s := by
  intro h
  rcases h with ⟨v, hv⟩
  exact typeof_value_ne_type_ref s v hv

/-- Canonical-form lemma for `bool_value`. -/
theorem bool_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Bool) :
    ∃ b : native_Bool, v = SmtValue.Boolean b := by
  cases v with
  | Boolean b =>
      exact ⟨b, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun fid A B =>
      exfalso
      simp [__smtx_typeof_value] at h
  | Set m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Bool) (by simp [dt_cons_chain_result]) h

/-- Canonical-form lemma for `int_value`. -/
theorem int_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Int) :
    ∃ n : native_Int, v = SmtValue.Numeral n := by
  cases v with
  | Numeral n =>
      exact ⟨n, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun fid A B =>
      exfalso
      simp [__smtx_typeof_value] at h
  | Set m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Int) (by simp [dt_cons_chain_result]) h

/-- Canonical-form lemma for `real_value`. -/
theorem real_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Real) :
    ∃ q : native_Rat, v = SmtValue.Rational q := by
  cases v with
  | Rational q =>
      exact ⟨q, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun fid A B =>
      exfalso
      simp [__smtx_typeof_value] at h
  | Set m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Real) (by simp [dt_cons_chain_result]) h

/-- Canonical-form lemma for `bitvec_value`. -/
theorem bitvec_value_canonical
    {v : SmtValue}
    {w : native_Nat}
    (h : __smtx_typeof_value v = SmtType.BitVec w) :
    ∃ n : native_Int, v = SmtValue.Binary (native_nat_to_int w) n := by
  cases v with
  | Binary w' n =>
      cases hWidth : native_zleq 0 w' <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w')) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
      have hw' : w' = native_nat_to_int w := by
        have hNonneg : 0 <= w' := by
          simpa [native_zleq, Smtm.native_zleq] using hWidth
        have hNat : native_int_to_nat w' = w := by
          cases h
          rfl
        have hInt : (Int.ofNat (Int.toNat w') : Int) = w' :=
          Int.toNat_of_nonneg hNonneg
        simp [native_int_to_nat, Smtm.native_int_to_nat] at hNat
        simp [hNat] at hInt
        exact hInt.symm
      subst hw'
      exact ⟨n, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun fid A B =>
      simp [__smtx_typeof_value] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.BitVec w) (by simp [dt_cons_chain_result]) h

/-- Lemma about `bitvec_width_nonneg`. -/
theorem bitvec_width_nonneg
    {w n : native_Int} {u : native_Nat}
    (h : __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec u) :
    native_zleq 0 w = true := by
  cases hWidth : native_zleq 0 w <;>
    cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  simp

/-- A well-typed bitvector value has a canonical payload for its width. -/
theorem bitvec_payload_canonical
    {w n : native_Int} {u : native_Nat}
    (h : __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec u) :
    native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
  cases hWidth : native_zleq 0 w <;>
    cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  simp

/-- A canonical bitvector payload is in range for its width. -/
theorem bitvec_payload_range_of_canonical
    {w n : native_Int}
    (hWidth : native_zleq 0 w = true)
    (hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    0 <= n ∧ n < native_int_pow2 w := by
  have hw : 0 <= w := by
    simpa [Smtm.native_zleq] using hWidth
  have hPowPos : 0 < native_int_pow2 w := by
    have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, hnot]
    exact Int.pow_pos (by decide)
  have hEq : n = native_mod_total n (native_int_pow2 w) := by
    simpa [SmtEval.native_zeq] using hMod
  constructor
  · rw [hEq]
    exact Int.emod_nonneg n (Int.ne_of_gt hPowPos)
  · rw [hEq]
    exact Int.emod_lt_of_pos n hPowPos

/-- Powers of two are monotone for nonnegative integer exponents. -/
theorem native_int_pow2_le_of_le_nonneg
    {a b : native_Int}
    (ha : 0 <= a)
    (hab : a <= b) :
    native_int_pow2 a <= native_int_pow2 b := by
  have hb : 0 <= b := Int.le_trans ha hab
  have hnotA : ¬ a < 0 := Int.not_lt_of_ge ha
  have hnotB : ¬ b < 0 := Int.not_lt_of_ge hb
  have hnat : Int.toNat a <= Int.toNat b :=
    Int.toNat_le_toNat hab
  have hpowNat : 2 ^ Int.toNat a <= 2 ^ Int.toNat b :=
    Nat.pow_le_pow_of_le (by decide) hnat
  have hpowInt :
      ((2 ^ Int.toNat a : Nat) : Int) <= ((2 ^ Int.toNat b : Nat) : Int) :=
    Int.ofNat_le.mpr hpowNat
  simpa [SmtEval.native_int_pow2, SmtEval.native_zexp_total, hnotA, hnotB] using hpowInt

/-- A payload canonical for width `w` remains canonical after zero-extension by `i`.
The extended width is written `i + w` rather than `native_zplus i w`: the sum is
of the Eunoia layer, which this file, standing over the model alone, does not
reach. The two are the same addition. -/
theorem bitvec_payload_canonical_zero_extend
    {i w n : native_Int}
    (hi0 : native_zleq 0 i = true)
    (hw0 : native_zleq 0 w = true)
    (hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    native_zeq n (native_mod_total n (native_int_pow2 (i + w))) = true := by
  have hi : 0 <= i := by
    simpa [Smtm.native_zleq] using hi0
  have hw : 0 <= w := by
    simpa [Smtm.native_zleq] using hw0
  have hRange := bitvec_payload_range_of_canonical hw0 hMod
  have hleWidth : w <= i + w := Int.le_add_of_nonneg_left hi
  have hpowLe : native_int_pow2 w <= native_int_pow2 (i + w) :=
    native_int_pow2_le_of_le_nonneg hw hleWidth
  have hltNew : n < native_int_pow2 (i + w) :=
    Int.lt_of_lt_of_le hRange.2 hpowLe
  have hEqNew : native_mod_total n (native_int_pow2 (i + w)) = n := by
    simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hRange.1 hltNew
  simp [SmtEval.native_zeq, hEqNew]

/-- Reducing a payload modulo a width makes it canonical for that width. -/
theorem native_mod_total_canonical
    (w n : native_Int) :
    native_zeq (native_mod_total n (native_int_pow2 w))
      (native_mod_total (native_mod_total n (native_int_pow2 w)) (native_int_pow2 w)) = true := by
  simp [SmtEval.native_zeq, SmtEval.native_mod_total]

/-- Derives `typeof_value_binary` from `nonneg`. -/
theorem typeof_value_binary_of_nonneg
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec (native_int_to_nat w) := by
  simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod]

/-- A bitvector value whose payload has just been reduced modulo its width is well-typed. -/
theorem typeof_value_binary_mod_of_nonneg
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __smtx_typeof_value (SmtValue.Binary w (native_mod_total n (native_int_pow2 w))) =
      SmtType.BitVec (native_int_to_nat w) := by
  have hMod :
      native_zeq (native_mod_total n (native_int_pow2 w))
        (native_mod_total (native_mod_total n (native_int_pow2 w)) (native_int_pow2 w)) = true := by
    exact native_mod_total_canonical w n
  exact typeof_value_binary_of_nonneg w (native_mod_total n (native_int_pow2 w)) hWidth hMod

/-- Canonical-form lemma for `fun_value`. -/
theorem fun_value_canonical
    {v : SmtValue}
    {A B : SmtType}
    (h : __smtx_typeof_value v = SmtType.FunType A B) :
    ∃ fid : native_String, v = SmtValue.Fun fid A B := by
  cases v with
  | Fun fid A' B' =>
      simp [__smtx_typeof_value] at h
      rcases h with ⟨hA, hB⟩
      cases hA
      cases hB
      exact ⟨fid, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          cases B' <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      have hInner :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i =
            SmtType.FunType A B :=
        typeof_value_dt_cons_inner_eq_of_eq_non_none h (by simp)
      rw [hInner] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.FunType A B) (by simp [dt_cons_chain_result]) h

/-- Canonical-form lemma for `map_value`. -/
theorem map_value_canonical
    {v : SmtValue}
    {A B : SmtType}
    (h : __smtx_typeof_value v = SmtType.Map A B) :
    ∃ m : SmtMap, v = SmtValue.Map m := by
  cases v with
  | Map m =>
      exact ⟨m, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Fun fid A' B' =>
      simp [__smtx_typeof_value] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          cases B' <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Map A B) (by simp [dt_cons_chain_result]) h

/-- Canonical-form lemma for `set_value`. -/
theorem set_value_canonical
    {v : SmtValue}
    {A : SmtType}
    (h : __smtx_typeof_value v = SmtType.Set A) :
    ∃ m : SmtMap, v = SmtValue.Set m := by
  cases v with
  | Set m =>
      exact ⟨m, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun fid A' B' =>
      simp [__smtx_typeof_value] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Set A) (by simp [dt_cons_chain_result]) h

/-- Lemma about `set_map_value_typed`. -/
theorem set_map_value_typed
    {m : SmtMap}
    {A : SmtType}
    (h : __smtx_typeof_value (SmtValue.Set m) = SmtType.Set A) :
    __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool := by
  cases typeof_map_value_shape m with
  | inl hMap =>
      rcases hMap with ⟨A', B', hMap⟩
      cases B' <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      case Bool =>
        cases h
        simp [hMap]
  | inr hNone =>
      simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h

/-- Derives `map_codomain_inhabited` from `map_value`. -/
theorem map_codomain_inhabited_of_map_value :
    ∀ {m : SmtMap} {A B : SmtType},
      __smtx_typeof_map_value m = SmtType.Map A B -> type_inhabited B
  | SmtMap.default T e, A, B, h => by
      cases h
      exact ⟨e, rfl⟩
  | SmtMap.cons i e m, A, B, h => by
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · simp [__smtx_typeof_map_value, native_ite, hEq] at h
        exact map_codomain_inhabited_of_map_value h
      · simp [__smtx_typeof_map_value, native_ite, hEq] at h

/-- Lemma about `map_codomain_inhabited`. -/
theorem map_codomain_inhabited
    {A B : SmtType}
    (h : type_inhabited (SmtType.Map A B)) :
    type_inhabited B := by
  rcases h with ⟨v, hv⟩
  rcases map_value_canonical (A := A) (B := B) hv with ⟨m, hm⟩
  cases hm
  simpa [__smtx_typeof_value] using
    map_codomain_inhabited_of_map_value (A := A) (B := B) hv

/-- Lemma about `not_type_inhabited_map`. -/
theorem not_type_inhabited_map
    {A B : SmtType}
    (hB : ¬ type_inhabited B) :
    ¬ type_inhabited (SmtType.Map A B) := by
  intro hMap
  exact hB (map_codomain_inhabited hMap)

/-- Canonical-form lemma for `seq_value`. -/
theorem seq_value_canonical
    {v : SmtValue}
    {T : SmtType}
    (h : __smtx_typeof_value v = SmtType.Seq T) :
    ∃ ss : SmtSeq, v = SmtValue.Seq ss := by
  cases v with
  | Seq ss =>
      exact ⟨ss, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun fid A B =>
      simp [__smtx_typeof_value] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Seq T) (by simp [dt_cons_chain_result]) h

/-- Canonical-form lemma for `char_value`. -/
def list_typed (T : SmtType) : List SmtValue -> Prop
  | [] => True
  | v :: vs => __smtx_typeof_value v = T ∧ list_typed T vs

/-- Derives `typeof_seq_value_pack_seq` from `typed`. -/
theorem typeof_seq_value_pack_seq_of_typed
    {T : SmtType} :
    ∀ {xs : List SmtValue},
      list_typed T xs ->
        __smtx_typeof_seq_value (native_pack_seq T xs) = SmtType.Seq T
  | [], hxs => by
      rfl
  | v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      have ih := typeof_seq_value_pack_seq_of_typed hxs
      simp [native_pack_seq, __smtx_typeof_seq_value, hv, ih, native_ite, native_Teq]

/-- Lemma about `char_value_list_typed`. -/
theorem char_value_list_typed_of_valid :
    ∀ {cs : List native_Char},
      native_string_valid cs = true ->
        list_typed SmtType.Char (cs.map SmtValue.Char)
  | [], _ => by
      simp [list_typed]
  | c :: cs, hValid => by
      simp [native_string_valid] at hValid
      rcases hValid with ⟨hc, hcs⟩
      have hcsValid : native_string_valid cs = true := by
        simpa [native_string_valid] using hcs
      exact ⟨by simp [__smtx_typeof_value, SmtEval.native_ite, hc],
        char_value_list_typed_of_valid hcsValid⟩

/-- Derives `char_values` from `string_typed`. -/
theorem char_values_of_string_typed
    (s : native_String)
    (hValid : native_string_valid s = true) :
    list_typed SmtType.Char (s.map SmtValue.Char) := by
  exact char_value_list_typed_of_valid hValid

/-- Lemma about `typeof_pack_string`. -/
theorem typeof_pack_string
    (s : native_String)
    (hValid : native_string_valid s = true) :
    __smtx_typeof_seq_value (native_pack_string s) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_seq_value (native_pack_seq SmtType.Char (s.map SmtValue.Char)) =
      SmtType.Seq SmtType.Char
  exact typeof_seq_value_pack_seq_of_typed (char_values_of_string_typed s hValid)

/-- Invalid strings pack to ill-typed SMT sequence values. -/
theorem typeof_pack_string_invalid :
    ∀ s : native_String,
      native_string_valid s = false ->
        __smtx_typeof_seq_value (native_pack_string s) = SmtType.None
  | [], hInvalid => by
      simp [native_string_valid] at hInvalid
  | c :: cs, hInvalid => by
      simp [native_string_valid] at hInvalid
      by_cases hc : native_char_valid c = true
      · have hcs : native_string_valid cs = false := by
          have hExists := hInvalid hc
          simpa [native_string_valid] using hExists
        have hTail := typeof_pack_string_invalid cs hcs
        change __smtx_typeof_seq_value
            (native_pack_seq SmtType.Char (SmtValue.Char c :: cs.map SmtValue.Char)) =
          SmtType.None
        change __smtx_typeof_seq_value (native_pack_seq SmtType.Char (cs.map SmtValue.Char)) =
          SmtType.None at hTail
        simp [native_pack_seq, __smtx_typeof_seq_value, __smtx_typeof_value,
          SmtEval.native_ite, hc, hTail, native_Teq]
      · have hcFalse : native_char_valid c = false := by
          cases hc' : native_char_valid c <;> simp [hc'] at hc ⊢
        change __smtx_typeof_seq_value
            (native_pack_seq SmtType.Char (SmtValue.Char c :: cs.map SmtValue.Char)) =
          SmtType.None
        cases hcs : native_string_valid cs
        · have hTail := typeof_pack_string_invalid cs hcs
          change __smtx_typeof_seq_value (native_pack_seq SmtType.Char (cs.map SmtValue.Char)) =
            SmtType.None at hTail
          simp [native_pack_seq, __smtx_typeof_seq_value, __smtx_typeof_value,
            SmtEval.native_ite, hcFalse, hTail, native_Teq]
        · have hTail := typeof_pack_string cs hcs
          change __smtx_typeof_seq_value (native_pack_seq SmtType.Char (cs.map SmtValue.Char)) =
            SmtType.Seq SmtType.Char at hTail
          simp [native_pack_seq, __smtx_typeof_seq_value, __smtx_typeof_value,
            SmtEval.native_ite, hcFalse, hTail, native_Teq]

/-- Shows that evaluating `string` terms produces values of the expected type. -/
theorem typeof_value_model_eval_string
    (M : SmtModel)
    (s : native_String) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.String s)) =
      __smtx_typeof (SmtTerm.String s) := by
  cases hValid : native_string_valid s
  · have hPack := typeof_pack_string_invalid s hValid
    rw [__smtx_model_eval.eq_4, __smtx_typeof.eq_4]
    simp [__smtx_typeof_value, SmtEval.native_ite, hValid, hPack]
  · have hPack := typeof_pack_string s hValid
    rw [__smtx_model_eval.eq_4, __smtx_typeof.eq_4]
    simp [__smtx_typeof_value, SmtEval.native_ite, hValid, hPack]

/-- Lemma about `map_lookup_typed`. -/
theorem map_lookup_typed :
    ∀ {m : SmtMap} {A B : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_typeof_value i = A ->
        __smtx_typeof_value (__smtx_map_lookup m i) = B
  | SmtMap.default T e, A, B, i, hMap, hi => by
      cases hMap
      simp [__smtx_map_lookup]
  | SmtMap.cons j e m, A, B, i, hMap, hi => by
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · have hm : __smtx_typeof_map_value m = SmtType.Map A B := by
          simpa [__smtx_typeof_map_value, native_ite, hEq] using hMap
        have hEq' :
            SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
              __smtx_typeof_map_value m := by
          simpa [native_Teq] using hEq
        have hHead : SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
            SmtType.Map A B := hEq'.trans hm
        have hj : __smtx_typeof_value j = A := by
          cases hHead
          rfl
        have he : __smtx_typeof_value e = B := by
          cases hHead
          rfl
        have hRec : __smtx_typeof_value (__smtx_map_lookup m i) = B :=
          map_lookup_typed hm hi
        by_cases hVeq : native_veq j i
        · simpa [__smtx_map_lookup, native_ite, hVeq] using he
        · simpa [__smtx_map_lookup, native_ite, hVeq] using hRec
      · simp [__smtx_typeof_map_value, native_ite, hEq] at hMap

/-- Shows that evaluating `eq_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_eq_value
    (M : SmtModel)
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_eq v1 v2) = SmtType.Bool := by
  cases v1 <;> cases v2
  case Seq.Seq ss1 ss2 =>
    cases ss1 <;> cases ss2 <;> simp [__smtx_model_eval_eq, __smtx_typeof_value]
  case Apply.Apply f1 a1 f2 a2 =>
    simp [__smtx_model_eval_eq, __smtx_typeof_value]
  case Fun.Fun fid1 A1 B1 fid2 A2 B2 =>
    simp [__smtx_model_eval_eq, __smtx_typeof_value]
  all_goals
    simp [__smtx_model_eval_eq, __smtx_typeof_value]

end Smtm
