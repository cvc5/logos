module

public import Cpc.Proofs.TypePreservation.Base
import all Cpc.SmtModel
import all Cpc.Proofs.TypePreservation.Common
import all Init.Data.Repr
import all Init.Data.Int.Repr

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/- Proof-side compatibility names for the regular-language smart constructors.
The model stores `SmtValue` atoms and exposes the smart constructors directly
under the non-`mk` names. -/
instance : Coe native_Char SmtValue where
  coe := SmtValue.Char

instance : Coe (List native_Char) (List SmtValue) where
  coe := impl_native_string_to_values

abbrev native_re_mk_concat := native_re_concat
abbrev native_re_mk_union := native_re_union
abbrev native_re_mk_inter := native_re_inter
abbrev native_re_mk_comp := native_re_comp
abbrev native_re_mk_star := native_re_mult
abbrev native_re_plus (r : SmtRegLan) :=
  native_re_concat r (native_re_mult r)

/- Legacy list-search primitives retained in the proof layer.  The executable
sequence operators now use the shared regular-expression matcher directly,
but several decomposition proofs still benefit from this structurally
recursive formulation. -/
def native_seq_prefix_eq : List SmtValue -> List SmtValue -> native_Bool
  | [], _ => true
  | _ :: _, [] => false
  | v1 :: vs1, v2 :: vs2 =>
      native_veq v1 v2 && native_seq_prefix_eq vs1 vs2

def native_seq_indexof_rec
    (xs pat : List SmtValue) (i fuel : Nat) : native_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if native_seq_prefix_eq pat xs then
        Int.ofNat i
      else
        match xs with
        | [] => -1
        | _ :: ys => native_seq_indexof_rec ys pat (i + 1) fuel

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
          simpa [native_zleq, SmtEval.native_zleq] using hWidth
        have hNat : native_int_to_nat w' = w := by
          cases h
          rfl
        have hInt : (Int.ofNat (Int.toNat w') : Int) = w' :=
          Int.toNat_of_nonneg hNonneg
        simp [native_int_to_nat, SmtEval.native_int_to_nat] at hNat
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
    simpa [SmtEval.native_zleq] using hWidth
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

/-- A payload canonical for width `w` remains canonical after zero-extension by `i`. -/
theorem bitvec_payload_canonical_zero_extend
    {i w n : native_Int}
    (hi0 : native_zleq 0 i = true)
    (hw0 : native_zleq 0 w = true)
    (hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    native_zeq n (native_mod_total n (native_int_pow2 (native_zplus i w))) = true := by
  have hi : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hw : 0 <= w := by
    simpa [SmtEval.native_zleq] using hw0
  have hRange := bitvec_payload_range_of_canonical hw0 hMod
  have hleWidth : w <= native_zplus i w := by
    simpa [SmtEval.native_zplus] using (Int.le_add_of_nonneg_left (a := w) hi)
  have hpowLe : native_int_pow2 w <= native_int_pow2 (native_zplus i w) :=
    native_int_pow2_le_of_le_nonneg hw hleWidth
  have hltNew : n < native_int_pow2 (native_zplus i w) :=
    Int.lt_of_lt_of_le hRange.2 hpowLe
  have hEqNew : native_mod_total n (native_int_pow2 (native_zplus i w)) = n := by
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
theorem char_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Char) :
    ∃ c : native_Char, v = SmtValue.Char c ∧ native_char_valid c = true := by
  cases v with
  | Char c =>
      cases hValid : native_char_valid c
      · simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at h
      · exact ⟨c, rfl, hValid⟩
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
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
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
        (U := SmtType.Char) (by simp [dt_cons_chain_result]) h

/-- Predicate asserting that every value in a list has the given SMT type. -/
def list_typed (T : SmtType) : List SmtValue -> Prop
  | [] => True
  | v :: vs => __smtx_typeof_value v = T ∧ list_typed T vs

/-- Lemma about `list_typed_append`. -/
theorem list_typed_append
    {T : SmtType} :
    ∀ {xs ys : List SmtValue},
      list_typed T xs ->
        list_typed T ys ->
        list_typed T (xs ++ ys)
  | [], ys, hxs, hys => by
      simpa [list_typed] using hys
  | v :: xs, ys, hxs, hys => by
      rcases hxs with ⟨hv, hxs⟩
      exact ⟨hv, list_typed_append hxs hys⟩

/-- Lemma about `list_typed_take`. -/
theorem list_typed_take
    {T : SmtType} :
    ∀ n {xs : List SmtValue},
      list_typed T xs ->
        list_typed T (xs.take n)
  | 0, xs, hxs => by
      simp [list_typed]
  | Nat.succ n, [], hxs => by
      simp [list_typed]
  | Nat.succ n, v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      exact ⟨hv, list_typed_take n hxs⟩

/-- Lemma about `list_typed_drop`. -/
theorem list_typed_drop
    {T : SmtType} :
    ∀ n {xs : List SmtValue},
      list_typed T xs ->
        list_typed T (xs.drop n)
  | 0, xs, hxs => by
      simpa using hxs
  | Nat.succ n, [], hxs => by
      simp [list_typed]
  | Nat.succ n, v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      simpa using list_typed_drop n hxs

/-- Lemma about `list_typed_reverse`. -/
theorem list_typed_reverse
    {T : SmtType} :
    ∀ {xs : List SmtValue},
      list_typed T xs ->
        list_typed T xs.reverse
  | [], hxs => by
      simp [list_typed]
  | v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      simpa [List.reverse_cons, list_typed, hv] using
        list_typed_append (list_typed_reverse hxs) (by simp [list_typed, hv])

/-- Lemma about `list_typed_extract`. -/
theorem list_typed_extract
    {T : SmtType}
    {xs : List SmtValue}
    (hxs : list_typed T xs)
    (i n : native_Int) :
    list_typed T (native_seq_extract xs i n) := by
  unfold native_seq_extract
  dsimp
  by_cases h :
      (decide (i < 0) || decide (n <= 0) || decide (i >= (↑xs.length : Int))) = true
  · rw [if_pos h]
    simp [list_typed]
  · rw [if_neg h]
    exact
      list_typed_take (Int.toNat (min n (Int.ofNat xs.length - i)))
        (list_typed_drop (Int.toNat i) hxs)

/-- Regex replacement preserves the element type of a value list. -/
theorem list_typed_replace_re
    {T : SmtType}
    {xs repl : List SmtValue}
    (r : SmtRegLan)
    (hxs : list_typed T xs)
    (hrepl : list_typed T repl) :
    list_typed T (native_str_replace_re xs r repl) := by
  unfold native_str_replace_re
  cases hFind : native_re_find_idx_from r xs 0 with
  | none =>
      simpa [hFind] using hxs
  | some found =>
      rcases found with ⟨idx, len⟩
      simpa [hFind, List.append_assoc] using
        (list_typed_append
          (list_typed_append (list_typed_take idx hxs) hrepl)
          (list_typed_drop (idx + len) hxs))

/-- Lemma about `list_typed_replace`. -/
theorem list_typed_replace
    {T : SmtType}
    {xs pat repl : List SmtValue}
    (hxs : list_typed T xs)
    (hrepl : list_typed T repl) :
    list_typed T (native_seq_replace xs pat repl) := by
  unfold native_seq_replace
  exact list_typed_replace_re (native_str_to_re pat) hxs hrepl

/-- Auxiliary lemma for `list_typed_replace_all`. -/
theorem list_typed_replace_all_aux
    {T : SmtType} :
    ∀ fuel (r : SmtRegLan) (repl : List SmtValue) {xs : List SmtValue},
      list_typed T repl ->
        list_typed T xs ->
        list_typed T (impl_native_re_replace_all_nonempty_list_aux fuel r repl xs)
  | 0, r, repl, xs, hrepl, hxs => by
      simpa [impl_native_re_replace_all_nonempty_list_aux] using hxs
  | Nat.succ fuel, r, repl, xs, hrepl, hxs => by
      cases hMatch : native_re_positive_prefix_match_len? r xs with
      | none =>
          cases xs with
          | nil => simp [impl_native_re_replace_all_nonempty_list_aux, hMatch, list_typed]
          | cons x xs =>
              rcases hxs with ⟨hx, hxs⟩
              simpa [impl_native_re_replace_all_nonempty_list_aux, hMatch, list_typed, hx] using
                list_typed_replace_all_aux fuel r repl hrepl hxs
      | some len =>
          cases len with
          | zero =>
              cases xs with
              | nil => simp [impl_native_re_replace_all_nonempty_list_aux, hMatch, list_typed]
              | cons x xs =>
                  rcases hxs with ⟨hx, hxs⟩
                  simpa [impl_native_re_replace_all_nonempty_list_aux, hMatch, list_typed, hx] using
                    list_typed_replace_all_aux fuel r repl hrepl hxs
          | succ len =>
              simpa [impl_native_re_replace_all_nonempty_list_aux, hMatch] using
                list_typed_append hrepl
                  (list_typed_replace_all_aux fuel r repl hrepl
                    (list_typed_drop (len + 1) hxs))

/-- Lemma about `list_typed_replace_all`. -/
theorem list_typed_replace_all
    {T : SmtType}
    {xs pat repl : List SmtValue}
    (hxs : list_typed T xs)
    (hrepl : list_typed T repl) :
    list_typed T (native_seq_replace_all xs pat repl) := by
  unfold native_seq_replace_all
  unfold native_str_replace_re_all impl_native_re_replace_all_nonempty_list
  exact list_typed_replace_all_aux (xs.length + 1) (native_str_to_re pat) repl hrepl hxs

/-- Regex replace-all preserves the element type of a value list. -/
theorem list_typed_replace_re_all
    {T : SmtType}
    {xs repl : List SmtValue}
    (r : SmtRegLan)
    (hxs : list_typed T xs)
    (hrepl : list_typed T repl) :
    list_typed T (native_str_replace_re_all xs r repl) := by
  unfold native_str_replace_re_all impl_native_re_replace_all_nonempty_list
  exact list_typed_replace_all_aux (xs.length + 1) r repl hrepl hxs

/-- Lemma about `list_typed_update`. -/
theorem list_typed_update
    {T : SmtType}
    {xs ys : List SmtValue}
    (hxs : list_typed T xs)
    (hys : list_typed T ys)
    (i : native_Int) :
    list_typed T (native_seq_update xs i ys) := by
  unfold native_seq_update
  dsimp
  by_cases h : (decide (i < 0) || decide ((↑xs.length : Int) <= i)) = true
  · rw [if_pos h]
    exact hxs
  · rw [if_neg h]
    simpa [List.append_assoc] using
      (list_typed_append
        (list_typed_append (list_typed_take (Int.toNat i) hxs)
          (list_typed_take (xs.length - Int.toNat i) hys))
        (list_typed_drop (Int.toNat i + ys.length) hxs))

/-- Derives `elem_typeof_seq_value` from `typeof_seq_value`. -/
theorem elem_typeof_seq_value_of_typeof_seq_value :
    ∀ {ss : SmtSeq} {T : SmtType},
      __smtx_typeof_seq_value ss = SmtType.Seq T ->
        __smtx_elem_typeof_seq_value ss = T
  | SmtSeq.empty U, T, h => by
      simpa [__smtx_typeof_seq_value, __smtx_elem_typeof_seq_value] using h
  | SmtSeq.cons v vs, T, h => by
      by_cases hEq : native_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · have hvs : __smtx_typeof_seq_value vs = SmtType.Seq T := by
          simpa [__smtx_typeof_seq_value, native_ite, hEq] using h
        simpa [__smtx_elem_typeof_seq_value] using
          (elem_typeof_seq_value_of_typeof_seq_value hvs)
      · simp [__smtx_typeof_seq_value, native_ite, hEq] at h

/-- Derives `typed_unpack_seq` from `typeof_seq_value`. -/
theorem typed_unpack_seq_of_typeof_seq_value :
    ∀ {ss : SmtSeq} {T : SmtType},
      __smtx_typeof_seq_value ss = SmtType.Seq T ->
        list_typed T (native_unpack_seq ss)
  | SmtSeq.empty U, T, h => by
      simp [native_unpack_seq, list_typed]
  | SmtSeq.cons v vs, T, h => by
      by_cases hEq : native_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · have hEq' : SmtType.Seq (__smtx_typeof_value v) = __smtx_typeof_seq_value vs := by
          simpa [native_Teq] using hEq
        have hvs : __smtx_typeof_seq_value vs = SmtType.Seq T := by
          simpa [__smtx_typeof_seq_value, native_ite, hEq] using h
        rw [hvs] at hEq'
        have hv : __smtx_typeof_value v = T := by
          cases hEq'
          rfl
        exact ⟨hv, typed_unpack_seq_of_typeof_seq_value hvs⟩
      · simp [__smtx_typeof_seq_value, native_ite, hEq] at h

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

/-- Consing a valid character onto a valid native string preserves validity. -/
theorem native_string_valid_cons
    {c : native_Char}
    (hc : native_char_valid c = true)
    {cs : native_String}
    (hcs : native_string_valid cs = true) :
    native_string_valid (c :: cs) = true := by
  rw [native_string_valid, List.all_eq_true] at hcs ⊢
  intro d hd
  cases hd with
  | head =>
      exact hc
  | tail _ hd =>
      exact hcs d hd

/-- A list typed as `Char` unpacks to a valid native string. -/
theorem native_string_valid_of_list_typed_char :
    ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs ->
        native_string_valid (xs.map impl_native_ssm_char_of_value) = true
  | [], _ => by
      simp [native_string_valid]
  | v :: vs, hxs => by
      rcases hxs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, hvc, hc⟩
      subst hvc
      have hTail := native_string_valid_of_list_typed_char hvs
      simpa [impl_native_ssm_char_of_value] using native_string_valid_cons hc hTail

/-- A sequence value typed as `Seq Char` unpacks to a valid native string. -/
theorem native_unpack_string_valid_of_typeof_seq_char
    {ss : SmtSeq}
    (h : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_string_valid (native_unpack_string ss) = true := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value h
  simpa [native_unpack_string] using native_string_valid_of_list_typed_char hTyped

/-- A sequence value typed as `Seq Char` unpacks to the value-level
embedding of its native string view. -/
theorem native_unpack_seq_eq_string_to_values_of_typeof_seq_char
    {ss : SmtSeq}
    (h : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_unpack_seq ss = impl_native_string_to_values (native_unpack_string ss) := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value h
  have hMap : ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs ->
        xs.map (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) = xs := by
    intro xs hxs
    induction xs with
    | nil => rfl
    | cons v vs ih =>
        rcases hxs with ⟨hv, hvs⟩
        rcases char_value_canonical hv with ⟨c, rfl, _hc⟩
        simpa [impl_native_ssm_char_of_value] using ih hvs
  unfold native_unpack_string impl_native_string_to_values
  simpa only [List.map_map, Function.comp_def] using (hMap hTyped).symm

/-- Appending valid native strings preserves validity. -/
theorem native_string_valid_append
    {xs ys : native_String}
    (hxs : native_string_valid xs = true)
    (hys : native_string_valid ys = true) :
    native_string_valid (xs ++ ys) = true := by
  rw [native_string_valid, List.all_eq_true] at hxs hys ⊢
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hxs c hc
  · exact hys c hc

/-- Taking a prefix of a valid native string preserves validity. -/
theorem native_string_valid_take
    (n : Nat)
    {xs : native_String}
    (hxs : native_string_valid xs = true) :
    native_string_valid (xs.take n) = true := by
  rw [native_string_valid, List.all_eq_true] at hxs ⊢
  intro c hc
  exact hxs c (List.mem_of_mem_take hc)

/-- Dropping a prefix of a valid native string preserves validity. -/
theorem native_string_valid_drop
    (n : Nat)
    {xs : native_String}
    (hxs : native_string_valid xs = true) :
    native_string_valid (xs.drop n) = true := by
  rw [native_string_valid, List.all_eq_true] at hxs ⊢
  intro c hc
  exact hxs c (List.mem_of_mem_drop hc)

/-- Mapping a validity-preserving character function over a native string preserves validity. -/
theorem native_string_valid_map
    (f : native_Char -> native_Char)
    (hf : ∀ c : native_Char, native_char_valid c = true ->
      native_char_valid (f c) = true)
    {s : native_String}
    (hs : native_string_valid s = true) :
    native_string_valid (s.map f) = true := by
  rw [native_string_valid, List.all_eq_true] at hs ⊢
  intro c hc
  rcases List.mem_map.mp hc with ⟨d, hd, hdc⟩
  subst hdc
  exact hf d (hs d hd)

/-- Lowercasing a valid SMT character preserves validity. -/
theorem native_char_valid_to_lower
    {c : native_Char}
    (hc : native_char_valid c = true) :
    native_char_valid (impl_native_char_to_lower c) = true := by
  have hcLt : c < 196608 := by
    simpa [native_char_valid] using hc
  cases hRange : (decide (65 ≤ c) && decide (c ≤ 90))
  · simp [impl_native_char_to_lower, hRange, native_char_valid, hcLt]
  · have hle90 : c ≤ 90 := by
      simp at hRange
      exact hRange.2
    simp [impl_native_char_to_lower, hRange, native_char_valid]
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hle90 32) (by decide)

/-- Uppercasing a valid SMT character preserves validity. -/
theorem native_char_valid_to_upper
    {c : native_Char}
    (hc : native_char_valid c = true) :
    native_char_valid (impl_native_char_to_upper c) = true := by
  have hcLt : c < 196608 := by
    simpa [native_char_valid] using hc
  cases hRange : (decide (97 ≤ c) && decide (c ≤ 122))
  · simp [impl_native_char_to_upper, hRange, native_char_valid, hcLt]
  · simp [impl_native_char_to_upper, hRange, native_char_valid]
    exact Nat.lt_of_le_of_lt (Nat.sub_le c 32) hcLt

/-- Lowercasing a valid native string preserves validity. -/
theorem native_str_to_lower_valid
    {s : native_String}
    (hs : native_string_valid s = true) :
    native_string_valid (native_str_to_lower s) = true := by
  unfold native_str_to_lower
  exact native_string_valid_map impl_native_char_to_lower
    (fun _ hc => native_char_valid_to_lower hc) hs

/-- Uppercasing a valid native string preserves validity. -/
theorem native_str_to_upper_valid
    {s : native_String}
    (hs : native_string_valid s = true) :
    native_string_valid (native_str_to_upper s) = true := by
  unfold native_str_to_upper
  exact native_string_valid_map impl_native_char_to_upper
    (fun _ hc => native_char_valid_to_upper hc) hs

/-- Regex replacement preserves character-sequence typing. -/
theorem native_str_replace_re_valid
    {s replacement : List SmtValue}
    (r : SmtRegLan)
    (hs : list_typed SmtType.Char s)
    (hreplacement : list_typed SmtType.Char replacement) :
    list_typed SmtType.Char (native_str_replace_re s r replacement) :=
  list_typed_replace_re r hs hreplacement

/-- Auxiliary character-sequence typing lemma for regex replace-all. -/
theorem native_re_replace_all_nonempty_list_aux_valid :
    ∀ fuel (r : SmtRegLan) (replacement : List SmtValue) {xs : List SmtValue},
      list_typed SmtType.Char replacement ->
        list_typed SmtType.Char xs ->
          list_typed SmtType.Char
            (impl_native_re_replace_all_nonempty_list_aux fuel r replacement xs) :=
  list_typed_replace_all_aux

/-- Regex replace-all preserves character-sequence typing. -/
theorem native_str_replace_re_all_valid
    {s replacement : List SmtValue}
    (r : SmtRegLan)
    (hs : list_typed SmtType.Char s)
    (hreplacement : list_typed SmtType.Char replacement) :
    list_typed SmtType.Char (native_str_replace_re_all s r replacement) :=
  list_typed_replace_re_all r hs hreplacement

/-- Character digits used by `Nat.toDigits` are valid SMT characters. -/
theorem native_char_valid_digitChar
    (n : Nat) :
    native_char_valid (Char.toNat (Nat.digitChar n)) = true := by
  unfold Nat.digitChar native_char_valid
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n = 1
    · simp [h1]
    · by_cases h2 : n = 2
      · simp [h2]
      · by_cases h3 : n = 3
        · simp [h3]
        · by_cases h4 : n = 4
          · simp [h4]
          · by_cases h5 : n = 5
            · simp [h5]
            · by_cases h6 : n = 6
              · simp [h6]
              · by_cases h7 : n = 7
                · simp [h7]
                · by_cases h8 : n = 8
                  · simp [h8]
                  · by_cases h9 : n = 9
                    · simp [h9]
                    · by_cases h10 : n = 10
                      · simp [h10]
                      · by_cases h11 : n = 11
                        · simp [h11]
                        · by_cases h12 : n = 12
                          · simp [
                              h12]
                          · by_cases h13 : n = 13
                            · simp [
                                h13]
                            · by_cases h14 : n = 14
                              · simp [
                                  h14]
                              · by_cases h15 : n = 15
                                · simp [
                                    h15]
                                · simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                                    h11, h12, h13, h14, h15]

/-- Consing a valid Lean character onto a valid native string literal preserves validity. -/
theorem native_string_valid_char_toNat_cons
    {c : Char}
    (hc : native_char_valid (Char.toNat c) = true)
    {cs : List Char}
    (hcs : native_string_valid (cs.map Char.toNat) = true) :
    native_string_valid ((c :: cs).map Char.toNat) = true := by
  simpa using native_string_valid_cons hc hcs

/-- `Nat.toDigitsCore` produces only valid SMT characters when the accumulator is valid. -/
theorem native_string_valid_toDigitsCore :
    ∀ fuel n ds,
      native_string_valid (ds.map Char.toNat) = true ->
        native_string_valid ((Nat.toDigitsCore 10 fuel n ds).map Char.toNat) = true
  | 0, n, ds, hds => by
      simpa [Nat.toDigitsCore.eq_1] using hds
  | fuel + 1, n, ds, hds => by
      rw [Nat.toDigitsCore.eq_2]
      by_cases hDiv : n / 10 = 0
      · rw [if_pos hDiv]
        exact native_string_valid_char_toNat_cons
          (native_char_valid_digitChar (n % 10)) hds
      · rw [if_neg hDiv]
        exact native_string_valid_toDigitsCore fuel (n / 10)
          ((Nat.digitChar (n % 10)) :: ds)
          (native_string_valid_char_toNat_cons
            (native_char_valid_digitChar (n % 10)) hds)

/-- String literals generated by `Nat.toString` are valid SMT strings. -/
theorem native_string_valid_nat_toString
    (n : Nat) :
    native_string_valid (native_string_lit (toString n)) = true := by
  unfold native_string_lit
  rw [show (toString n).toList = Nat.toDigits 10 n by
    rw [show (toString n) = n.repr by rfl]
    unfold Nat.repr
    rw [String.toList_ofList]]
  rw [Nat.toDigits.eq_1]
  exact native_string_valid_toDigitsCore (n + 1) n [] (by simp [native_string_valid])

/-- `str.from_code` produces valid native strings. -/
theorem native_str_from_code_valid
    (i : native_Int) :
    native_string_valid (native_str_from_code i) = true := by
  unfold native_str_from_code
  cases h : (decide (0 ≤ i) && native_char_valid (Int.toNat i))
  · simp [native_string_lit, native_string_valid]
  · have hChar : native_char_valid (Int.toNat i) = true := by
      simp at h
      exact h.2
    simp [native_string_valid, hChar]

/-- `str.from_int` produces valid native strings. -/
theorem native_str_from_int_valid
    (i : native_Int) :
    native_string_valid (native_str_from_int i) = true := by
  cases i with
  | ofNat n =>
      unfold native_str_from_int
      have hNot : ¬ ((Int.ofNat n) < 0) := by
        exact Int.not_lt_of_ge (Int.natCast_nonneg n)
      rw [if_neg hNot]
      simpa [Int.toString_eq_repr, Int.repr, Nat.toString_eq_repr] using
        native_string_valid_nat_toString n
  | negSucc n =>
      unfold native_str_from_int
      have hNeg : (Int.negSucc n) < 0 := by
        exact Int.negSucc_lt_zero n
      rw [if_pos hNeg]
      simp [native_string_lit, native_string_valid]

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

/-- Lemma about `map_store_typed`. -/
theorem map_store_typed
    {m : SmtMap}
    {A B : SmtType}
    {i e : SmtValue}
    (hMap : __smtx_typeof_map_value m = SmtType.Map A B)
    (hi : __smtx_typeof_value i = A)
    (he : __smtx_typeof_value e = B) :
    __smtx_typeof_value (SmtValue.Map (SmtMap.cons i e m)) = SmtType.Map A B := by
  simp [__smtx_typeof_value, __smtx_typeof_map_value, hMap, hi, he, native_ite, native_Teq]

/-- Lemma about the default value of a typed map. -/
theorem map_default_typed :
    ∀ {m : SmtMap} {A B : SmtType},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_typeof_value (__smtx_map_get_default m) = B
  | SmtMap.default T e, A, B, hMap => by
      cases hMap
      rfl
  | SmtMap.cons i e m, A, B, hMap => by
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · have hm : __smtx_typeof_map_value m = SmtType.Map A B := by
          simpa [__smtx_typeof_map_value, native_ite, hEq] using hMap
        simpa [__smtx_map_get_default] using map_default_typed hm
      · simp [__smtx_typeof_map_value, native_ite, hEq] at hMap

/-- Lemma about `__smtx_map_update_aux`. -/
private theorem map_update_aux_no_default_typed
    {m : SmtMap} {A B : SmtType} {d i e : SmtValue}
    (hMap : __smtx_typeof_map_value m = SmtType.Map A B)
    (hi : __smtx_typeof_value i = A)
    (he : __smtx_typeof_value e = B) :
    __smtx_typeof_map_value (__smtx_map_update_aux_no_default d m i e) =
      SmtType.Map A B := by
  by_cases hEq : native_veq d e = true
  · simp [__smtx_map_update_aux_no_default, hEq, native_ite, hMap]
  · have hEqFalse : native_veq d e = false := by
      cases hEqBool : native_veq d e <;> simp [hEqBool] at hEq ⊢
    simp [__smtx_map_update_aux_no_default, hEqFalse, native_ite,
      __smtx_typeof_map_value, hMap, hi, he, native_Teq]

private theorem map_update_aux_typed_explicit :
    ∀ (m : SmtMap) (A B : SmtType) (d i e : SmtValue),
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_typeof_value d = B ->
          __smtx_typeof_value i = A ->
            __smtx_typeof_value e = B ->
              __smtx_typeof_map_value (__smtx_map_update_aux d m i e) =
                SmtType.Map A B
  | SmtMap.default T ed, A, B, d, i, e, hMap, _hd, hi, he => by
      exact map_update_aux_no_default_typed hMap hi he
  | SmtMap.cons j e1 m, A, B, d, i, e, hMap, hd, hi, he => by
      by_cases hTyEq :
          native_Teq (SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e1))
            (__smtx_typeof_map_value m) = true
      · have hM : __smtx_typeof_map_value m = SmtType.Map A B := by
          simpa [__smtx_typeof_map_value, hTyEq, native_ite] using hMap
        have hHead :
            SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e1) =
              SmtType.Map A B := by
          have hEqMap :
              SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e1) =
                __smtx_typeof_map_value m := by
            simpa [native_Teq] using hTyEq
          exact hEqMap.trans hM
        have hj : __smtx_typeof_value j = A := by
          injection hHead with hIdx hVal
        have he1 : __smtx_typeof_value e1 = B := by
          injection hHead with hIdx hVal
        by_cases hJi : native_veq j i = true
        · simp [__smtx_map_update_aux, hJi, native_ite]
          exact map_update_aux_no_default_typed hM hi he
        · have hJiFalse : native_veq j i = false := by
            cases hJiBool : native_veq j i <;> simp [hJiBool] at hJi ⊢
          by_cases hCmp : native_vcmp j i = true
          · simp [__smtx_map_update_aux, hJiFalse, hCmp, native_ite]
            exact map_update_aux_no_default_typed hMap hi he
          · have hCmpFalse : native_vcmp j i = false := by
              cases hCmpBool : native_vcmp j i <;> simp [hCmpBool] at hCmp ⊢
            have hRest := map_update_aux_typed_explicit m A B d i e hM hd hi he
            simp [__smtx_map_update_aux, hJiFalse, hCmpFalse, native_ite,
              __smtx_typeof_map_value, hj, he1, hRest, native_Teq]
      · have hTyFalse :
            native_Teq (SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e1))
              (__smtx_typeof_map_value m) = false := by
          cases hTyBool :
              native_Teq (SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e1))
                (__smtx_typeof_map_value m) <;>
            simp [hTyBool] at hTyEq ⊢
        simp [__smtx_typeof_map_value, hTyFalse, native_ite] at hMap

theorem map_update_aux_typed :
    ∀ {m : SmtMap} {A B : SmtType} {d i e : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_typeof_value d = B ->
          __smtx_typeof_value i = A ->
            __smtx_typeof_value e = B ->
              __smtx_typeof_map_value (__smtx_map_update_aux d m i e) =
                SmtType.Map A B
  := by
    intro m A B d i e hMap hd hi he
    exact map_update_aux_typed_explicit m A B d i e hMap hd hi he

/-- Lemma about the update used by `map_store`. -/
theorem map_canon_insert_typed
    {m : SmtMap}
    {A B : SmtType}
    {i e : SmtValue}
    (hMap : __smtx_typeof_map_value m = SmtType.Map A B)
    (hi : __smtx_typeof_value i = A)
    (he : __smtx_typeof_value e = B) :
    __smtx_typeof_map_value (__smtx_map_update_aux (__smtx_map_get_default m) m i e) =
      SmtType.Map A B := by
  exact map_update_aux_typed (m := m) hMap (map_default_typed hMap) hi he

/-- Canonical-form lemma for `reglan_value`. -/
theorem reglan_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.RegLan) :
    ∃ r : SmtRegLan, v = SmtValue.RegLan r := by
  cases v with
  | RegLan r =>
      exact ⟨r, rfl⟩
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
  | Seq ss =>
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
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.RegLan) (by simp [dt_cons_chain_result]) h

/-- Derives `bool_binop_args_bool` from `non_none`. -/
theorem bool_binop_args_bool_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.Bool ∧ __smtx_typeof t2 = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, native_ite, native_Teq, h1, h2] at ht
  simp

/-- Derives `arith_binop_args` from `non_none`. -/
theorem arith_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2, h1, h2] at ht
  · simp
  · simp

/-- Derives `arith_binop_ret_bool_args` from `non_none`. -/
theorem arith_binop_ret_bool_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool)
    (ht : term_has_non_none_type (op t1 t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2_ret, h1, h2] at ht
  · simp
  · simp

/-- Derives `arith_binop_ret_args` from `non_none`. -/
theorem arith_binop_ret_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) R)
    (ht : term_has_non_none_type (op t1 t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2_ret, h1, h2] at ht
  · simp
  · simp

/-- Derives `arith_unop_arg` from `non_none`. -/
theorem arith_unop_arg_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_arith_overload_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, __smtx_typeof_arith_overload_op_1, h] at ht
  · simp
  · simp

/-- Derives `to_real_arg` from `non_none`. -/
theorem to_real_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.to_real t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  rw [__smtx_typeof.eq_21] at ht
  cases h : __smtx_typeof t <;>
    simp [native_ite, native_Teq, h] at ht
  rfl

/-- Derives `real_arg` from `non_none`. -/
theorem real_arg_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {Tout : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Real)
          Tout SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, native_ite, native_Teq, h] at ht
  simp

/-- Derives the overloaded arithmetic argument type for `abs` from `non_none`. -/
theorem abs_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.abs t)) :
    __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  rw [__smtx_typeof.eq_24] at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof_arith_overload_op_1, h] at ht
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Derives `int_arg` for an `abs` term whose result type is known to be `Int`. -/
theorem abs_int_arg_of_type_int
    {t : SmtTerm}
    (ht : __smtx_typeof (SmtTerm.abs t) = SmtType.Int) :
    __smtx_typeof t = SmtType.Int := by
  rw [__smtx_typeof.eq_24] at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof_arith_overload_op_1, h] at ht
  rfl

/-- Shows that evaluating `eq_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_eq_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_eq v1 v2) = SmtType.Bool := by
  cases v1 <;> cases v2
  case Seq.Seq ss1 ss2 =>
    cases ss1 <;> cases ss2 <;> simp [__smtx_model_eval_eq, __smtx_typeof_value]
  case Apply.Apply f1 a1 f2 a2 =>
    simp [__smtx_model_eval_eq, __smtx_typeof_value]
  all_goals
    simp [__smtx_model_eval_eq, __smtx_typeof_value]

/-- Shows that evaluating `xor_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_xor_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_xor v1 v2) = SmtType.Bool := by
  unfold __smtx_model_eval_xor
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v1 v2) with ⟨b, hb⟩
  rw [hb]
  rfl

end Smtm
