module

public import CpcMini.Proofs.TypePreservation.CoreArith
import all CpcMini.Proofs.TypePreservation.CoreArith
public import CpcMini.Proofs.TypePreservation.Datatypes
import all CpcMini.Proofs.TypePreservation.Datatypes

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

attribute [local simp] __smtx_type_wf_component

private theorem term_has_non_none_of_type_eq
    {t : SmtTerm} {T : SmtType}
    (h : __smtx_typeof t = T) (hT : T ≠ SmtType.None) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type
  rw [h]
  exact hT

private def mini_result_components_wf : SmtType -> Prop
  | SmtType.Seq A => __smtx_type_wf (SmtType.Seq A) = true
  | SmtType.Set A => __smtx_type_wf (SmtType.Set A) = true
  | SmtType.Datatype s d => __smtx_type_wf (SmtType.Datatype s d) = true
  | SmtType.Map A B => __smtx_type_wf (SmtType.Map A B) = true
  | SmtType.FunType A B => __smtx_type_wf (SmtType.FunType A B) = true
  | SmtType.DtcAppType _ B => mini_result_components_wf B
  | _ => True

private theorem mini_result_components_wf_native_ite
    (b : native_Bool) {T U : SmtType}
    (hT : mini_result_components_wf T)
    (hU : mini_result_components_wf U) :
    mini_result_components_wf (native_ite b T U) := by
  cases b <;> simpa [native_ite]

private theorem mini_result_components_wf_guard_wf_bool (T : SmtType) :
    mini_result_components_wf (__smtx_typeof_guard_wf T SmtType.Bool) := by
  unfold __smtx_typeof_guard_wf
  exact mini_result_components_wf_native_ite _ (by trivial) (by trivial)

private theorem mini_result_components_wf_of_type_wf
    {T : SmtType} (h : __smtx_type_wf T = true) :
    mini_result_components_wf T := by
  cases T <;>
    simp [mini_result_components_wf, __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and] at h ⊢
  all_goals exact h

private theorem mini_result_components_wf_dt_cons_rec
    (T : SmtType) (hT : mini_result_components_wf T) :
    ∀ (d : SmtDatatype) (i : native_Nat),
      mini_result_components_wf (__smtx_typeof_dt_cons_rec T d i)
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero => by
      simpa [__smtx_typeof_dt_cons_rec] using hT
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero => by
      simpa [__smtx_typeof_dt_cons_rec, mini_result_components_wf] using
        mini_result_components_wf_dt_cons_rec T hT
          (SmtDatatype.sum c d) native_nat_zero
  | SmtDatatype.sum c d, native_nat_succ i => by
      simpa [__smtx_typeof_dt_cons_rec] using
        mini_result_components_wf_dt_cons_rec T hT d i
  | SmtDatatype.null, i => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec, mini_result_components_wf]

private theorem mini_seq_char_wf :
    __smtx_type_wf (SmtType.Seq SmtType.Char) = true := by
  native_decide

private theorem mini_generic_apply_type_of_not_special
    {f x : SmtTerm}
    (hNoSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hNoTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  cases f <;> simp [__smtx_typeof]
  · exact False.elim (hNoSel _ _ _ _ rfl)
  · exact False.elim (hNoTester _ _ _ rfl)

private theorem mini_smt_term_result_components_wf_of_non_none
    (x : SmtTerm) (hxNN : term_has_non_none_type x) :
    mini_result_components_wf (__smtx_typeof x) := by
  let rec go (x : SmtTerm) (hxNN : term_has_non_none_type x) :
      mini_result_components_wf (__smtx_typeof x) := by
    cases x
    case String s =>
      cases hValid : native_string_valid s <;>
        simp [__smtx_typeof, native_ite, hValid, mini_result_components_wf,
          mini_seq_char_wf]
    case Var s T =>
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        simpa [term_has_non_none_type, __smtx_typeof] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      simpa [__smtx_typeof, smtx_typeof_guard_wf_of_non_none T T hGuardNN] using
        mini_result_components_wf_of_type_wf hWf
    case UConst s T =>
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        simpa [term_has_non_none_type, __smtx_typeof] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      simpa [__smtx_typeof, smtx_typeof_guard_wf_of_non_none T T hGuardNN] using
        mini_result_components_wf_of_type_wf hWf
    case ite c x y =>
      rcases ite_args_of_non_none hxNN with ⟨T, hc, hxT, hyT, hTNN⟩
      have hxGood := go x (term_has_non_none_of_type_eq hxT hTNN)
      rw [typeof_ite_eq]
      simp [__smtx_typeof_ite, native_ite, native_Teq, hc, hxT, hyT]
      simpa [hxT] using hxGood
    case choice s T body =>
      have hGuardTy :
          __smtx_typeof (SmtTerm.choice s T body) = __smtx_typeof_guard_wf T T :=
        choice_term_guard_type_of_non_none hxNN
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        rw [← hGuardTy]
        exact hxNN
      rw [choice_term_typeof_of_non_none hxNN]
      exact mini_result_components_wf_of_type_wf
        (smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN)
    case bind s T x1 x2 =>
      have hTyEq : __smtx_typeof (SmtTerm.bind s T x1 x2) = __smtx_typeof x2 :=
        bind_term_typeof_of_non_none hxNN
      rw [hTyEq]
      exact go x2 (by simpa [term_has_non_none_type, hTyEq] using hxNN)
    case DtCons s d i =>
      let raw :=
        __smtx_typeof_dt_cons_rec (SmtType.Datatype s d)
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      have hGuardNN : __smtx_typeof_guard_wf (SmtType.Datatype s d) raw ≠
          SmtType.None := by
        simpa [term_has_non_none_type, typeof_dt_cons_eq, raw] using hxNN
      rw [typeof_dt_cons_eq,
        smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN]
      exact mini_result_components_wf_dt_cons_rec (SmtType.Datatype s d)
        (mini_result_components_wf_of_type_wf
          (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN))
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
    case Apply f x =>
      by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
      · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
        let R := __smtx_ret_typeof_sel s d i j
        let inner :=
          __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R)
            (__smtx_typeof x)
        have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
          simpa [term_has_non_none_type, typeof_dt_sel_apply_eq, R, inner] using hxNN
        rw [dt_sel_term_typeof_of_non_none hxNN]
        exact mini_result_components_wf_of_type_wf
          (smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN)
      · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
        · rcases hTesterWitness with ⟨s, d, i, rfl⟩
          rw [dt_tester_term_typeof_of_non_none hxNN]
          simp [mini_result_components_wf]
        · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
            intro s d i j hEq
            exact hSelWitness ⟨s, d, i, j, hEq⟩
          have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
            intro s d i hEq
            exact hTesterWitness ⟨s, d, i, hEq⟩
          have hTy : generic_apply_type f x :=
            mini_generic_apply_type_of_not_special hSel hTester
          have hApplyNN :
              __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
                SmtType.None := by
            rw [← hTy]
            exact hxNN
          rcases typeof_apply_non_none_cases hApplyNN with
            ⟨A, B, hHead, hX, hA, _hB⟩
          have hfNN : term_has_non_none_type f := by
            unfold term_has_non_none_type
            rcases hHead with hF | hF <;> rw [hF] <;> simp
          have hfGood := go f hfNN
          have hApplyTy :
              __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) = B := by
            rcases hHead with hF | hF <;>
              simp [hF, hX, __smtx_typeof_apply, __smtx_typeof_guard,
                native_ite, native_Teq, hA]
          rw [hTy, hApplyTy]
          rcases hHead with hF | hF
          · have hHeadGood : __smtx_type_wf (SmtType.FunType A B) = true := by
              simpa [hF, mini_result_components_wf] using hfGood
            exact mini_result_components_wf_of_type_wf
              (fun_type_wf_components_of_wf hHeadGood).2
          · simpa [hF, mini_result_components_wf] using hfGood
    case Binary w n =>
      rw [__smtx_typeof.eq_def]
      exact mini_result_components_wf_native_ite _ (by trivial) (by trivial)
    case eq t1 t2 =>
      rw [__smtx_typeof.eq_def]
      unfold __smtx_typeof_eq __smtx_typeof_guard
      exact mini_result_components_wf_native_ite _ (by trivial)
        (mini_result_components_wf_native_ite _ (by trivial) (by trivial))
    case «exists» s T body =>
      rw [__smtx_typeof.eq_def]
      exact mini_result_components_wf_native_ite _
        (mini_result_components_wf_guard_wf_bool T) (by trivial)
    case «forall» s T body =>
      rw [__smtx_typeof.eq_def]
      exact mini_result_components_wf_native_ite _
        (mini_result_components_wf_guard_wf_bool T) (by trivial)
    case not t =>
      rw [__smtx_typeof.eq_def]
      exact mini_result_components_wf_native_ite _ (by trivial) (by trivial)
    case or t1 t2 =>
      rw [__smtx_typeof.eq_def]
      exact mini_result_components_wf_native_ite _
        (mini_result_components_wf_native_ite _ (by trivial) (by trivial)) (by trivial)
    case and t1 t2 =>
      rw [__smtx_typeof.eq_def]
      exact mini_result_components_wf_native_ite _
        (mini_result_components_wf_native_ite _ (by trivial) (by trivial)) (by trivial)
    case imp t1 t2 =>
      rw [__smtx_typeof.eq_def]
      exact mini_result_components_wf_native_ite _
        (mini_result_components_wf_native_ite _ (by trivial) (by trivial)) (by trivial)
    all_goals
      simp [mini_result_components_wf, __smtx_typeof]
  exact go x hxNN

private theorem mini_smt_fun_wf_of_non_none_type
    (x : SmtTerm) (A B : SmtType)
    (hxTy : __smtx_typeof x = SmtType.FunType A B) :
    __smtx_type_wf (SmtType.FunType A B) = true := by
  have h := mini_smt_term_result_components_wf_of_non_none x
    (term_has_non_none_of_type_eq hxTy (by simp))
  simpa [hxTy, mini_result_components_wf] using h

/-! ### Value-level canonicality helpers for `canonical_of_supported`. -/

/-- `NotValue` is (vacuously) canonical. -/
private theorem mini_value_canonical_notValue :
    value_canonical SmtValue.NotValue := by
  simp [value_canonical, __smtx_value_canonical]

/-- Boolean-typed values are canonical. -/
private theorem mini_value_canonical_of_bool_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Bool) :
    value_canonical v := by
  rcases bool_value_canonical h with ⟨b, rfl⟩
  simp [value_canonical, __smtx_value_canonical]

/-- Packing a valid string produces a canonical sequence value. -/
private theorem mini_seq_canonical_pack_string :
    ∀ s : native_String,
      native_string_valid s = true ->
        __smtx_seq_canonical (native_pack_string s) = true
  | [], _ => by
      simp [native_pack_string, native_pack_seq, __smtx_seq_canonical]
  | c :: cs, hValid => by
      have hParts : native_char_valid c = true ∧ native_string_valid cs = true := by
        simpa [native_string_valid, List.all_cons, Bool.and_eq_true] using hValid
      have hTail : __smtx_seq_canonical (native_pack_seq SmtType.Char (cs.map SmtValue.Char)) = true :=
        mini_seq_canonical_pack_string cs hParts.2
      show __smtx_seq_canonical
          (native_pack_seq SmtType.Char (SmtValue.Char c :: cs.map SmtValue.Char)) = true
      simp [native_pack_seq, __smtx_seq_canonical, __smtx_value_canonical,
        SmtEval.native_and, hParts.1, hTail]

/-- Value-level SMT `ite` preserves canonicality of the selected branch. -/
private theorem mini_model_eval_ite_canonical
    {c t e : SmtValue}
    (ht : value_canonical t)
    (he : value_canonical e) :
    value_canonical (__smtx_model_eval_ite c t e) := by
  cases c <;>
    try simpa [__smtx_model_eval_ite] using mini_value_canonical_notValue
  · cases ‹native_Bool› <;>
      simp [__smtx_model_eval_ite, ht, he]

/-- Value-level Boolean negation always returns a canonical value. -/
private theorem mini_model_eval_not_canonical (v : SmtValue) :
    value_canonical (__smtx_model_eval_not v) := by
  cases v <;>
    simp [__smtx_model_eval_not, value_canonical, __smtx_value_canonical]

/-- Value-level Boolean disjunction always returns a canonical value. -/
private theorem mini_model_eval_or_canonical (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_or v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_or, value_canonical, __smtx_value_canonical]

/-- Value-level Boolean conjunction always returns a canonical value. -/
private theorem mini_model_eval_and_canonical (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_and v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_and, value_canonical, __smtx_value_canonical]

/-- Value-level implication always returns a canonical value. -/
private theorem mini_model_eval_imp_canonical (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_imp v1 v2) := by
  simpa [__smtx_model_eval_imp] using
    mini_model_eval_or_canonical (__smtx_model_eval_not v1) v2

/-- Value-level SMT equality always returns a canonical Boolean value. -/
private theorem mini_model_eval_eq_canonical (v1 v2 : SmtValue) :
    value_canonical (__smtx_model_eval_eq v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_eq, value_canonical, __smtx_value_canonical]

/-- Choice evaluation always returns a canonical value. -/
private theorem mini_native_eval_tchoice_canonical
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm) :
    value_canonical (native_eval_choice M s T body) := by
  classical
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  · have hCan : value_canonical (Classical.choose hSat) := by
      simpa [value_canonical] using (Classical.choose_spec hSat).2.1
    simpa [hSat] using hCan
  · by_cases hTy :
        ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v
    · have hCan : value_canonical (Classical.choose hTy) := by
        simpa [value_canonical] using (Classical.choose_spec hTy).2
      simpa [hSat, hTy] using hCan
    · simpa [hSat, hTy] using mini_value_canonical_notValue

/-- Applying a function-typed value to an argument of the domain type yields a
canonical value. -/
private theorem mini_model_eval_apply_fun_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (fid : native_String)
    (A B : SmtType)
    (x : SmtValue)
    (hxTy : __smtx_typeof_value x = A)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true) :
    value_canonical (__smtx_model_eval_apply M (SmtValue.Fun fid A B) x) := by
  by_cases hxNot : x = SmtValue.NotValue
  · subst x
    simp [__smtx_model_eval_apply, value_canonical, __smtx_value_canonical]
  · have hCan : value_canonical (native_eval_fun_apply M fid A B x) := by
      have hRaw := (model_total_typed_native_fun_typed hM fid A B x hFunWF hxTy).2
      simpa [value_canonical] using hRaw
    have hApply :
        __smtx_model_eval_apply M (SmtValue.Fun fid A B) x =
          native_eval_fun_apply M fid A B x := by
      cases x <;> simp [__smtx_model_eval_apply] at hxNot ⊢
    simpa [hApply] using hCan

/-- Applying `NotValue` yields a canonical value. -/
private theorem mini_model_eval_apply_not_value_canonical
    (M : SmtModel) (x : SmtValue) :
    value_canonical (__smtx_model_eval_apply M SmtValue.NotValue x) := by
  cases x <;>
    simp [__smtx_model_eval_apply, value_canonical, __smtx_value_canonical]

/-- Applying a looked-up function-typed value yields a canonical value. -/
private theorem mini_model_eval_apply_lookup_fun_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (A B : SmtType)
    (x : SmtValue)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true)
    (hxTy : __smtx_typeof_value x = A) :
    value_canonical
      (__smtx_model_eval_apply M
        (native_model_lookup M s (SmtType.FunType A B)) x) := by
  have hLookupTy :
      __smtx_typeof_value (native_model_lookup M s (SmtType.FunType A B)) =
        SmtType.FunType A B :=
    model_total_typed_lookup hM s (SmtType.FunType A B) hFunWF
  rcases fun_value_canonical hLookupTy with ⟨fid, hLookupEq⟩
  rw [hLookupEq]
  exact mini_model_eval_apply_fun_canonical M hM fid A B x hxTy hFunWF

/-- Value-level generic application preserves canonicality. -/
private theorem mini_model_eval_apply_canonical
    (M : SmtModel)
    (hM : model_wf M)
    {f x : SmtValue}
    {A B : SmtType}
    (hHead :
      __smtx_typeof_value f = SmtType.FunType A B ∨
        __smtx_typeof_value f = SmtType.DtcAppType A B)
    (hFunWF :
      __smtx_typeof_value f = SmtType.FunType A B ->
        __smtx_type_wf (SmtType.FunType A B) = true)
    (hxTy : __smtx_typeof_value x = A)
    (hf : value_canonical f)
    (hx : value_canonical x) :
    value_canonical (__smtx_model_eval_apply M f x) := by
  cases hHead with
  | inl hFun =>
      rcases fun_value_canonical hFun with ⟨fid, rfl⟩
      exact mini_model_eval_apply_fun_canonical M hM fid A B x hxTy (hFunWF rfl)
  | inr hDtc =>
      cases f <;> cases x <;>
        simp [__smtx_model_eval_apply, __smtx_typeof_value,
          value_canonical, __smtx_value_canonical,
          SmtEval.native_and] at hDtc hf hx ⊢
      all_goals
        first
        | assumption
        | (constructor <;> assumption)

/-- Selecting the `n`-th applied argument of a canonical value yields a canonical value. -/
private theorem mini_vsm_apply_arg_nth_canonical :
    ∀ {v : SmtValue} {n npos : native_Nat},
      value_canonical v ->
        value_canonical (__smtx_apply_arg_nth_value v n npos)
  | SmtValue.Apply f a, n, npos, hv => by
      cases npos with
      | zero =>
          simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
      | succ npos =>
          have hf : value_canonical f := by
            have hParts := hv
            simp [value_canonical, __smtx_value_canonical,
              SmtEval.native_and] at hParts
            exact hParts.1
          have ha : value_canonical a := by
            have hParts := hv
            simp [value_canonical, __smtx_value_canonical,
              SmtEval.native_and] at hParts
            exact hParts.2
          cases hEq : native_nateq n npos
          · simpa [__smtx_apply_arg_nth_value, hEq, SmtEval.native_ite] using
              mini_vsm_apply_arg_nth_canonical hf
          · simpa [__smtx_apply_arg_nth_value, hEq, SmtEval.native_ite] using ha
  | SmtValue.NotValue, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Boolean b, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Numeral k, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Rational q, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Binary w k, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Map m, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Fun fid A B, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Set m, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Seq s, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.Char c, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.UValue u k, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.RegLan r, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue
  | SmtValue.DtCons s d i, n, npos, hv => by
      simpa [__smtx_apply_arg_nth_value] using mini_value_canonical_notValue

/-- The "wrong selector" fallback branch of `dt_sel` yields a canonical value. -/
private theorem mini_model_eval_dt_sel_wrong_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (n m : native_Nat)
    (v : SmtValue)
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))) = true)
    (hvTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    value_canonical
      (__smtx_model_eval_apply M
        (native_model_lookup M (native_wrong_apply_sel_id n m)
          (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))
        v) := by
  exact mini_model_eval_apply_lookup_fun_canonical M hM (native_wrong_apply_sel_id n m)
    (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m) v
    (dt_sel_wrong_fun_type_wf_of_map_wf s d n m hMapWF) hvTy

/-- Value-level `dt_sel` preserves canonicality. -/
private theorem mini_model_eval_dt_sel_canonical
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (n m : native_Nat)
    {v : SmtValue}
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))) = true)
    (hvTy : __smtx_typeof_value v = SmtType.Datatype s d)
    (hv : value_canonical v) :
    value_canonical (__smtx_model_eval_dt_sel M s d n m v) := by
  unfold __smtx_model_eval_dt_sel
  cases hEq : native_veq (__smtx_apply_head_value v) (SmtValue.DtCons s d n)
  · simpa [native_ite, hEq] using
      mini_model_eval_dt_sel_wrong_canonical M hM s d n m v hMapWF hvTy
  · simpa [native_ite, hEq] using
      mini_vsm_apply_arg_nth_canonical (v := v) (n := m)
        (npos := __smtx_dt_num_sels (__smtx_dd_lookup s d) n) hv

mutual

/-- Induction lemma proving type preservation for supported SMT terms in total typed models. -/
private theorem supported_type_preservation
    (M : SmtModel)
    (hM : model_wf M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  cases hs with
  | boolean b =>
      exact typeof_value_model_eval_boolean M b
  | numeral n =>
      exact typeof_value_model_eval_numeral M n
  | rational q =>
      exact typeof_value_model_eval_rational M q
  | string s =>
      exact typeof_value_model_eval_string M s
  | binary w n =>
      exact typeof_value_model_eval_binary M w n ht
  | var s T hT =>
      exact typeof_value_model_eval_var M hM s T hT ht
  | uconst s T hT =>
      exact typeof_value_model_eval_uconst M hM s T hT ht
  | ite htc hsc ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_ite M _ _ _ ht
        (supported_type_preservation M hM _ htc hsc)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «exists» s T body =>
      exact typeof_value_model_eval_exists M s T body ht
  | «forall» s T body =>
      exact typeof_value_model_eval_forall M s T body ht
  | choice s T body hChoice =>
      exact typeof_value_model_eval_choice M hM M s T body ht
  | bind s T x1 x2 hbt hs1 hs2 =>
      have ht1 : term_has_non_none_type x1 := bind_arg1_non_none_of_non_none ht
      have ht2 : term_has_non_none_type x2 := bind_arg2_non_none_of_non_none ht
      have hTx1 : __smtx_typeof x1 = T := bind_arg1_type_of_non_none ht
      have hWf : __smtx_type_wf T = true := bind_binder_type_wf_of_non_none ht
      have hx1ty : __smtx_typeof_value (__smtx_model_eval M x1) = __smtx_typeof x1 :=
        supported_type_preservation M hM x1 ht1 hs1
      have hx1canon : value_canonical (__smtx_model_eval M x1) :=
        canonical_of_supported M hM x1 ht1 hs1
      have hM' : model_wf (native_model_push M s T (__smtx_model_eval M x1)) :=
        model_total_typed_push hM s T (__smtx_model_eval M x1) hWf (hx1ty.trans hTx1) hx1canon
      exact typeof_value_model_eval_bind M s T x1 x2 ht
        (supported_type_preservation _ hM' x2 ht2 hs2)
  | «not» ht1 hs1 =>
      exact typeof_value_model_eval_not M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | «or» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_or M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «and» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_and M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «imp» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_imp M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | eq t1 t2 =>
      exact typeof_value_model_eval_eq M t1 t2 ht
  | dt_cons s d i =>
      exact typeof_value_model_eval_dt_cons M s d i ht
  | dt_sel ht1 hT hWrongMapWF htx hsx =>
      exact typeof_value_model_eval_dt_sel M hM _ _ _ _ _ ht1 hWrongMapWF hT
        (supported_type_preservation M hM _ htx hsx)
  | dt_tester s d i x =>
      exact typeof_value_model_eval_dt_tester M s d i x ht
  | @apply f x hTy hEval htf hsf htx hsx =>
      have hTy' :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTy']
        exact hNone
      rw [hEval M, hTy']
      have hFunWF :
          ∀ {A B : SmtType},
            __smtx_typeof f = SmtType.FunType A B ->
              __smtx_type_wf (SmtType.FunType A B) = true := by
        intro A B hFunTy
        exact mini_smt_fun_wf_of_non_none_type f A B hFunTy
      exact typeof_value_model_eval_apply_generic M hM f x hFunWF hNN
        (supported_type_preservation M hM f htf hsf)
        (supported_type_preservation M hM x htx hsx)

/-- Canonicity preservation for supported SMT terms in total typed models.  Runs
mutually with `supported_type_preservation` because the `bind` type-preservation
step needs the pushed model to remain `model_wf`, which in turn needs
canonicity of the bound value. -/
private theorem canonical_of_supported
    (M : SmtModel)
    (hM : model_wf M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    value_canonical (__smtx_model_eval M t) := by
  cases hs
  case bind s T x1 x2 hbt hs1 hs2 =>
      have ht1 : term_has_non_none_type x1 := bind_arg1_non_none_of_non_none ht
      have ht2 : term_has_non_none_type x2 := bind_arg2_non_none_of_non_none ht
      have hTx1 : __smtx_typeof x1 = T := bind_arg1_type_of_non_none ht
      have hWf : __smtx_type_wf T = true := bind_binder_type_wf_of_non_none ht
      have hx1ty : __smtx_typeof_value (__smtx_model_eval M x1) = __smtx_typeof x1 :=
        supported_type_preservation M hM x1 ht1 hs1
      have hx1canon : value_canonical (__smtx_model_eval M x1) :=
        canonical_of_supported M hM x1 ht1 hs1
      have hM' : model_wf (native_model_push M s T (__smtx_model_eval M x1)) :=
        model_total_typed_push hM s T (__smtx_model_eval M x1) hWf (hx1ty.trans hTx1) hx1canon
      rw [smtx_model_eval_bind_eq]
      exact canonical_of_supported _ hM' x2 ht2 hs2
  case boolean b =>
      simp [__smtx_model_eval, value_canonical, __smtx_value_canonical]
  case numeral n =>
      simp [__smtx_model_eval, value_canonical, __smtx_value_canonical]
  case rational q =>
      simp [__smtx_model_eval, value_canonical, __smtx_value_canonical]
  case string s =>
      have hsValid : native_string_valid s = true := by
        by_cases hV : native_string_valid s = true
        · exact hV
        · exfalso
          apply ht
          have hVF : native_string_valid s = false := by
            cases h : native_string_valid s <;> simp [h] at hV ⊢
          rw [__smtx_typeof.eq_4]
          simp [SmtEval.native_ite, hVF]
      have hCan : value_canonical (SmtValue.Seq (native_pack_string s)) := by
        simpa [value_canonical, __smtx_value_canonical] using
          mini_seq_canonical_pack_string s hsValid
      rw [__smtx_model_eval.eq_4]
      exact hCan
  case binary w n =>
      cases hw : native_zleq 0 w <;>
        cases hn : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_model_eval, __smtx_typeof, value_canonical,
            __smtx_value_canonical, term_has_non_none_type,
            native_and, SmtEval.native_and,
            native_ite, hw, hn] at ht ⊢
  case var s T hT =>
      have hWF : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T (by
          simpa [term_has_non_none_type, __smtx_typeof] using ht)
      simpa [__smtx_model_eval] using
        model_total_typed_var_lookup_canonical hM s T hWF
  case uconst s T hT =>
      have hWF : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T (by
          simpa [term_has_non_none_type, __smtx_typeof] using ht)
      simpa [__smtx_model_eval] using
        model_total_typed_lookup_canonical hM s T hWF
  case ite htc hsc ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_ite_canonical
          (c := __smtx_model_eval M _) (t := __smtx_model_eval M _)
          (e := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case «exists» s T body =>
      exact mini_value_canonical_of_bool_type
        ((typeof_value_model_eval_exists M s T body ht).trans
          (exists_term_typeof_of_non_none ht))
  case «forall» s T body =>
      exact mini_value_canonical_of_bool_type
        ((typeof_value_model_eval_forall M s T body ht).trans
          (forall_term_typeof_of_non_none ht))
  case choice s T body htc =>
      simpa [__smtx_model_eval] using mini_native_eval_tchoice_canonical M s T body
  case «not» ht1 hs1 =>
      simpa [__smtx_model_eval] using mini_model_eval_not_canonical (__smtx_model_eval M _)
  case «or» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_or_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «and» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_and_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «imp» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_imp_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case eq t1 t2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_eq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)
  case dt_cons s d i =>
      simp [__smtx_model_eval, value_canonical, __smtx_value_canonical]
  case dt_sel s d i j x htSel hT hWrongMapWF htx hsx =>
      have hxTy :=
        (supported_type_preservation M hM _ htx hsx).trans
          (dt_sel_arg_datatype_of_non_none htSel)
      simpa [__smtx_model_eval] using
        mini_model_eval_dt_sel_canonical M hM s d i j hWrongMapWF hxTy
          (canonical_of_supported M hM _ htx hsx)
  case dt_tester s d i x =>
      simp [__smtx_model_eval, __smtx_model_eval_dt_tester, value_canonical,
        __smtx_value_canonical]
  case apply f x hTyApp hEval htf hsf htx hsx =>
      have hf := canonical_of_supported M hM f htf hsf
      have hx := canonical_of_supported M hM x htx hsx
      have hTy' :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTyApp
        exact hTyApp
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTy']
        exact hNone
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHeadTerm, hX, hA, hB⟩
      have hPresF :
          __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
        supported_type_preservation M hM f htf hsf
      have hPresX :
          __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
        supported_type_preservation M hM x htx hsx
      have hxTy : __smtx_typeof_value (__smtx_model_eval M x) = A := by
        simpa [hX] using hPresX
      have hHeadVal :
          __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B ∨
            __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
        cases hHeadTerm with
        | inl hFun => exact Or.inl (by simpa [hFun] using hPresF)
        | inr hDtc => exact Or.inr (by simpa [hDtc] using hPresF)
      have hFunWF :
          __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B ->
            __smtx_type_wf (SmtType.FunType A B) = true := by
        intro hValFun
        cases hHeadTerm with
        | inl hFun => exact mini_smt_fun_wf_of_non_none_type f A B hFun
        | inr hDtc =>
            have hValDtc :
                __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
              simpa [hDtc] using hPresF
            rw [hValFun] at hValDtc
            cases hValDtc
      simpa [hEval M] using
        mini_model_eval_apply_canonical M hM
          (f := __smtx_model_eval M f)
          (x := __smtx_model_eval M x)
          (hHead := hHeadVal)
          (hFunWF := hFunWF)
          (hxTy := hxTy)
          hf hx

end

theorem generic_apply_subterms_non_none
    {f x : SmtTerm}
    (hTy : generic_apply_type f x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x)) :
    term_has_non_none_type f ∧ term_has_non_none_type x := by
  have hApply : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    unfold generic_apply_type at hTy
    unfold term_has_non_none_type at ht
    rw [hTy] at ht
    exact ht
  rcases typeof_apply_non_none_cases hApply with ⟨A, B, hF, hX, hA, hB⟩
  constructor
  · unfold term_has_non_none_type
    rcases hF with hF | hF <;> rw [hF] <;> simp
  · unfold term_has_non_none_type
    rw [hX]
    exact hA

private theorem tp_dt_cons_wf_rec_tail_of_true
    {dd : SmtDatatypeDecl} {T : SmtType} {c : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec dd (SmtDatatypeCons.cons T c) = true) :
    __smtx_dt_cons_wf_rec dd c = true := by
  cases T <;>
    simp only [__smtx_dt_cons_wf_rec, native_and, Bool.and_eq_true] at h <;>
    exact h.2

private theorem tp_dt_wf_cons_of_wf
    {dd : SmtDatatypeDecl} {c : SmtDatatypeCons} {d : SmtDatatype}
    (h : __smtx_dt_wf_rec dd (SmtDatatype.sum c d) = true) :
    __smtx_dt_cons_wf_rec dd c = true := by
  simp only [__smtx_dt_wf_rec, native_and, Bool.and_eq_true] at h
  exact h.1

private theorem tp_dt_wf_tail_of_nonempty_tail_wf
    {dd : SmtDatatypeDecl} {c cTail : SmtDatatypeCons} {dTail : SmtDatatype}
    (h : __smtx_dt_wf_rec dd
      (SmtDatatype.sum c (SmtDatatype.sum cTail dTail)) = true) :
    __smtx_dt_wf_rec dd (SmtDatatype.sum cTail dTail) = true := by
  simp only [__smtx_dt_wf_rec, native_and, Bool.and_eq_true] at h
  simpa [__smtx_dt_wf_rec, native_and] using h.2

private theorem tp_ret_typeof_sel_rec_resolve_ne_reglan_of_cons_wf
    (dd : SmtDatatypeDecl) :
    ∀ (c : SmtDatatypeCons) (d : SmtDatatype) (j : native_Nat),
      __smtx_dt_cons_wf_rec dd c = true →
        __smtx_ret_typeof_sel_rec
            (SmtDatatype.sum (__smtx_dtc_resolve c dd)
              (__smtx_dt_resolve d dd)) native_nat_zero j ≠ SmtType.RegLan
  | SmtDatatypeCons.unit, d, j, _ => by
      cases j <;> simp [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec]
  | SmtDatatypeCons.cons T c, d, native_nat_zero, h => by
      cases T <;>
        simp [__smtx_dtc_resolve, __smtx_dt_cons_wf_rec,
          __smtx_type_wf_rec, __smtx_ret_typeof_sel_rec, native_and] at h ⊢
  | SmtDatatypeCons.cons T c, d, native_nat_succ j, h => by
      have hTail : __smtx_dt_cons_wf_rec dd c = true :=
        tp_dt_cons_wf_rec_tail_of_true h
      cases T <;>
        simpa [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec] using
          tp_ret_typeof_sel_rec_resolve_ne_reglan_of_cons_wf dd c d j hTail

private theorem tp_ret_typeof_sel_rec_resolve_ne_reglan_of_dt_wf
    (dd : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (i j : native_Nat),
      __smtx_dt_wf_rec dd d = true →
        __smtx_ret_typeof_sel_rec (__smtx_dt_resolve d dd) i j ≠ SmtType.RegLan
  | SmtDatatype.null, i, j, _ => by
      cases i <;> cases j <;> simp [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec]
  | SmtDatatype.sum c d, native_nat_zero, j, h => by
      have hCons := tp_dt_wf_cons_of_wf h
      simpa [__smtx_dt_resolve] using
        tp_ret_typeof_sel_rec_resolve_ne_reglan_of_cons_wf dd c d j hCons
  | SmtDatatype.sum c d, native_nat_succ i, j, h => by
      cases d with
      | null => simp [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec]
      | sum cTail dTail =>
          have hTail := tp_dt_wf_tail_of_nonempty_tail_wf h
          simpa [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec] using
            tp_ret_typeof_sel_rec_resolve_ne_reglan_of_dt_wf dd
              (SmtDatatype.sum cTail dTail) i j hTail

private theorem tp_ret_typeof_sel_ne_reglan_of_datatype_wf
    {s : native_String} {d : SmtDatatypeDecl} {i j : native_Nat}
    (hWf : __smtx_type_wf (SmtType.Datatype s d) = true) :
    __smtx_ret_typeof_sel s d i j ≠ SmtType.RegLan := by
  have hDtWf : __smtx_dt_wf_rec d (__smtx_dd_lookup s d) = true :=
    datatype_wf_rec_of_type_wf hWf
  simpa [__smtx_ret_typeof_sel] using
    tp_ret_typeof_sel_rec_resolve_ne_reglan_of_dt_wf
      d (__smtx_dd_lookup s d) i j hDtWf

private theorem tp_ret_typeof_sel_rec_resolve_ne_funtype_of_cons_wf
    (dd : SmtDatatypeDecl) :
    ∀ (c : SmtDatatypeCons) (d : SmtDatatype) (j : native_Nat),
      __smtx_dt_cons_wf_rec dd c = true → ∀ A B : SmtType,
        __smtx_ret_typeof_sel_rec
            (SmtDatatype.sum (__smtx_dtc_resolve c dd)
              (__smtx_dt_resolve d dd)) native_nat_zero j ≠ SmtType.FunType A B
  | SmtDatatypeCons.unit, d, j, _ => by
      intro A B; cases j <;> simp [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec]
  | SmtDatatypeCons.cons T c, d, native_nat_zero, h => by
      intro A B
      cases T <;>
        simp [__smtx_dtc_resolve, __smtx_dt_cons_wf_rec,
          __smtx_type_wf_rec, __smtx_ret_typeof_sel_rec, native_and] at h ⊢
  | SmtDatatypeCons.cons T c, d, native_nat_succ j, h => by
      have hTail : __smtx_dt_cons_wf_rec dd c = true :=
        tp_dt_cons_wf_rec_tail_of_true h
      cases T <;>
        simpa [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec] using
          tp_ret_typeof_sel_rec_resolve_ne_funtype_of_cons_wf dd c d j hTail

private theorem tp_ret_typeof_sel_rec_resolve_ne_funtype_of_dt_wf
    (dd : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (i j : native_Nat),
      __smtx_dt_wf_rec dd d = true → ∀ A B : SmtType,
        __smtx_ret_typeof_sel_rec (__smtx_dt_resolve d dd) i j ≠ SmtType.FunType A B
  | SmtDatatype.null, i, j, _ => by
      intro A B; cases i <;> cases j <;>
        simp [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec]
  | SmtDatatype.sum c d, native_nat_zero, j, h => by
      have hCons := tp_dt_wf_cons_of_wf h
      simpa [__smtx_dt_resolve] using
        tp_ret_typeof_sel_rec_resolve_ne_funtype_of_cons_wf dd c d j hCons
  | SmtDatatype.sum c d, native_nat_succ i, j, h => by
      cases d with
      | null => intro A B; simp [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec]
      | sum cTail dTail =>
          have hTail := tp_dt_wf_tail_of_nonempty_tail_wf h
          simpa [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec] using
            tp_ret_typeof_sel_rec_resolve_ne_funtype_of_dt_wf dd
              (SmtDatatype.sum cTail dTail) i j hTail

private theorem tp_ret_typeof_sel_ne_funtype_of_datatype_wf
    {s : native_String} {d : SmtDatatypeDecl} {i j : native_Nat}
    (hWf : __smtx_type_wf (SmtType.Datatype s d) = true) :
    ∀ A B : SmtType, __smtx_ret_typeof_sel s d i j ≠ SmtType.FunType A B := by
  have hDtWf : __smtx_dt_wf_rec d (__smtx_dd_lookup s d) = true :=
    datatype_wf_rec_of_type_wf hWf
  simpa [__smtx_ret_typeof_sel] using
    tp_ret_typeof_sel_rec_resolve_ne_funtype_of_dt_wf
      d (__smtx_dd_lookup s d) i j hDtWf

private theorem tp_type_wf_parts_of_wf_ne_reglan
    {T : SmtType}
    (hWf : __smtx_type_wf T = true)
    (hNe : T ≠ SmtType.RegLan)
    (hNeFun : ∀ A B : SmtType, T ≠ SmtType.FunType A B) :
    native_inhabited_type T = true ∧
      __smtx_type_wf_rec T = true := by
  cases T <;> simp [__smtx_type_wf, native_and] at hWf hNe ⊢
  case FunType A B =>
    exact False.elim (hNeFun A B rfl)
  all_goals first | contradiction | exact hWf | exact hWf.1 | exact ⟨hWf, rfl⟩ | exact ⟨hWf.1, rfl⟩

private theorem tp_map_type_inhabited
    {A B : SmtType}
    (hB : type_inhabited B) :
    type_inhabited (SmtType.Map A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Map (SmtMap.default A v), by
    simp [__smtx_typeof_value, __smtx_typeof_map_value, hv]⟩

/-- Derives inhabitedness of the selector result type from a non-`None` selector term. -/
theorem dt_sel_term_inhabited_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner :=
    __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R)
      (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_dt_sel_apply_eq] at ht
    simpa [R, inner] using ht
  have hInh : type_inhabited R :=
    smtx_typeof_guard_wf_inhabited_of_non_none R inner hGuardNN
  rw [dt_sel_term_typeof_of_non_none ht]
  exact hInh

/-- The model fallback used for wrong datatype-selector applications is well-formed. -/
theorem dt_sel_wrong_map_type_wf_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    __smtx_type_wf
      (SmtType.Map SmtType.Int
        (SmtType.Map SmtType.Int
          (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true := by
  let R := __smtx_ret_typeof_sel s d i j
  let D := SmtType.Datatype s d
  let M3 := SmtType.Map D R
  let M2 := SmtType.Map SmtType.Int M3
  let M1 := SmtType.Map SmtType.Int M2
  have hxTy : __smtx_typeof x = D := by
    simpa [D] using dt_sel_arg_datatype_of_non_none ht
  have hDTWf : __smtx_type_wf D = true := by
    have hGood := mini_smt_term_result_components_wf_of_non_none x
      (term_has_non_none_of_type_eq hxTy (by simp [D]))
    simpa [D, hxTy, mini_result_components_wf] using hGood
  let inner :=
    __smtx_typeof_apply (SmtType.FunType D R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_dt_sel_apply_eq] at ht
    simpa [R, D, inner] using ht
  have hRWf : __smtx_type_wf R = true :=
    smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
  have hRNe : R ≠ SmtType.RegLan := by
    simpa [R, D] using
      tp_ret_typeof_sel_ne_reglan_of_datatype_wf
        (s := s) (d := d) (i := i) (j := j) hDTWf
  have hRNeFun : ∀ A B : SmtType, R ≠ SmtType.FunType A B := by
    intro A B
    simpa [R, D] using
      tp_ret_typeof_sel_ne_funtype_of_datatype_wf
        (s := s) (d := d) (i := i) (j := j) hDTWf A B
  have hRParts :
      native_inhabited_type R = true ∧ __smtx_type_wf_rec R = true :=
    tp_type_wf_parts_of_wf_ne_reglan hRWf hRNe hRNeFun
  have hDTParts :
      native_inhabited_type D = true ∧ __smtx_type_wf_rec D = true :=
    tp_type_wf_parts_of_wf_ne_reglan hDTWf (by simp [D]) (by
      intro A B h
      simp [D] at h)
  have hM3Inh : native_inhabited_type M3 = true :=
    native_inhabited_type_map hRParts.1
  have hM3Rec : __smtx_type_wf_rec M3 = true := by
    simp [M3, __smtx_type_wf_rec, native_and, hDTParts.1,
      hDTParts.2, hRParts.1, hRParts.2]
  have hM2Inh : native_inhabited_type M2 = true :=
    native_inhabited_type_map hM3Inh
  have hM2Rec : __smtx_type_wf_rec M2 = true := by
    simp [M2, __smtx_type_wf_rec, native_and, hM3Inh, hM3Rec]
  have hM1Inh : native_inhabited_type M1 = true :=
    native_inhabited_type_map hM2Inh
  have hM1Rec : __smtx_type_wf_rec M1 = true := by
    simp [M1, __smtx_type_wf_rec, native_and, hM2Inh, hM2Rec]
  simpa [M1, M2, M3, D, R] using
    type_wf_of_inhabited_and_wf_rec hM1Inh hM1Rec

/-- Packages the generic-application constructor once the recursive support facts are available. -/
theorem supported_generic_apply_of_non_none
    {f x : SmtTerm}
    (hTy : generic_apply_type f x)
    (hEval : generic_apply_eval f x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hsf : supported_preservation_term f)
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply f x) := by
  have hArgs := generic_apply_subterms_non_none hTy ht
  exact supported_preservation_term.apply hTy hEval hArgs.1 hsf hArgs.2 hsx

/-- Generic application facts for heads other than datatype selectors/testers. -/
theorem generic_apply_facts_of_not_special
    {f x : SmtTerm}
    (hNoSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hNoTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x ∧ generic_apply_eval f x := by
  constructor
  · unfold generic_apply_type
    cases f <;> simp [__smtx_typeof]
    · exact False.elim (hNoSel _ _ _ _ rfl)
    · exact False.elim (hNoTester _ _ _ rfl)
  · intro M
    cases f with
    | DtSel s d i j =>
        exact False.elim (hNoSel s d i j rfl)
    | DtTester s d i =>
        exact False.elim (hNoTester s d i rfl)
    | _ =>
        simp [__smtx_model_eval]

/-- Every non-`None` SMT term lies in the supported preservation fragment. -/
theorem supported_preservation_term_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> supported_preservation_term t := by
  let rec go (t : SmtTerm) (ht : term_has_non_none_type t) : supported_preservation_term t := by
    match t with
    | SmtTerm.None =>
        have hNone : __smtx_typeof SmtTerm.None = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.Boolean b =>
        exact supported_preservation_term.boolean b
    | SmtTerm.Numeral n =>
        exact supported_preservation_term.numeral n
    | SmtTerm.Rational q =>
        exact supported_preservation_term.rational q
    | SmtTerm.String s =>
        exact supported_preservation_term.string s
    | SmtTerm.Binary w n =>
        exact supported_preservation_term.binary w n
    | SmtTerm.Var s T =>
        have hTNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          intro hNone
          apply ht
          simpa [__smtx_typeof] using hNone
        exact supported_preservation_term.var s T
          (smtx_typeof_guard_wf_inhabited_of_non_none T T hTNN)
    | SmtTerm.ite c t1 t2 =>
        rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
        have htc : term_has_non_none_type c := by
          unfold term_has_non_none_type
          rw [hc]
          simp
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [h1]
          exact hT
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [h2]
          exact hT
        exact supported_preservation_term.ite
          htc (go c htc) ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.eq t1 t2 =>
        exact supported_preservation_term.eq t1 t2
    | SmtTerm.exists s T body =>
        exact supported_preservation_term.exists s T body
    | SmtTerm.forall s T body =>
        exact supported_preservation_term.forall s T body
    | SmtTerm.choice s T body =>
        exact supported_preservation_term.choice s T body ht
    | SmtTerm.bind s T x1 x2 =>
        have ht1 : term_has_non_none_type x1 := bind_arg1_non_none_of_non_none ht
        have ht2 : term_has_non_none_type x2 := bind_arg2_non_none_of_non_none ht
        exact supported_preservation_term.bind s T x1 x2 ht (go x1 ht1) (go x2 ht2)
    | SmtTerm.DtCons s d i =>
        exact supported_preservation_term.dt_cons s d i
    | SmtTerm.DtSel s d i j =>
        have hNone : __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.DtTester s d i =>
        have hNone : __smtx_typeof (SmtTerm.DtTester s d i) = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.UConst s T =>
        have hTNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          intro hNone
          apply ht
          simpa [__smtx_typeof] using hNone
        exact supported_preservation_term.uconst s T
          (smtx_typeof_guard_wf_inhabited_of_non_none T T hTNN)
    | SmtTerm.not t =>
        have hArg : __smtx_typeof t = SmtType.Bool := by
          unfold term_has_non_none_type at ht
          rw [typeof_not_eq] at ht
          cases h : __smtx_typeof t <;>
            simp [native_ite, native_Teq, h] at ht
          rfl
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type
          rw [hArg]
          simp
        exact supported_preservation_term.not hArgNN (go t hArgNN)
    | SmtTerm.or t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.or) (typeof_or_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.or ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.and t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.and) (typeof_and_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.and ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.imp t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.imp) (typeof_imp_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.imp ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.Apply f x =>
        cases f with
        | «exists» s T body =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.exists s T body) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.exists s T body) hArgs.1)
              (go x hArgs.2)
        | «forall» s T body =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.forall s T body) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.forall s T body) hArgs.1)
              (go x hArgs.2)
        | choice s T body =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.choice s T body) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.choice s T body) hArgs.1)
              (go x hArgs.2)
        | bind s T x1 x2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.bind s T x1 x2) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.bind s T x1 x2) hArgs.1)
              (go x hArgs.2)
        | DtSel s d i j =>
            have htx : term_has_non_none_type x := by
              have hx : __smtx_typeof x = SmtType.Datatype s d :=
                dt_sel_arg_datatype_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht
              unfold term_has_non_none_type
              rw [hx]
              simp
            exact supported_preservation_term.dt_sel
              ht
              (dt_sel_term_inhabited_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht)
              (dt_sel_wrong_map_type_wf_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht)
              htx
              (go x htx)
        | DtTester s d i =>
            exact supported_preservation_term.dt_tester s d i x
        | None =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.None) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go SmtTerm.None hArgs.1)
              (go x hArgs.2)
        | Boolean b =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Boolean b) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Boolean b) hArgs.1)
              (go x hArgs.2)
        | Numeral n =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Numeral n) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Numeral n) hArgs.1)
              (go x hArgs.2)
        | Rational q =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Rational q) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Rational q) hArgs.1)
              (go x hArgs.2)
        | String s =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.String s) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.String s) hArgs.1)
              (go x hArgs.2)
        | Binary w n =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Binary w n) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Binary w n) hArgs.1)
              (go x hArgs.2)
        | Apply f1 x1 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Apply f1 x1) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Apply f1 x1) hArgs.1)
              (go x hArgs.2)
        | Var s T =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Var s T) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Var s T) hArgs.1)
              (go x hArgs.2)
        | ite c t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.ite c t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.ite c t1 t2) hArgs.1)
              (go x hArgs.2)
        | eq t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.eq t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.eq t1 t2) hArgs.1)
              (go x hArgs.2)
        | DtCons s d i =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.DtCons s d i) (x := x)
              (by intro s' d' i' j hEq; cases hEq)
              (by intro s' d' i' hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.DtCons s d i) hArgs.1)
              (go x hArgs.2)
        | UConst s T =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.UConst s T) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.UConst s T) hArgs.1)
              (go x hArgs.2)
        | not t =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.not t) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.not t) hArgs.1)
              (go x hArgs.2)
        | or t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.or t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.or t1 t2) hArgs.1)
              (go x hArgs.2)
        | and t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.and t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.and t1 t2) hArgs.1)
              (go x hArgs.2)
        | imp t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.imp t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.imp t1 t2) hArgs.1)
              (go x hArgs.2)
  exact go

/-- Main type-preservation theorem for evaluation of non-`None` SMT terms in total typed models. -/
theorem type_preservation
    (M : SmtModel)
    (hM : model_wf M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  exact supported_type_preservation M hM t ht
    (supported_preservation_term_of_non_none t ht)

/-- Backwards-compatible wrapper for `type_preservation`. -/
theorem smt_model_eval_preserves_type_of_non_none
    (M : SmtModel) (hM : model_wf M)
    (t : SmtTerm) :
    term_has_non_none_type t ->
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  intro ht
  exact type_preservation M hM t ht

/-- States that evaluating a Boolean-typed SMT term yields a Boolean value. -/
theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : model_wf M)
    (t : SmtTerm) :
  __smtx_typeof t = SmtType.Bool ->
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  intro hTy
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact bool_value_canonical hPres

/-- Derives SMT evaluation type preservation for terms in the supported fragment. -/
theorem smt_model_eval_preserves_type_of_supported
    (M : SmtModel) (hM : model_wf M)
    (t : SmtTerm) (T : SmtType)
    (hTy : __smtx_typeof t = T)
    (hNonNone : T ≠ SmtType.None)
    (_hs : supported_preservation_term t) :
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact hNonNone
  simpa [hTy] using
    type_preservation M hM t hNN

/-- Derives Boolean-value evaluation for supported Boolean-typed SMT terms. -/
theorem smt_model_eval_bool_is_boolean_of_supported
    (M : SmtModel) (hM : model_wf M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool)
    (hs : supported_preservation_term t) :
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool :=
    smt_model_eval_preserves_type_of_supported M hM t SmtType.Bool hTy (by simp) hs
  exact bool_value_canonical hPres


end Smtm
