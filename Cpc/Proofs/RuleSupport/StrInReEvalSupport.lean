module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  simp [__eo_requires, native_ite, native_teq, native_not] at h
  exact h.1

theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not] at h'
  rcases h' with ⟨hxy, hxOk, _hz⟩
  subst y
  simp [__eo_requires, native_ite, native_teq, hxOk, native_not]

theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not] at h'
  rcases h' with ⟨_hxy, hxOk, _hz⟩
  intro hx
  subst x
  have hxNe : y ≠ Term.Stuck := by
    intro hy
    subst y
    simp at hxOk
  exact hxNe hx

theorem eo_requires_result_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not] at h'
  exact h'.2.2

theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

theorem eq_operands_have_smt_translation_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    RuleProofs.eo_has_smt_translation x ∧
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation] using hNonNone
  · simpa [RuleProofs.eo_has_smt_translation, hTy] using hNonNone

theorem str_in_re_args_smt_types_of_has_translation
    (s r : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
  intro hTrans
  have hNN :
      term_has_non_none_type (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) ≠
      SmtType.None
    exact hTrans
  exact seq_char_reglan_args_of_non_none
    (op := SmtTerm.str_in_re) (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt r)) hNN

theorem eo_is_str_eq_true_cases (s : Term) :
    __eo_is_str s = Term.Boolean true ->
    ∃ cs : native_String, s = Term.String cs := by
  intro h
  cases s <;>
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_not, SmtEval.native_and] at h
  case String cs => exact ⟨cs, rfl⟩

theorem native_unpack_seq_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | x :: xs => by
      simp [native_pack_seq, native_unpack_seq, native_unpack_seq_pack_seq T xs]

theorem map_native_ssm_char_of_value_char :
    ∀ s : native_String,
      List.map (impl_native_ssm_char_of_value ∘ SmtValue.Char) s = s
  | [] => rfl
  | c :: cs => by
      simp [Function.comp_def, impl_native_ssm_char_of_value]

theorem native_unpack_string_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp [native_unpack_string, native_pack_string, native_unpack_seq_pack_seq,
    map_native_ssm_char_of_value_char]

@[simp] theorem native_unpack_seq_pack_string (s : native_String) :
    native_unpack_seq (native_pack_string s) = impl_native_string_to_values s := by
  unfold native_pack_string
  rw [native_unpack_seq_pack_seq]
  rfl

theorem native_string_valid_of_smtx_typeof_eo_string
    (s : native_String)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String s)) =
      SmtType.Seq SmtType.Char) :
    native_string_valid s = true := by
  change __smtx_typeof (SmtTerm.String s) = SmtType.Seq SmtType.Char at hTy
  unfold __smtx_typeof at hTy
  cases hValid : native_string_valid s
  · simp [native_ite, hValid] at hTy
  · rfl

theorem native_string_valid_cons_parts
    {c : native_Char} {cs : native_String}
    (h : native_string_valid (c :: cs) = true) :
    native_char_valid c = true ∧ native_string_valid cs = true := by
  simpa [native_string_valid] using h

theorem native_string_valid_append_left
    (xs ys : List native_Char) :
    native_string_valid (xs ++ ys) = true ->
      native_string_valid xs = true := by
  intro h
  simp [native_string_valid] at h ⊢
  intro x hx
  exact h.1 x hx

theorem native_string_valid_append_right
    (xs ys : List native_Char) :
    native_string_valid (xs ++ ys) = true ->
      native_string_valid ys = true := by
  intro h
  simp [native_string_valid] at h ⊢
  intro x hx
  exact h.2 x hx

@[simp] private theorem native_re_str_valid_string
    (str : native_String) :
    Smtm.native_re_str_valid (impl_native_string_to_values str) =
      native_string_valid str := by
  induction str with
  | nil => rfl
  | cons c cs ih =>
      change
        (native_char_valid c &&
          Smtm.native_re_str_valid (impl_native_string_to_values cs)) =
        (native_char_valid c && native_string_valid cs)
      rw [ih]

@[simp] private theorem native_string_to_values_nil :
    impl_native_string_to_values [] = [] := rfl

@[simp] private theorem native_string_to_values_cons
    (c : native_Char) (cs : native_String) :
    impl_native_string_to_values (c :: cs) =
      SmtValue.Char c :: impl_native_string_to_values cs := rfl

private theorem native_str_in_re_cons
    {c : native_Char} {cs : native_String} {r : SmtRegLan}
    (hValid : native_string_valid (c :: cs) = true) :
    native_str_in_re (c :: cs) r =
      native_str_in_re cs (native_re_deriv c r) := by
  rcases native_string_valid_cons_parts hValid with ⟨_hc, hcs⟩
  simp [native_str_in_re, native_re_str_valid, native_re_elem_valid,
    impl_native_string_to_values, _hc]

private theorem native_re_nullable_fold_empty (xs : List SmtValue) :
    native_re_nullable
        (xs.foldl (fun acc c => native_re_deriv c acc) SmtRegLan.empty) =
      false := by
  induction xs with
  | nil => rfl
  | cons c xs ih => simpa [native_re_deriv] using ih

private theorem native_re_of_list_cons_ne_empty_and_epsilon :
    ∀ (c : SmtValue) (cs : List SmtValue),
      impl_native_re_of_list (c :: cs) ≠ SmtRegLan.empty ∧
        impl_native_re_of_list (c :: cs) ≠ SmtRegLan.epsilon
  | c, [] => by
      simp [impl_native_re_of_list, native_re_concat]
  | c, d :: ds => by
      have hTail := native_re_of_list_cons_ne_empty_and_epsilon d ds
      have hConcat :
          native_re_mk_concat (SmtRegLan.char c) (impl_native_re_of_list (d :: ds)) =
            SmtRegLan.concat (SmtRegLan.char c) (impl_native_re_of_list (d :: ds)) := by
        simp [native_re_mk_concat, native_re_concat, hTail.1, hTail.2]
      change
        native_re_mk_concat (SmtRegLan.char c) (impl_native_re_of_list (d :: ds)) ≠
            SmtRegLan.empty ∧
          native_re_mk_concat (SmtRegLan.char c) (impl_native_re_of_list (d :: ds)) ≠
            SmtRegLan.epsilon
      rw [hConcat]
      simp

private theorem native_re_nullable_str_to_re (s : List SmtValue) :
    native_re_nullable (native_str_to_re s) = decide (s = []) := by
  cases s with
  | nil =>
      simp [native_str_to_re, impl_native_re_of_list, native_re_nullable]
  | cons c cs =>
      cases cs with
      | nil =>
          simp [native_str_to_re, impl_native_re_of_list,
            native_re_concat, native_re_nullable]
      | cons d ds =>
          have hTail := native_re_of_list_cons_ne_empty_and_epsilon d ds
          have hConcat :
              native_re_mk_concat (SmtRegLan.char c) (impl_native_re_of_list (d :: ds)) =
                SmtRegLan.concat (SmtRegLan.char c) (impl_native_re_of_list (d :: ds)) := by
            simp [native_re_mk_concat, native_re_concat, hTail.1, hTail.2]
          change
            native_re_nullable
                (native_re_mk_concat (SmtRegLan.char c)
                  (impl_native_re_of_list (d :: ds))) =
              false
          rw [hConcat]
          simp [native_re_nullable]

private theorem native_re_nullable_mk_union (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_union r s) =
      (native_re_nullable r || native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_re_nullable_mk_inter (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_re_nullable_mk_concat (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat, native_re_nullable]

private theorem native_re_mk_concat_left_epsilon (r : SmtRegLan) :
    native_re_mk_concat SmtRegLan.epsilon r = r := by
  cases r <;> rfl

private theorem native_re_mk_concat_right_epsilon (r : SmtRegLan) :
    native_re_mk_concat r SmtRegLan.epsilon = r := by
  cases r <;> simp [native_re_mk_concat, native_re_concat]

private theorem native_re_mk_concat_left_empty (r : SmtRegLan) :
    native_re_mk_concat SmtRegLan.empty r = SmtRegLan.empty := by
  cases r <;> rfl

private theorem native_re_mk_union_right_empty (r : SmtRegLan) :
    native_re_mk_union r SmtRegLan.empty = r := by
  cases r <;> simp [native_re_mk_union, native_re_union]

private theorem native_re_nullable_re_range (s t : List SmtValue) :
    native_re_nullable (native_re_range s t) = false := by
  cases s with
  | nil =>
      simp [native_re_range, native_re_nullable]
  | cons c cs =>
      cases cs with
      | nil =>
          cases t with
          | nil =>
              simp [native_re_range, native_re_nullable]
          | cons d ds =>
              cases ds <;>
                simp [native_re_range, native_re_nullable]
      | cons d ds =>
          simp [native_re_range, native_re_nullable]

theorem smtx_model_eval_str_in_re_string
    (M : SmtModel) (str : native_String) (r : Term) (rv : SmtRegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String str)) r)) =
      SmtValue.Boolean (native_str_in_re str rv) := by
  change __smtx_model_eval M
      (SmtTerm.str_in_re (SmtTerm.String str) (__eo_to_smt r)) =
    SmtValue.Boolean (native_str_in_re str rv)
  rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_4, hREval]
  simp [__smtx_model_eval_str_in_re]

private theorem re_nullable_term_eq (M : SmtModel) :
    (r : Term) -> (rv : SmtRegLan) ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __re_nullable r ≠ Term.Stuck ->
      __re_nullable r = Term.Boolean (native_re_nullable rv)
  | Term.UOp UserOp.re_all, rv, hEval, _hNe => by
      have hTrans : __eo_to_smt (Term.UOp UserOp.re_all) = SmtTerm.re_all := by
        rfl
      rw [hTrans, __smtx_model_eval.eq_106] at hEval
      cases hEval
      change Term.Boolean true =
        Term.Boolean (native_re_nullable native_re_all)
      simp [native_re_all, native_re_nullable]
  | Term.UOp UserOp.re_none, rv, hEval, _hNe => by
      have hTrans : __eo_to_smt (Term.UOp UserOp.re_none) = SmtTerm.re_none := by
        rfl
      rw [hTrans, __smtx_model_eval.eq_105] at hEval
      cases hEval
      change Term.Boolean false =
        Term.Boolean (native_re_nullable native_re_none)
      simp [native_re_none, native_re_nullable]
  | Term.UOp UserOp.re_allchar, rv, hEval, _hNe => by
      have hTrans : __eo_to_smt (Term.UOp UserOp.re_allchar) = SmtTerm.re_allchar := by
        rfl
      rw [hTrans, __smtx_model_eval.eq_104] at hEval
      cases hEval
      change Term.Boolean false =
        Term.Boolean (native_re_nullable native_re_allchar)
      simp [native_re_allchar, native_re_nullable]
  | Term.Apply (Term.UOp UserOp.str_to_re) s, rv, hEval, hNe => by
      change
        __eo_requires (__eo_is_str s) (Term.Boolean true)
          (__eo_eq s (Term.String [])) ≠ Term.Stuck at hNe
      have hStrReq : __eo_is_str s = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck (__eo_is_str s) (Term.Boolean true)
          (__eo_eq s (Term.String [])) hNe
      rcases eo_is_str_eq_true_cases s hStrReq with ⟨str, rfl⟩
      change __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String str)) =
        SmtValue.RegLan rv at hEval
      simp only [__smtx_model_eval, __smtx_model_eval_str_to_re] at hEval
      simp only [native_unpack_seq_pack_string] at hEval
      cases hEval
      change
        __eo_requires (__eo_is_str (Term.String str)) (Term.Boolean true)
          (__eo_eq (Term.String str) (Term.String [])) =
        Term.Boolean (native_re_nullable (native_str_to_re str))
      simp [__eo_requires, __eo_is_str, __eo_is_str_internal,
        __eo_eq, native_ite, native_teq, native_not, SmtEval.native_and,
        native_re_nullable_str_to_re, impl_native_string_to_values]
  | Term.Apply (Term.UOp UserOp.re_mult) r, rv, hEval, _hNe => by
      change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt r)) =
        SmtValue.RegLan rv at hEval
      cases hChild : __smtx_model_eval M (__eo_to_smt r) <;>
        simp [__smtx_model_eval, __smtx_model_eval_re_mult, hChild] at hEval
      case RegLan rx =>
        cases hEval
        change Term.Boolean true =
          Term.Boolean (native_re_nullable (native_re_mult rx))
        cases rx <;>
          simp [native_re_mult, native_re_nullable]
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s) t, rv, hEval, _hNe => by
      change __smtx_model_eval M (SmtTerm.re_range (__eo_to_smt s) (__eo_to_smt t)) =
        SmtValue.RegLan rv at hEval
      cases hS : __smtx_model_eval M (__eo_to_smt s) <;>
        simp [__smtx_model_eval, __smtx_model_eval_re_range, hS] at hEval
      case Seq ss =>
        cases hT : __smtx_model_eval M (__eo_to_smt t) <;>
          simp [hT] at hEval
        case Seq ts =>
          cases hEval
          change Term.Boolean false =
            Term.Boolean
              (native_re_nullable
                (native_re_range (native_unpack_seq ss)
                  (native_unpack_seq ts)))
          simp [native_re_nullable_re_range]
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr, rv, hEval, hNe => by
      have hRNe : __re_nullable r ≠ Term.Stuck := by
        change __eo_or (__re_nullable r) (__re_nullable rr) ≠ Term.Stuck at hNe
        intro h
        rw [h] at hNe
        simp [__eo_or] at hNe
      have hRRNe : __re_nullable rr ≠ Term.Stuck := by
        change __eo_or (__re_nullable r) (__re_nullable rr) ≠ Term.Stuck at hNe
        intro h
        rw [h] at hNe
        cases (__re_nullable r) <;> simp [__eo_or] at hNe
      change __smtx_model_eval M (SmtTerm.re_union (__eo_to_smt r) (__eo_to_smt rr)) =
        SmtValue.RegLan rv at hEval
      cases hR : __smtx_model_eval M (__eo_to_smt r) <;>
        simp [__smtx_model_eval, __smtx_model_eval_re_union, hR] at hEval
      case RegLan rx =>
        cases hRR : __smtx_model_eval M (__eo_to_smt rr) <;>
          simp [hRR] at hEval
        case RegLan ry =>
          cases hEval
          have hNullR := re_nullable_term_eq M r rx hR hRNe
          have hNullRR := re_nullable_term_eq M rr ry hRR hRRNe
          change __eo_or (__re_nullable r) (__re_nullable rr) =
            Term.Boolean (native_re_nullable (native_re_union rx ry))
          simp [hNullR, hNullRR, native_re_nullable_mk_union,
            __eo_or, native_or]
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr, rv, hEval, hNe => by
      have hRNe : __re_nullable r ≠ Term.Stuck := by
        change __eo_and (__re_nullable r) (__re_nullable rr) ≠ Term.Stuck at hNe
        intro h
        rw [h] at hNe
        simp [__eo_and] at hNe
      have hRRNe : __re_nullable rr ≠ Term.Stuck := by
        change __eo_and (__re_nullable r) (__re_nullable rr) ≠ Term.Stuck at hNe
        intro h
        rw [h] at hNe
        cases (__re_nullable r) <;> simp [__eo_and] at hNe
      change __smtx_model_eval M (SmtTerm.re_inter (__eo_to_smt r) (__eo_to_smt rr)) =
        SmtValue.RegLan rv at hEval
      cases hR : __smtx_model_eval M (__eo_to_smt r) <;>
        simp [__smtx_model_eval, __smtx_model_eval_re_inter, hR] at hEval
      case RegLan rx =>
        cases hRR : __smtx_model_eval M (__eo_to_smt rr) <;>
          simp [hRR] at hEval
        case RegLan ry =>
          cases hEval
          have hNullR := re_nullable_term_eq M r rx hR hRNe
          have hNullRR := re_nullable_term_eq M rr ry hRR hRRNe
          change __eo_and (__re_nullable r) (__re_nullable rr) =
            Term.Boolean (native_re_nullable (native_re_inter rx ry))
          simp [hNullR, hNullRR, native_re_nullable_mk_inter,
            __eo_and, SmtEval.native_and]
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r) rr, rv, hEval, hNe => by
      have hRNe : __re_nullable r ≠ Term.Stuck := by
        change __eo_and (__re_nullable r) (__re_nullable rr) ≠ Term.Stuck at hNe
        intro h
        rw [h] at hNe
        simp [__eo_and] at hNe
      have hRRNe : __re_nullable rr ≠ Term.Stuck := by
        change __eo_and (__re_nullable r) (__re_nullable rr) ≠ Term.Stuck at hNe
        intro h
        rw [h] at hNe
        cases (__re_nullable r) <;> simp [__eo_and] at hNe
      change __smtx_model_eval M (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt rr)) =
        SmtValue.RegLan rv at hEval
      cases hR : __smtx_model_eval M (__eo_to_smt r) <;>
        simp [__smtx_model_eval, __smtx_model_eval_re_concat, hR] at hEval
      case RegLan rx =>
        cases hRR : __smtx_model_eval M (__eo_to_smt rr) <;>
          simp [hRR] at hEval
        case RegLan ry =>
          cases hEval
          have hNullR := re_nullable_term_eq M r rx hR hRNe
          have hNullRR := re_nullable_term_eq M rr ry hRR hRRNe
          change __eo_and (__re_nullable r) (__re_nullable rr) =
            Term.Boolean (native_re_nullable (native_re_concat rx ry))
          simp [hNullR, hNullRR, native_re_nullable_mk_concat,
            __eo_and, SmtEval.native_and]
  | Term.Apply (Term.UOp UserOp.re_comp) r, rv, hEval, hNe => by
      have hRNe : __re_nullable r ≠ Term.Stuck := by
        change __eo_not (__re_nullable r) ≠ Term.Stuck at hNe
        intro h
        rw [h] at hNe
        simp [__eo_not] at hNe
      change __smtx_model_eval M (SmtTerm.re_comp (__eo_to_smt r)) =
        SmtValue.RegLan rv at hEval
      cases hR : __smtx_model_eval M (__eo_to_smt r) <;>
        simp [__smtx_model_eval, __smtx_model_eval_re_comp, hR] at hEval
      case RegLan rx =>
        cases hEval
        have hNullR := re_nullable_term_eq M r rx hR hRNe
        change __eo_not (__re_nullable r) =
          Term.Boolean (native_re_nullable (native_re_comp rx))
        cases rx <;>
          simp [hNullR, native_re_comp,
            native_re_nullable, __eo_not, native_not]
  | r, rv, hEval, hNe => by
      cases r <;> try exact False.elim (hNe rfl)
      case UOp op =>
        cases op <;> try exact False.elim (hNe rfl)
        case re_allchar =>
          change __smtx_model_eval M SmtTerm.re_allchar =
            SmtValue.RegLan rv at hEval
          rw [__smtx_model_eval.eq_104] at hEval
          cases hEval
          change Term.Boolean false =
            Term.Boolean (native_re_nullable native_re_allchar)
          simp [native_re_allchar, native_re_nullable]
        case re_none =>
          change __smtx_model_eval M SmtTerm.re_none =
            SmtValue.RegLan rv at hEval
          rw [__smtx_model_eval.eq_105] at hEval
          cases hEval
          change Term.Boolean false =
            Term.Boolean (native_re_nullable native_re_none)
          simp [native_re_none, native_re_nullable]
        case re_all =>
          change __smtx_model_eval M SmtTerm.re_all =
            SmtValue.RegLan rv at hEval
          rw [__smtx_model_eval.eq_106] at hEval
          cases hEval
          change Term.Boolean true =
            Term.Boolean (native_re_nullable native_re_all)
          simp [native_re_all, native_re_nullable]
      case Apply f x =>
        cases f <;> try exact False.elim (hNe rfl)
        case UOp op =>
          cases op <;> try exact False.elim (hNe rfl)
          case str_to_re =>
            change
              __eo_requires (__eo_is_str x) (Term.Boolean true)
                (__eo_eq x (Term.String [])) ≠ Term.Stuck at hNe
            have hStrReq : __eo_is_str x = Term.Boolean true :=
              eo_requires_eq_of_ne_stuck (__eo_is_str x) (Term.Boolean true)
                (__eo_eq x (Term.String [])) hNe
            rcases eo_is_str_eq_true_cases x hStrReq with ⟨str, rfl⟩
            change __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String str)) =
              SmtValue.RegLan rv at hEval
            simp only [__smtx_model_eval, __smtx_model_eval_str_to_re] at hEval
            simp only [native_unpack_seq_pack_string] at hEval
            cases hEval
            change
              __eo_requires (__eo_is_str (Term.String str)) (Term.Boolean true)
                (__eo_eq (Term.String str) (Term.String [])) =
              Term.Boolean (native_re_nullable (native_str_to_re str))
            simp [__eo_requires, __eo_is_str, __eo_is_str_internal,
              __eo_eq, native_ite, native_teq, native_not, SmtEval.native_and,
              native_re_nullable_str_to_re, impl_native_string_to_values]
          case re_mult =>
            change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt x)) =
              SmtValue.RegLan rv at hEval
            cases hChild : __smtx_model_eval M (__eo_to_smt x) <;>
              simp [__smtx_model_eval, __smtx_model_eval_re_mult, hChild] at hEval
            case RegLan rx =>
              cases hEval
              change Term.Boolean true =
                Term.Boolean (native_re_nullable (native_re_mult rx))
              cases rx <;>
                simp [native_re_mult, native_re_nullable]
          case re_comp =>
            have hXNe : __re_nullable x ≠ Term.Stuck := by
              change __eo_not (__re_nullable x) ≠ Term.Stuck at hNe
              intro h
              rw [h] at hNe
              simp [__eo_not] at hNe
            change __smtx_model_eval M (SmtTerm.re_comp (__eo_to_smt x)) =
              SmtValue.RegLan rv at hEval
            cases hX : __smtx_model_eval M (__eo_to_smt x) <;>
              simp [__smtx_model_eval, __smtx_model_eval_re_comp, hX] at hEval
            case RegLan rx =>
              cases hEval
              have hNullX := re_nullable_term_eq M x rx hX hXNe
              change __eo_not (__re_nullable x) =
                Term.Boolean (native_re_nullable (native_re_comp rx))
              cases rx <;>
                simp [hNullX, native_re_comp,
                  native_re_nullable, __eo_not, native_not]
        case Apply g y =>
          cases g <;> try exact False.elim (hNe rfl)
          case UOp op =>
            cases op <;> try exact False.elim (hNe rfl)
            case re_range =>
              change __smtx_model_eval M
                  (SmtTerm.re_range (__eo_to_smt y) (__eo_to_smt x)) =
                SmtValue.RegLan rv at hEval
              cases hY : __smtx_model_eval M (__eo_to_smt y) <;>
                simp [__smtx_model_eval, __smtx_model_eval_re_range, hY] at hEval
              case Seq ys =>
                cases hX : __smtx_model_eval M (__eo_to_smt x) <;>
                  simp [hX] at hEval
                case Seq xs =>
                  cases hEval
                  change Term.Boolean false =
                    Term.Boolean
                      (native_re_nullable
                        (native_re_range (native_unpack_seq ys)
                          (native_unpack_seq xs)))
                  simp [native_re_nullable_re_range]
            case re_union =>
              have hYNe : __re_nullable y ≠ Term.Stuck := by
                change __eo_or (__re_nullable y) (__re_nullable x) ≠
                  Term.Stuck at hNe
                intro h
                rw [h] at hNe
                simp [__eo_or] at hNe
              have hXNe : __re_nullable x ≠ Term.Stuck := by
                change __eo_or (__re_nullable y) (__re_nullable x) ≠
                  Term.Stuck at hNe
                intro h
                rw [h] at hNe
                cases (__re_nullable y) <;> simp [__eo_or] at hNe
              change __smtx_model_eval M
                  (SmtTerm.re_union (__eo_to_smt y) (__eo_to_smt x)) =
                SmtValue.RegLan rv at hEval
              cases hY : __smtx_model_eval M (__eo_to_smt y) <;>
                simp [__smtx_model_eval, __smtx_model_eval_re_union, hY] at hEval
              case RegLan ry =>
                cases hX : __smtx_model_eval M (__eo_to_smt x) <;>
                  simp [hX] at hEval
                case RegLan rx =>
                  cases hEval
                  have hNullY := re_nullable_term_eq M y ry hY hYNe
                  have hNullX := re_nullable_term_eq M x rx hX hXNe
                  change __eo_or (__re_nullable y) (__re_nullable x) =
                    Term.Boolean (native_re_nullable (native_re_union ry rx))
                  simp [hNullY, hNullX, native_re_nullable_mk_union,
                    __eo_or, native_or]
            case re_inter =>
              have hYNe : __re_nullable y ≠ Term.Stuck := by
                change __eo_and (__re_nullable y) (__re_nullable x) ≠
                  Term.Stuck at hNe
                intro h
                rw [h] at hNe
                simp [__eo_and] at hNe
              have hXNe : __re_nullable x ≠ Term.Stuck := by
                change __eo_and (__re_nullable y) (__re_nullable x) ≠
                  Term.Stuck at hNe
                intro h
                rw [h] at hNe
                cases (__re_nullable y) <;> simp [__eo_and] at hNe
              change __smtx_model_eval M
                  (SmtTerm.re_inter (__eo_to_smt y) (__eo_to_smt x)) =
                SmtValue.RegLan rv at hEval
              cases hY : __smtx_model_eval M (__eo_to_smt y) <;>
                simp [__smtx_model_eval, __smtx_model_eval_re_inter, hY] at hEval
              case RegLan ry =>
                cases hX : __smtx_model_eval M (__eo_to_smt x) <;>
                  simp [hX] at hEval
                case RegLan rx =>
                  cases hEval
                  have hNullY := re_nullable_term_eq M y ry hY hYNe
                  have hNullX := re_nullable_term_eq M x rx hX hXNe
                  change __eo_and (__re_nullable y) (__re_nullable x) =
                    Term.Boolean (native_re_nullable (native_re_inter ry rx))
                  simp [hNullY, hNullX, native_re_nullable_mk_inter,
                    __eo_and, SmtEval.native_and]
            case re_concat =>
              have hYNe : __re_nullable y ≠ Term.Stuck := by
                change __eo_and (__re_nullable y) (__re_nullable x) ≠
                  Term.Stuck at hNe
                intro h
                rw [h] at hNe
                simp [__eo_and] at hNe
              have hXNe : __re_nullable x ≠ Term.Stuck := by
                change __eo_and (__re_nullable y) (__re_nullable x) ≠
                  Term.Stuck at hNe
                intro h
                rw [h] at hNe
                cases (__re_nullable y) <;> simp [__eo_and] at hNe
              change __smtx_model_eval M
                  (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt x)) =
                SmtValue.RegLan rv at hEval
              cases hY : __smtx_model_eval M (__eo_to_smt y) <;>
                simp [__smtx_model_eval, __smtx_model_eval_re_concat, hY] at hEval
              case RegLan ry =>
                cases hX : __smtx_model_eval M (__eo_to_smt x) <;>
                  simp [hX] at hEval
                case RegLan rx =>
                  cases hEval
                  have hNullY := re_nullable_term_eq M y ry hY hYNe
                  have hNullX := re_nullable_term_eq M x rx hX hXNe
                  change __eo_and (__re_nullable y) (__re_nullable x) =
                    Term.Boolean (native_re_nullable (native_re_concat ry rx))
                  simp [hNullY, hNullX, native_re_nullable_mk_concat,
                    __eo_and, SmtEval.native_and]

private theorem smtx_model_eval_re_nullable
    (M : SmtModel) (r : Term) (rv : SmtRegLan)
    (hEval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hNe : __re_nullable r ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (__re_nullable r)) =
      SmtValue.Boolean (native_re_nullable rv) := by
  rw [re_nullable_term_eq M r rv hEval hNe]
  change __smtx_model_eval M (SmtTerm.Boolean (native_re_nullable rv)) =
    SmtValue.Boolean (native_re_nullable rv)
  rw [__smtx_model_eval.eq_1]

private def intRangeTerm : native_Int -> Nat -> Term
  | _start, 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)
  | start, n + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral start))
        (intRangeTerm (start + 1) n)

def extractString (s : native_String) (i : native_Int) :
    native_String :=
  native_str_substr s i (native_zplus (native_zplus i (native_zneg i)) 1)

def substrWord (s : native_String) : native_Int -> Nat -> Term
  | _start, 0 => Term.String []
  | start, n + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.String (extractString s start)))
        (substrWord s (start + 1) n)

theorem substrWord_ne_stuck (s : native_String) :
    ∀ (n : Nat) (start : native_Int), substrWord s start n ≠ Term.Stuck
  | 0, _start => by simp [substrWord]
  | _n + 1, _start => by simp [substrWord]

private theorem str_flatten_word_rec_range_eq_substrWord
    (s : native_String) :
    ∀ (n : Nat) (start : native_Int),
      __str_flatten_word_rec (intRangeTerm start n) (Term.String s) =
        substrWord s start n
  | 0, _start => by rfl
  | n + 1, start => by
      simp only [intRangeTerm, substrWord, __str_flatten_word_rec,
        __eo_extract, extractString]
      rw [str_flatten_word_rec_range_eq_substrWord s n (start + 1)]
      simp [__eo_mk_apply, substrWord_ne_stuck]

private def zeroIntListTerm : Nat -> Term
  | 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)
  | n + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (zeroIntListTerm n)

private theorem zeroIntListTerm_ne_stuck :
    ∀ n, zeroIntListTerm n ≠ Term.Stuck
  | 0 => by simp [zeroIntListTerm]
  | _n + 1 => by simp [zeroIntListTerm]

private theorem eo_list_repeat_rec_zero_eq :
    ∀ n,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) n =
        zeroIntListTerm n
  | 0 => by rfl
  | n + 1 => by
      simp [__eo_list_repeat_rec, zeroIntListTerm, eo_list_repeat_rec_zero_eq n,
        __eo_mk_apply, zeroIntListTerm_ne_stuck]

private theorem eo_list_repeat_zero_eq (n : Nat) :
    __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
        (Term.Numeral 0) (Term.Numeral (Int.ofNat n)) =
      zeroIntListTerm n := by
  have hnot : native_zlt (↑n : native_Int) 0 = false := by
    simp [native_zlt]
  simp [__eo_list_repeat, native_ite, native_int_to_nat, hnot,
    eo_list_repeat_rec_zero_eq]

private theorem intRangeTerm_ne_stuck :
    ∀ n start, intRangeTerm start n ≠ Term.Stuck
  | 0, _start => by simp [intRangeTerm]
  | _n + 1, _start => by simp [intRangeTerm]

private theorem iota_zero_list_eq_range :
    ∀ (n : Nat) (start : native_Int),
      __iota_rec (zeroIntListTerm n) (Term.Numeral start) =
        intRangeTerm start n
  | 0, _start => by rfl
  | n + 1, start => by
      simp only [zeroIntListTerm, intRangeTerm, __iota_rec, __eo_add,
        native_zplus]
      rw [iota_zero_list_eq_range n (start + 1)]
      simp [__eo_mk_apply, intRangeTerm_ne_stuck]

theorem extractString_zero_cons
    (c : native_Char) (cs : native_String) :
    extractString (c :: cs) 0 = [c] := by
  have hnot : ¬ ((cs.length : Int) + 1 ≤ 0) := by omega
  have hmin : min (1 : Int) ((cs.length : Int) + 1) = 1 := by omega
  simp [extractString, native_str_substr, native_str_len, native_zplus,
    native_zneg, hnot, hmin]

private theorem eo_extract_zero_zero_cons
    (c : native_Char) (cs : native_String) :
    __eo_extract (Term.String (c :: cs)) (Term.Numeral 0) (Term.Numeral 0) =
      Term.String [c] := by
  have hnot : ¬ ((cs.length : Int) + 1 ≤ 0) := by omega
  have hmin : min (1 : Int) ((cs.length : Int) + 1) = 1 := by omega
  simp [__eo_extract, native_str_substr, native_str_len, native_zplus,
    native_zneg, hnot, hmin]

private theorem native_str_substr_tail_cons
    (c : native_Char) (cs : native_String) :
    native_str_substr (c :: cs) 1 (Int.ofNat cs.length) = cs := by
  cases cs with
  | nil =>
      simp [native_str_substr, native_str_len]
  | cons d ds =>
      have hBounds :
          ¬ ((1 : Int) < 0 ∨
            ((↑(List.length ds) : Int) + 1) ≤ 0 ∨
              1 ≥ ((↑(List.length ds) : Int) + 1 + 1)) := by
        omega
      have hMin :
          (min (((↑(List.length ds) : Int) + 1))
              (((↑(List.length ds) : Int) + 1 + 1) - 1)).toNat =
            ds.length + 1 := by
        have h :
            min (((↑(List.length ds) : Int) + 1))
                (((↑(List.length ds) : Int) + 1 + 1) - 1) =
              (↑(ds.length + 1) : Int) := by
          omega
        simp
      simp [native_str_substr, native_str_len]
      omega

private theorem eo_extract_tail_cons
    (c : native_Char) (cs : native_String) :
    __eo_extract (Term.String (c :: cs)) (Term.Numeral 1)
        (__eo_add (Term.Numeral (-1 : native_Int))
          (__eo_len (Term.String (c :: cs)))) =
      Term.String cs := by
  have hLen :
      native_zplus
          (native_zplus
            (native_zplus (-1 : native_Int) (native_str_len (c :: cs)))
            (native_zneg (1 : native_Int))) 1 =
        Int.ofNat cs.length := by
    change ((-1 : Int) + Int.ofNat (List.length (c :: cs)) + -1 + 1) =
      Int.ofNat cs.length
    simp
    omega
  simp only [__eo_extract, __eo_add, __eo_len]
  rw [hLen]
  exact congrArg Term.String (native_str_substr_tail_cons c cs)

private theorem extractString_cons_succ_nat
    (c : native_Char) (cs : native_String) (i : Nat) :
    extractString (c :: cs) ((i : Int) + 1) =
      extractString cs (i : Int) := by
  by_cases hLt : i < cs.length
  · have hLenNotLe : ¬ cs.length ≤ i := Nat.not_le_of_gt hLt
    have hLeftNonneg :
        ¬ (((i : Int) + 1 < 0) ∨
          ((i : Int) + 1 + -((i : Int) + 1) + 1 ≤ 0)) := by
      omega
    have hRightNonneg :
        ¬ (((i : Int) < 0) ∨ ((i : Int) + -(i : Int) + 1 ≤ 0)) := by
      omega
    have hMinLeft :
        (min ((i : Int) + 1 + -((i : Int) + 1) + 1)
            ((cs.length : Int) + 1 - ((i : Int) + 1))).toNat = 1 := by
      have h :
          min ((i : Int) + 1 + -((i : Int) + 1) + 1)
              ((cs.length : Int) + 1 - ((i : Int) + 1)) =
            1 := by
        omega
      simp [h]
    have hMinRight :
        (min ((i : Int) + -(i : Int) + 1)
            ((cs.length : Int) - (i : Int))).toNat = 1 := by
      have h :
          min ((i : Int) + -(i : Int) + 1)
              ((cs.length : Int) - (i : Int)) =
            1 := by
        omega
      simp [h]
    have hLeftLt : ¬ ((i : Int) + 1 < 0) := by omega
    have hRightLt : ¬ ((i : Int) < 0) := by omega
    simp [extractString, native_str_substr, native_str_len, native_zplus,
      native_zneg, hLeftLt, hRightLt, hLenNotLe, hMinLeft,
      hMinRight, List.drop_succ_cons]
    -- v4.33 `simp` rewrites inside `decide`'s proposition without refreshing the
    -- `Decidable` instance, so the remaining guards cannot be rewritten; split
    -- on them instead.
    split <;> split
    case isTrue.isTrue => rfl
    case isFalse.isFalse => rfl
    case isTrue.isFalse h1 _ =>
        exfalso
        -- ascribe the cast form `omega` understands (`↑i`, not `Int.ofNat i`)
        have h : ((i : Int) + 1 + -((i : Int) + 1) + 1) ≤ 0 :=
          of_decide_eq_true h1
        omega
    case isFalse.isTrue _ h2 =>
        exfalso
        have h : ((i : Int) + -(i : Int) + 1) ≤ 0 :=
          of_decide_eq_true h2
        omega
  · have hLeft : ((i : Int) + 1) >= ((cs.length : Int) + 1) := by
      omega
    have hLenLe : cs.length ≤ i := Nat.le_of_not_gt hLt
    simp [extractString, native_str_substr, native_str_len, native_zplus,
      native_zneg, hLeft, hLenLe]

private theorem substrWord_cons_succ_nat
    (c : native_Char) (cs : native_String) :
    ∀ (n i : Nat),
      substrWord (c :: cs) (Int.ofNat (i + 1)) n =
        substrWord cs (Int.ofNat i) n
  | 0, _i => by rfl
  | n + 1, i => by
      simp only [substrWord]
      have hHeadStart :
          Int.ofNat (i + 1) = (i : Int) + 1 := by
        simp
      rw [hHeadStart, extractString_cons_succ_nat c cs i]
      have hRightStart :
          Int.ofNat i + 1 = Int.ofNat (i + 1) := by
        simp
      have hLeftStart :
          (i : Int) + 1 + 1 = Int.ofNat (i + 1 + 1) := by
        simp
      rw [hRightStart, hLeftStart,
        substrWord_cons_succ_nat c cs n (i + 1)]
      rfl

theorem substrWord_cons_tail
    (c : native_Char) (cs : native_String) :
    substrWord (c :: cs) 1 cs.length =
      substrWord cs 0 cs.length := by
  simpa using substrWord_cons_succ_nat c cs cs.length 0

theorem str_flatten_nary_intro_empty :
    __str_flatten (__str_nary_intro (Term.String [])) = Term.String [] := by
  rfl

private theorem eo_requires_true_true (z : Term) :
    __eo_requires (Term.Boolean true) (Term.Boolean true) z = z := by
  simp [__eo_requires, native_ite, native_teq, native_not]

private theorem eo_requires_refl_of_ne_stuck
    (x z : Term) (hx : x ≠ Term.Stuck) :
    __eo_requires x x z = z := by
  simp [__eo_requires, native_ite, native_teq, native_not, hx]

private theorem str_concat_empty_is_list :
    __eo_is_list (Term.UOp UserOp.str_concat) (Term.String []) =
      Term.Boolean true := by
  change
    __eo_is_ok
        (__eo_requires
          (__eo_is_list_nil (Term.UOp UserOp.str_concat) (Term.String []))
          (Term.Boolean true) (Term.String [])) =
      Term.Boolean true
  have hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) (Term.String []) =
        Term.Boolean true := by
    simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
      native_teq]
  rw [hNil, eo_requires_true_true]
  simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not]

private theorem str_concat_substrWord_is_list
    (s : native_String) :
    ∀ (n : Nat) (start : native_Int),
      __eo_is_list (Term.UOp UserOp.str_concat) (substrWord s start n) =
        Term.Boolean true
  | 0, _start => str_concat_empty_is_list
  | n + 1, start => by
      simp only [substrWord, __eo_is_list, __eo_get_nil_rec]
      rw [eo_requires_refl_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (substrWord s (start + 1) n)) (by simp)]
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (substrWord s (start + 1) n)) =
          Term.Boolean true
      have hTail := str_concat_substrWord_is_list s n (start + 1)
      unfold __eo_is_list at hTail
      cases hSub : substrWord s (start + 1) n <;>
        simp [hSub] at hTail ⊢ <;>
        exact hTail

private theorem eo_list_concat_rec_substrWord_empty
    (s : native_String) :
    ∀ (n : Nat) (start : native_Int),
      __eo_list_concat_rec (substrWord s start n) (Term.String []) =
        substrWord s start n
  | 0, _start => by rfl
  | n + 1, start => by
      simp only [substrWord, __eo_list_concat_rec]
      rw [eo_list_concat_rec_substrWord_empty s n (start + 1)]
      simp [__eo_mk_apply, substrWord_ne_stuck]

private theorem str_nary_intro_cons
    (c : native_Char) (cs : native_String) :
    __str_nary_intro (Term.String (c :: cs)) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_concat) (Term.String (c :: cs)))
        (Term.String []) := by
  simp only [__str_nary_intro]
  change
    __eo_ite (__eo_eq (Term.String (c :: cs)) (Term.String []))
        (Term.String (c :: cs))
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_concat) (Term.String (c :: cs)))
          (Term.String [])) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_concat) (Term.String (c :: cs)))
        (Term.String [])
  have hEqFalse :
      __eo_eq (Term.String (c :: cs)) (Term.String []) =
        Term.Boolean false := by
    change Term.Boolean (decide (Term.String [] = Term.String (c :: cs))) =
      Term.Boolean false
    simp
  rw [hEqFalse]
  simp [__eo_ite, native_teq, native_ite, __eo_mk_apply]

private theorem eo_list_concat_str_concat_substrWord_empty
    (s : native_String) :
    ∀ (n : Nat) (start : native_Int),
      __eo_list_concat (Term.UOp UserOp.str_concat) (substrWord s start n)
          (Term.String []) =
        substrWord s start n
  | n, start => by
      simp only [__eo_list_concat]
      rw [str_concat_substrWord_is_list s n start, eo_requires_true_true,
        str_concat_empty_is_list, eo_requires_true_true,
        eo_list_concat_rec_substrWord_empty s n start]

theorem str_flatten_nary_intro_cons
    (c : native_Char) (cs : native_String) :
    __str_flatten (__str_nary_intro (Term.String (c :: cs))) =
      substrWord (c :: cs) 0 (c :: cs).length := by
  rw [str_nary_intro_cons c cs]
  have hIsStr : __eo_is_str (Term.String (c :: cs)) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not]
  have hCountLen :
      native_zlt (Int.ofNat (c :: cs).length) 0 = false := by
    change decide ((Int.ofNat (c :: cs).length : Int) < 0) = false
    simp
    omega
  have hReqLen :
      __eo_requires
          (Term.Boolean (native_zlt (Int.ofNat (c :: cs).length) 0))
          (Term.Boolean false)
          (__iota_rec
            (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0)
              (Term.Numeral (Int.ofNat (c :: cs).length)))
            (Term.Numeral 0)) =
        __iota_rec
          (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0)
            (Term.Numeral (Int.ofNat (c :: cs).length)))
          (Term.Numeral 0) := by
    rw [hCountLen]
    exact eo_requires_refl_of_ne_stuck (Term.Boolean false) _ (by simp)
  have hTail :
      __eo_requires (Term.String [])
          (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
        Term.String [] := by
    change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
      Term.String []
    simp [__eo_requires, native_ite, native_teq, native_not]
  simp only [__str_flatten, __eo_len, native_str_len, __eo_is_neg]
  rw [hIsStr]
  simp only [__eo_ite, native_teq, native_ite]
  rw [hTail, hReqLen, eo_list_repeat_zero_eq, iota_zero_list_eq_range,
    str_flatten_word_rec_range_eq_substrWord]
  exact eo_list_concat_str_concat_substrWord_empty (c :: cs) (c :: cs).length 0

theorem str_eval_empty_eq_nullable (r : Term) :
    __str_eval_str_in_re_rec (Term.String []) r = __re_nullable r := by
  cases r <;> rfl

theorem str_eval_concat_step_of_ne_re_none
    (s1 s2 r : Term)
    (hRStuck : r ≠ Term.Stuck)
    (hRNone : r ≠ Term.UOp UserOp.re_none) :
    __str_eval_str_in_re_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2) r =
      __str_eval_str_in_re_rec s2 (__derivative s1 r) := by
  cases r <;> simp [__str_eval_str_in_re_rec] at hRStuck hRNone ⊢

theorem smt_value_rel_reglan_valid_eq
    {r s : SmtRegLan} {str : native_String}
    (hRel : RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s))
    (hValid : native_string_valid str = true) :
    native_str_in_re str r = native_str_in_re str s := by
  change __smtx_model_eval_eq (SmtValue.RegLan r) (SmtValue.RegLan s) =
    SmtValue.Boolean true at hRel
  have hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r = native_str_in_re str s := by
    simpa [__smtx_model_eval_eq] using hRel
  exact hExt str hValid

private theorem native_str_in_re_mk_comp_list :
    ∀ (xs : List SmtValue) (r : SmtRegLan),
      native_re_nullable
          (xs.foldl (fun acc c => native_re_deriv c acc)
            (native_re_mk_comp r)) =
        Bool.not
          (native_re_nullable
            (xs.foldl (fun acc c => native_re_deriv c acc) r))
  | [], r => by
      cases r <;> simp [native_re_mk_comp, native_re_comp, native_re_nullable]
  | c :: cs, r => by
      have h := native_str_in_re_mk_comp_list cs (native_re_deriv c r)
      cases r <;> simp [native_re_mk_comp, native_re_comp,
        native_re_deriv] at h ⊢
      case comp r =>
        have hComp := native_str_in_re_mk_comp_list cs (native_re_deriv c r)
        have hComp' :
            native_re_nullable
                (List.foldl (fun acc c => native_re_deriv c acc)
                  (match native_re_deriv c r with
                  | SmtRegLan.comp r => r
                  | r => SmtRegLan.comp r)
                  cs) =
              Bool.not
                (native_re_nullable
                    (List.foldl (fun acc c => native_re_deriv c acc)
                      (native_re_deriv c r) cs)) := by
          exact hComp
        cases hA :
            native_re_nullable
              (List.foldl (fun acc c => native_re_deriv c acc)
                (native_re_deriv c r) cs) <;>
          cases hB :
            native_re_nullable
              (List.foldl (fun acc c => native_re_deriv c acc)
                (match native_re_deriv c r with
                | SmtRegLan.comp r => r
                | r => SmtRegLan.comp r)
                cs) <;>
          simp [hA, hB] at hComp' ⊢ <;> assumption
      all_goals exact h

private theorem native_str_in_re_re_comp
    (s : native_String) (r : SmtRegLan) :
    native_str_in_re s (native_re_comp r) =
      (native_string_valid s && Bool.not (native_str_in_re s r)) := by
  cases hValid : native_string_valid s
  · simp [native_str_in_re, native_re_str_valid_string, hValid]
  · simp only [native_str_in_re, native_re_str_valid_string, hValid,
      Bool.true_and]
    exact native_str_in_re_mk_comp_list (impl_native_string_to_values s) r

theorem smt_value_rel_reglan_of_eq {r s : SmtRegLan}
    (h : r = s) :
    RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s) := by
  subst s
  exact RuleProofs.smt_value_rel_refl (SmtValue.RegLan r)

private def nativeListInRe (xs : List native_Char) (r : SmtRegLan) :
    native_Bool :=
  native_re_nullable <|
    (impl_native_string_to_values xs).foldl
      (fun acc c => native_re_deriv c acc) r

private theorem nativeListInRe_empty :
    (xs : List native_Char) -> nativeListInRe xs SmtRegLan.empty = false
  | [] => by rfl
  | _ :: xs => by
      exact nativeListInRe_empty xs

private theorem native_re_deriv_re_all_valid_local
    (c : native_Char) (hValid : native_char_valid c = true) :
    native_re_deriv c native_re_all = native_re_all := by
  simp [native_re_all, native_re_deriv, native_re_elem_valid,
    native_re_concat, hValid]

private theorem nativeListInRe_re_all_local :
    (xs : List native_Char) ->
      xs.all native_char_valid = true ->
      nativeListInRe xs native_re_all = true
  | [], _ => by
      simp [nativeListInRe, impl_native_string_to_values, native_re_all,
        native_re_nullable]
  | c :: xs, hValid => by
      simp [List.all_eq_true] at hValid
      have hXsValid : xs.all native_char_valid = true := by
        simpa [List.all_eq_true] using hValid.2
      change nativeListInRe xs (native_re_deriv c native_re_all) = true
      rw [native_re_deriv_re_all_valid_local c hValid.1]
      exact nativeListInRe_re_all_local xs hXsValid

private theorem native_str_in_re_all_valid_local
    (str : native_String) :
    native_string_valid str = true ->
    native_str_in_re str native_re_all = true := by
  intro hValid
  have hListValid : str.all native_char_valid = true := by
    simpa [native_string_valid] using hValid
  simpa [native_str_in_re, hValid, nativeListInRe] using
    nativeListInRe_re_all_local str hListValid

private theorem native_re_mk_union_self_local (r : SmtRegLan) :
    native_re_mk_union r r = r := by
  cases r <;> simp [native_re_mk_union, native_re_union]

private theorem native_re_mk_union_eq_union_of_ne_local
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_union r s = SmtRegLan.union r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem nativeListInRe_mk_union :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_union r s) =
        (nativeListInRe xs r || nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, impl_native_string_to_values,
        native_re_nullable_mk_union]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_union, native_re_union, nativeListInRe_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_union, native_re_union, nativeListInRe_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_union_self_local]
            simp [nativeListInRe]
          · rw [native_re_mk_union_eq_union_of_ne_local r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_union cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_re_mk_inter_self_local (r : SmtRegLan) :
    native_re_mk_inter r r = r := by
  cases r <;> simp [native_re_mk_inter, native_re_inter]

private theorem native_re_mk_inter_eq_inter_of_ne_local
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_inter r s = SmtRegLan.inter r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem nativeListInRe_mk_inter :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_inter r s) =
        (nativeListInRe xs r && nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, impl_native_string_to_values,
        native_re_nullable_mk_inter]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_inter, native_re_inter, nativeListInRe_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_inter, native_re_inter, nativeListInRe_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_inter_self_local]
            simp [nativeListInRe]
          · rw [native_re_mk_inter_eq_inter_of_ne_local r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_inter cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem nativeListInRe_mk_concat_empty_right
  (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;> simp [native_re_mk_concat, native_re_concat,
    nativeListInRe_empty]

private theorem nativeListInRe_mk_concat_epsilon_right
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.epsilon) =
      nativeListInRe xs r := by
  cases r <;> simp [native_re_mk_concat, native_re_concat,
    nativeListInRe_empty]

private theorem native_re_mk_concat_eq_concat_of_ne_local
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ SmtRegLan.epsilon ->
    s ≠ SmtRegLan.epsilon ->
    native_re_mk_concat r s = SmtRegLan.concat r s := by
  intro hrEmpty hsEmpty hrEps hsEps
  cases r <;> cases s
  all_goals
    simp [native_re_mk_concat, native_re_concat] at hrEmpty hsEmpty hrEps hsEps ⊢

private theorem nativeListInRe_deriv_mk_concat
    (xs : List native_Char) (c : native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_deriv c (native_re_mk_concat r s)) =
      nativeListInRe xs
        (native_re_mk_union
          (native_re_mk_concat (native_re_deriv c r) s)
          (if native_re_nullable r then native_re_deriv c s else SmtRegLan.empty)) := by
  by_cases hrEmpty : r = SmtRegLan.empty
  · subst r
    simp [native_re_mk_concat, native_re_concat, native_re_deriv,
      native_re_nullable,
      nativeListInRe_mk_union, nativeListInRe_empty]
  · by_cases hsEmpty : s = SmtRegLan.empty
    · subst s
      have hL :
          nativeListInRe xs
            (native_re_deriv c (native_re_mk_concat r SmtRegLan.empty)) =
            false := by
        simp [native_re_mk_concat, native_re_concat, native_re_deriv,
          nativeListInRe_empty]
      rw [hL]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat_empty_right]
      simp [native_re_deriv, nativeListInRe_empty]
    · by_cases hrEps : r = SmtRegLan.epsilon
      · subst r
        simp [native_re_mk_concat, native_re_concat, native_re_deriv,
          native_re_nullable,
          nativeListInRe_mk_union, nativeListInRe_empty]
      · by_cases hsEps : s = SmtRegLan.epsilon
        · subst s
          have hMk : native_re_mk_concat r SmtRegLan.epsilon = r := by
            cases r <;>
              simp [native_re_mk_concat, native_re_concat] at hrEmpty hrEps ⊢
          rw [hMk]
          rw [nativeListInRe_mk_union]
          rw [nativeListInRe_mk_concat_epsilon_right]
          simp [native_re_deriv, nativeListInRe_empty]
        · have hMk :=
            native_re_mk_concat_eq_concat_of_ne_local r s hrEmpty hsEmpty
              hrEps hsEps
          rw [hMk]
          simp [native_re_deriv, nativeListInRe_mk_union]

private def nativeListInReConcat :
    List native_Char -> SmtRegLan -> SmtRegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && nativeListInRe (c :: cs) s) ||
        nativeListInReConcat cs (native_re_deriv c r) s

private theorem nativeListInRe_mk_concat :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_concat r s) =
        nativeListInReConcat xs r s
  | [], r, s => by
      simp [nativeListInRe, impl_native_string_to_values, nativeListInReConcat,
        native_re_nullable_mk_concat]
  | c :: cs, r, s => by
      change
        nativeListInRe cs
            (native_re_deriv c (native_re_mk_concat r s)) =
          ((native_re_nullable r &&
              nativeListInRe cs (native_re_deriv c s)) ||
            nativeListInReConcat cs (native_re_deriv c r) s)
      rw [nativeListInRe_deriv_mk_concat cs c r s]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat cs (native_re_deriv c r) s]
      cases hNullable : native_re_nullable r <;>
        simp [nativeListInRe_empty, Bool.or_comm]

private theorem nativeListInReConcat_true_iff_exists_append :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInReConcat xs r s = true ↔
        ∃ xs1 xs2 : List native_Char,
          xs1 ++ xs2 = xs ∧
            nativeListInRe xs1 r = true ∧
            nativeListInRe xs2 s = true
  | [], r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.and_eq_true] at h
        exact ⟨[], [], by rfl, by simpa [nativeListInRe] using h.1,
          by simpa [nativeListInRe] using h.2⟩
      · intro h
        rcases h with ⟨xs1, xs2, hAppend, hLeft, hRight⟩
        cases xs1 with
        | nil =>
            cases xs2 with
            | nil =>
                simp [nativeListInReConcat, nativeListInRe] at hLeft hRight ⊢
                simp [hLeft, hRight]
            | cons _ _ =>
                simp at hAppend
        | cons _ _ =>
            simp at hAppend
  | c :: cs, r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with hHead | hTail
        · exact ⟨[], c :: cs, by rfl,
            by simpa [nativeListInRe] using hHead.1, hHead.2⟩
        · have hTailExists :=
            (nativeListInReConcat_true_iff_exists_append cs
              (native_re_deriv c r) s).1 hTail
          rcases hTailExists with ⟨xs1, xs2, hAppend, hLeft, hRight⟩
          exact ⟨c :: xs1, xs2, by simp [hAppend],
            by simpa [nativeListInRe] using hLeft, hRight⟩
      · intro h
        rcases h with ⟨xs1, xs2, hAppend, hLeft, hRight⟩
        cases xs1 with
        | nil =>
            cases xs2 with
            | nil =>
                simp at hAppend
            | cons _ _ =>
                cases hAppend
                have hNullable : native_re_nullable r = true := by
                  simpa [nativeListInRe] using hLeft
                simp [nativeListInReConcat, hNullable, hRight]
        | cons _ ds =>
            cases hAppend
            have hLeftDeriv :
                nativeListInRe ds (native_re_deriv c r) = true := by
              simpa [nativeListInRe] using hLeft
            have hTail :
                nativeListInReConcat (ds ++ xs2) (native_re_deriv c r) s =
                  true :=
              (nativeListInReConcat_true_iff_exists_append (ds ++ xs2)
                (native_re_deriv c r) s).2
                ⟨ds, xs2, by rfl, hLeftDeriv, hRight⟩
            simp [nativeListInReConcat, hTail]

private theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs1 xs2 : List native_Char,
        xs1 ++ xs2 = xs ∧
          nativeListInRe xs1 r = true ∧
          nativeListInRe xs2 s = true := by
  rw [nativeListInRe_mk_concat xs r s]
  exact nativeListInReConcat_true_iff_exists_append xs r s

private theorem nativeListInRe_mk_concat_assoc
    (xs : List native_Char) (r s t : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat (native_re_mk_concat r s) t) =
      nativeListInRe xs (native_re_mk_concat r (native_re_mk_concat s t)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs
        (native_re_mk_concat r s) t).1 h with
      ⟨xrs, xt, hAppend, hrs, ht⟩
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xrs r s).1 hrs with
      ⟨xr, xs', hAppendRS, hr, hs⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r
      (native_re_mk_concat s t)).2
    refine ⟨xr, xs' ++ xt, ?_, hr, ?_⟩
    · rw [← List.append_assoc, hAppendRS, hAppend]
    · exact
        (nativeListInRe_mk_concat_true_iff_exists_append (xs' ++ xt) s t).2
          ⟨xs', xt, rfl, hs, ht⟩
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r
        (native_re_mk_concat s t)).1 h with
      ⟨xr, xst, hAppend, hr, hst⟩
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xst s t).1 hst with
      ⟨xs', xt, hAppendST, hs, ht⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs
      (native_re_mk_concat r s) t).2
    refine ⟨xr ++ xs', xt, ?_, ?_, ht⟩
    · rw [List.append_assoc, hAppendST, hAppend]
    · exact
        (nativeListInRe_mk_concat_true_iff_exists_append (xr ++ xs') r s).2
          ⟨xr, xs', rfl, hr, hs⟩

private theorem nativeListInRe_mk_concat_congr_valid
    (xs : List native_Char) (r r' s s' : SmtRegLan)
    (hxs : native_string_valid xs = true)
    (hr :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys r = nativeListInRe ys r')
    (hs :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys s = nativeListInRe ys s') :
    nativeListInRe xs (native_re_mk_concat r s) =
      nativeListInRe xs (native_re_mk_concat r' s') := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r s).1 h
        with ⟨xs1, xs2, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (xs1 ++ xs2) = true := by
      rw [hAppend]
      exact hxs
    have hValid1 := native_string_valid_append_left xs1 xs2 hAppendValid
    have hValid2 := native_string_valid_append_right xs1 xs2 hAppendValid
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r' s').2
    refine ⟨xs1, xs2, hAppend, ?_, ?_⟩
    · rwa [← hr xs1 hValid1]
    · rwa [← hs xs2 hValid2]
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r' s').1 h
        with ⟨xs1, xs2, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (xs1 ++ xs2) = true := by
      rw [hAppend]
      exact hxs
    have hValid1 := native_string_valid_append_left xs1 xs2 hAppendValid
    have hValid2 := native_string_valid_append_right xs1 xs2 hAppendValid
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r s).2
    refine ⟨xs1, xs2, hAppend, ?_, ?_⟩
    · rwa [hr xs1 hValid1]
    · rwa [hs xs2 hValid2]

private theorem nativeListInRe_raw_star_append :
    (xs ys : List native_Char) -> (r : SmtRegLan) ->
      nativeListInRe xs (SmtRegLan.star r) = true ->
      nativeListInRe ys (SmtRegLan.star r) = true ->
      nativeListInRe (xs ++ ys) (SmtRegLan.star r) = true
  | [], ys, r, _hLeft, hRight => by
      simpa using hRight
  | c :: cs, ys, r, hLeft, hRight => by
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true := by
        simpa [nativeListInRe, native_re_deriv] using hLeft
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
        ⟨xs1, xs2, hAppend, hChunk, hTail⟩
      have hLen : xs2.length < (c :: cs).length := by
        have hLenEq := congrArg List.length hAppend
        simp at hLenEq ⊢
        omega
      have hTailAppend :
          nativeListInRe (xs2 ++ ys) (SmtRegLan.star r) = true :=
        nativeListInRe_raw_star_append xs2 ys r hTail hRight
      have hAppend' : xs1 ++ (xs2 ++ ys) = cs ++ ys := by
        rw [← List.append_assoc, hAppend]
      have hConcat' :
          nativeListInRe (cs ++ ys)
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true :=
        (nativeListInRe_mk_concat_true_iff_exists_append (cs ++ ys)
          (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨xs1, xs2 ++ ys, hAppend', hChunk, hTailAppend⟩
      simpa [nativeListInRe, native_re_deriv] using hConcat'
termination_by xs _ _ _ _ => xs.length
decreasing_by
  all_goals
    omega

private theorem nativeListInRe_concat_star_absorb
    (xs : List native_Char) (a r : SmtRegLan) :
    nativeListInRe xs
        (native_re_mk_concat
          (native_re_mk_concat a (SmtRegLan.star r))
          (SmtRegLan.star r)) =
      nativeListInRe xs (native_re_mk_concat a (SmtRegLan.star r)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs
        (native_re_mk_concat a (SmtRegLan.star r)) (SmtRegLan.star r)).1 h with
      ⟨xs1, xs2, hAppend, hLeft, hRight⟩
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs1
        a (SmtRegLan.star r)).1 hLeft with
      ⟨ys1, ys2, hAppendLeft, hA, hStarLeft⟩
    have hStar :
        nativeListInRe (ys2 ++ xs2) (SmtRegLan.star r) = true :=
      nativeListInRe_raw_star_append ys2 xs2 r hStarLeft hRight
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs
      a (SmtRegLan.star r)).2
    refine ⟨ys1, ys2 ++ xs2, ?_, hA, hStar⟩
    rw [← List.append_assoc, hAppendLeft, hAppend]
  · intro h
    have hNil : nativeListInRe [] (SmtRegLan.star r) = true := by
      simp [nativeListInRe, impl_native_string_to_values, native_re_nullable]
    exact (nativeListInRe_mk_concat_true_iff_exists_append xs
      (native_re_mk_concat a (SmtRegLan.star r)) (SmtRegLan.star r)).2
      ⟨xs, [], by simp, h, hNil⟩

private theorem native_str_in_re_mk_union_sem
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

private theorem native_str_in_re_mk_inter_sem
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_mk_inter str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

private theorem native_str_in_re_empty (str : native_String) :
    native_str_in_re str native_re_none = false := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, native_re_none, nativeListInRe] using
      nativeListInRe_empty str
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

private theorem smt_value_rel_re_union
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_union r s))
      (SmtValue.RegLan (native_re_union r' s')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  simp [native_str_in_re_mk_union_sem,
    smt_value_rel_reglan_valid_eq hr hValid,
    smt_value_rel_reglan_valid_eq hs hValid]

private theorem smt_value_rel_re_inter_comm
    (r s : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_inter r s))
      (SmtValue.RegLan (native_re_inter s r)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  simp [native_str_in_re_mk_inter_sem, Bool.and_comm]

private theorem smt_value_rel_deriv_union
    (c : native_Char) (ry rx dy dx : SmtRegLan)
    (hc : native_char_valid c = true)
    (hy : RuleProofs.smt_value_rel (SmtValue.RegLan dy)
      (SmtValue.RegLan (native_re_deriv c ry)))
    (hx : RuleProofs.smt_value_rel (SmtValue.RegLan dx)
      (SmtValue.RegLan (native_re_deriv c rx))) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_union dy dx))
      (SmtValue.RegLan (native_re_deriv c (native_re_union ry rx))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hCons : native_string_valid (c :: str) = true := by
    change (native_char_valid c && native_string_valid str) = true
    simp [hc, hValid]
  calc
    native_str_in_re str (native_re_union dy dx)
        = (native_str_in_re str dy || native_str_in_re str dx) := by
          rw [native_str_in_re_mk_union_sem]
    _ =
        (native_str_in_re str (native_re_deriv c ry) ||
          native_str_in_re str (native_re_deriv c rx)) := by
          rw [smt_value_rel_reglan_valid_eq hy hValid,
            smt_value_rel_reglan_valid_eq hx hValid]
    _ =
        (native_str_in_re (c :: str) ry ||
          native_str_in_re (c :: str) rx) := by
          rw [← native_str_in_re_cons (c := c) (cs := str) (r := ry) hCons,
            ← native_str_in_re_cons (c := c) (cs := str) (r := rx) hCons]
    _ = native_str_in_re (c :: str) (native_re_union ry rx) := by
          simpa [impl_native_string_to_values] using
            (native_str_in_re_mk_union_sem (c :: str) ry rx).symm
    _ = native_str_in_re str
        (native_re_deriv c (native_re_union ry rx)) := by
          rw [native_str_in_re_cons (c := c) (cs := str)
            (r := native_re_union ry rx) hCons]

private theorem smt_value_rel_deriv_inter
    (c : native_Char) (ry rx dy dx : SmtRegLan)
    (hc : native_char_valid c = true)
    (hy : RuleProofs.smt_value_rel (SmtValue.RegLan dy)
      (SmtValue.RegLan (native_re_deriv c ry)))
    (hx : RuleProofs.smt_value_rel (SmtValue.RegLan dx)
      (SmtValue.RegLan (native_re_deriv c rx))) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_inter dy dx))
      (SmtValue.RegLan (native_re_deriv c (native_re_inter ry rx))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hCons : native_string_valid (c :: str) = true := by
    change (native_char_valid c && native_string_valid str) = true
    simp [hc, hValid]
  calc
    native_str_in_re str (native_re_inter dy dx)
        = (native_str_in_re str dy && native_str_in_re str dx) := by
          rw [native_str_in_re_mk_inter_sem]
    _ =
        (native_str_in_re str (native_re_deriv c ry) &&
          native_str_in_re str (native_re_deriv c rx)) := by
          rw [smt_value_rel_reglan_valid_eq hy hValid,
            smt_value_rel_reglan_valid_eq hx hValid]
    _ =
        (native_str_in_re (c :: str) ry &&
          native_str_in_re (c :: str) rx) := by
          rw [← native_str_in_re_cons (c := c) (cs := str) (r := ry) hCons,
            ← native_str_in_re_cons (c := c) (cs := str) (r := rx) hCons]
    _ = native_str_in_re (c :: str) (native_re_inter ry rx) := by
          simpa [impl_native_string_to_values] using
            (native_str_in_re_mk_inter_sem (c :: str) ry rx).symm
    _ = native_str_in_re str
        (native_re_deriv c (native_re_inter ry rx)) := by
          rw [native_str_in_re_cons (c := c) (cs := str)
            (r := native_re_inter ry rx) hCons]

private abbrev mkReUnion (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) y

private abbrev mkReInter (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y

private abbrev mkReConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y

private theorem smt_reglan_ne_none : SmtType.RegLan ≠ SmtType.None := by
  intro h
  cases h

private theorem eo_eq_eq_true_of_eq_local {x y : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean true := by
  intro hEq hX hY
  subst y
  cases x <;> simp [__eo_eq, native_teq] at hX ⊢

private theorem eo_eq_eq_false_of_ne_local {x y : Term} :
    x ≠ y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean false := by
  intro hNe hX hY
  by_cases hEq : x = y
  · exact False.elim (hNe hEq)
  · cases x <;> cases y <;>
      simp [__eo_eq, native_teq, eq_comm, hEq] at hNe hX hY ⊢ <;>
      contradiction

private theorem reUnion_typeof_of_args (x y : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt (mkReUnion x y)) = SmtType.RegLan := by
  intro hxTy hyTy
  change __smtx_typeof
      (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_union_eq]
  simp [hxTy, hyTy, native_ite, native_Teq]

private theorem reUnion_args_of_reglan_type (x y : Term) :
    __smtx_typeof (__eo_to_smt (mkReUnion x y)) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.RegLan := by
  intro hTy
  have hTy' :
      __smtx_typeof
          (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan := by
    simpa [mkReUnion] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    exact smt_reglan_ne_none
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
    (typeof_re_union_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

private theorem reInter_typeof_of_args (x y : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt (mkReInter x y)) = SmtType.RegLan := by
  intro hxTy hyTy
  change __smtx_typeof
      (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_inter_eq]
  simp [hxTy, hyTy, native_ite, native_Teq]

private theorem reInter_args_of_reglan_type (x y : Term) :
    __smtx_typeof (__eo_to_smt (mkReInter x y)) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.RegLan := by
  intro hTy
  have hTy' :
      __smtx_typeof
          (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan := by
    simpa [mkReInter] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    exact smt_reglan_ne_none
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
    (typeof_re_inter_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

private theorem reConcat_typeof_of_args (x y : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt (mkReConcat x y)) = SmtType.RegLan := by
  intro hxTy hyTy
  change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_concat_eq]
  simp [hxTy, hyTy, native_ite, native_Teq]

private theorem reConcat_args_of_reglan_type (x y : Term) :
    __smtx_typeof (__eo_to_smt (mkReConcat x y)) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.RegLan := by
  intro hTy
  have hTy' :
      __smtx_typeof
          (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan := by
    simpa [mkReConcat] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    exact smt_reglan_ne_none
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
    (typeof_re_concat_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

def RegLanEval (M : SmtModel) (t : Term) : Prop :=
  ∃ r, __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r

private def RegLanContains (M : SmtModel) (t : Term)
    (str : native_String) : Prop :=
  ∃ r, __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r ∧
    native_str_in_re str r = true

private theorem native_string_valid_of_reglan_contains
    {M : SmtModel} {t : Term} {str : native_String} :
    RegLanContains M t str ->
    native_string_valid str = true := by
  intro hIn
  rcases hIn with ⟨r, _hEval, hMem⟩
  by_cases hValid : native_string_valid str = true
  · exact hValid
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid] at hMem

private theorem regLanEval_ne_stuck {M : SmtModel} {t : Term} :
    RegLanEval M t -> t ≠ Term.Stuck := by
  intro hEval hStuck
  rcases hEval with ⟨r, hEval⟩
  subst t
  change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan r at hEval
  simp [__smtx_model_eval] at hEval

private theorem reUnion_eval_reglan_of_reglan_args
    (M : SmtModel) (x y : Term) :
    RegLanEval M x ->
    RegLanEval M y ->
    RegLanEval M (mkReUnion x y) := by
  intro hx hy
  rcases hx with ⟨rx, hxEval⟩
  rcases hy with ⟨ry, hyEval⟩
  exact ⟨native_re_union rx ry, by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.RegLan (native_re_union rx ry)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hxEval, hyEval]⟩

private theorem reInter_eval_reglan_of_reglan_args
    (M : SmtModel) (x y : Term) :
    RegLanEval M x ->
    RegLanEval M y ->
    RegLanEval M (mkReInter x y) := by
  intro hx hy
  rcases hx with ⟨rx, hxEval⟩
  rcases hy with ⟨ry, hyEval⟩
  exact ⟨native_re_inter rx ry, by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.RegLan (native_re_inter rx ry)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hxEval, hyEval]⟩

private theorem reConcat_eval_reglan_of_reglan_args
    (M : SmtModel) (x y : Term) :
    RegLanEval M x ->
    RegLanEval M y ->
    RegLanEval M (mkReConcat x y) := by
  intro hx hy
  rcases hx with ⟨rx, hxEval⟩
  rcases hy with ⟨ry, hyEval⟩
  exact ⟨native_re_concat rx ry, by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.RegLan (native_re_concat rx ry)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hxEval, hyEval]⟩

private theorem smt_value_rel_re_concat
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat r s))
      (SmtValue.RegLan (native_re_concat r' s')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  simpa [native_str_in_re, hValid, native_re_concat, native_re_mk_concat,
    nativeListInRe] using
    nativeListInRe_mk_concat_congr_valid str r r' s s' hValid
      (by
        intro ys hys
        simpa [native_str_in_re, hys, nativeListInRe] using
          smt_value_rel_reglan_valid_eq hr hys)
      (by
        intro ys hys
        simpa [native_str_in_re, hys, nativeListInRe] using
          smt_value_rel_reglan_valid_eq hs hys)

private theorem smt_value_rel_re_concat_assoc
    (r s t : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat (native_re_concat r s) t))
      (SmtValue.RegLan (native_re_concat r (native_re_concat s t))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  simpa [native_str_in_re, hValid, native_re_concat, native_re_mk_concat,
    nativeListInRe] using
    nativeListInRe_mk_concat_assoc str r s t

private theorem smt_value_rel_reglan_native_union_of_contains_iff
    (M : SmtModel) (t a b : Term) (r ra rb : SmtRegLan)
    (hTEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hContains :
      ∀ str,
        RegLanContains M t str ↔
          RegLanContains M a str ∨ RegLanContains M b str) :
    RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan (native_re_union ra rb)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str _hValid
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hIn
    have hTIn : RegLanContains M t str := ⟨r, hTEval, hIn⟩
    rcases (hContains str).1 hTIn with hAIn | hBIn
    · rcases hAIn with ⟨ra', hAEval', hAIn'⟩
      rw [hAEval] at hAEval'
      cases hAEval'
      rw [native_str_in_re_mk_union_sem]
      simp [hAIn']
    · rcases hBIn with ⟨rb', hBEval', hBIn'⟩
      rw [hBEval] at hBEval'
      cases hBEval'
      rw [native_str_in_re_mk_union_sem]
      simp [hBIn']
  · intro hIn
    rw [native_str_in_re_mk_union_sem] at hIn
    simp only [Bool.or_eq_true] at hIn
    rcases hIn with hAIn | hBIn
    · rcases (hContains str).2 (Or.inl ⟨ra, hAEval, hAIn⟩) with
        ⟨r', hTEval', hTIn⟩
      rw [hTEval] at hTEval'
      cases hTEval'
      exact hTIn
    · rcases (hContains str).2 (Or.inr ⟨rb, hBEval, hBIn⟩) with
        ⟨r', hTEval', hTIn⟩
      rw [hTEval] at hTEval'
      cases hTEval'
      exact hTIn

private theorem smt_value_rel_reglan_native_inter_of_contains_iff
    (M : SmtModel) (t a b : Term) (r ra rb : SmtRegLan)
    (hTEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hContains :
      ∀ str,
        RegLanContains M t str ↔
          RegLanContains M a str ∧ RegLanContains M b str) :
    RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan (native_re_inter ra rb)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str _hValid
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hIn
    have hTIn : RegLanContains M t str := ⟨r, hTEval, hIn⟩
    rcases (hContains str).1 hTIn with ⟨hAIn, hBIn⟩
    rcases hAIn with ⟨ra', hAEval', hAIn'⟩
    rcases hBIn with ⟨rb', hBEval', hBIn'⟩
    rw [hAEval] at hAEval'
    rw [hBEval] at hBEval'
    cases hAEval'
    cases hBEval'
    rw [native_str_in_re_mk_inter_sem]
    simp [hAIn', hBIn']
  · intro hIn
    rw [native_str_in_re_mk_inter_sem] at hIn
    simp only [Bool.and_eq_true] at hIn
    rcases hIn with ⟨hAIn, hBIn⟩
    rcases (hContains str).2
        ⟨⟨ra, hAEval, hAIn⟩, ⟨rb, hBEval, hBIn⟩⟩ with
      ⟨r', hTEval', hTIn⟩
    rw [hTEval] at hTEval'
    cases hTEval'
    exact hTIn

private theorem reUnion_contains_left
    (M : SmtModel) (x y : Term) (str : native_String) :
    RegLanEval M x ->
    RegLanEval M y ->
    RegLanContains M x str ->
    RegLanContains M (mkReUnion x y) str := by
  intro hxEval hyEval hxIn
  rcases hxEval with ⟨rx, hxEval⟩
  rcases hyEval with ⟨ry, hyEval⟩
  rcases hxIn with ⟨rx', hxEval', hxIn⟩
  rw [hxEval] at hxEval'
  cases hxEval'
  exact ⟨native_re_union rx ry, by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.RegLan (native_re_union rx ry)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hxEval, hyEval],
    by
      simp [native_str_in_re_mk_union_sem, hxIn]⟩

private theorem reUnion_contains_right
    (M : SmtModel) (x y : Term) (str : native_String) :
    RegLanEval M x ->
    RegLanEval M y ->
    RegLanContains M y str ->
    RegLanContains M (mkReUnion x y) str := by
  intro hxEval hyEval hyIn
  rcases hxEval with ⟨rx, hxEval⟩
  rcases hyEval with ⟨ry, hyEval⟩
  rcases hyIn with ⟨ry', hyEval', hyIn⟩
  rw [hyEval] at hyEval'
  cases hyEval'
  exact ⟨native_re_union rx ry, by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.RegLan (native_re_union rx ry)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hxEval, hyEval],
    by
      simp [native_str_in_re_mk_union_sem, hyIn]⟩

private theorem reUnion_contains_cases
    (M : SmtModel) (x y : Term) (str : native_String) :
    RegLanEval M x ->
    RegLanEval M y ->
    RegLanContains M (mkReUnion x y) str ->
      RegLanContains M x str ∨ RegLanContains M y str := by
  intro hxEval hyEval hIn
  rcases hxEval with ⟨rx, hxEval⟩
  rcases hyEval with ⟨ry, hyEval⟩
  rcases hIn with ⟨r, hEval, hIn⟩
  change __smtx_model_eval M
      (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)) =
    SmtValue.RegLan r at hEval
  simp only [__smtx_model_eval, __smtx_model_eval_re_union, hxEval, hyEval] at hEval
  cases hEval
  simp [native_str_in_re_mk_union_sem, Bool.or_eq_true] at hIn
  rcases hIn with hxIn | hyIn
  · exact Or.inl ⟨rx, hxEval, hxIn⟩
  · exact Or.inr ⟨ry, hyEval, hyIn⟩

private theorem reInter_contains
    (M : SmtModel) (x y : Term) (str : native_String) :
    RegLanEval M x ->
    RegLanEval M y ->
    RegLanContains M x str ->
    RegLanContains M y str ->
    RegLanContains M (mkReInter x y) str := by
  intro hxEval hyEval hxIn hyIn
  rcases hxEval with ⟨rx, hxEval⟩
  rcases hyEval with ⟨ry, hyEval⟩
  rcases hxIn with ⟨rx', hxEval', hxIn⟩
  rcases hyIn with ⟨ry', hyEval', hyIn⟩
  rw [hxEval] at hxEval'
  rw [hyEval] at hyEval'
  cases hxEval'
  cases hyEval'
  exact ⟨native_re_inter rx ry, by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.RegLan (native_re_inter rx ry)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hxEval, hyEval],
    by
      simp [native_str_in_re_mk_inter_sem, hxIn, hyIn]⟩

private theorem reInter_contains_cases
    (M : SmtModel) (x y : Term) (str : native_String) :
    RegLanEval M x ->
    RegLanEval M y ->
    RegLanContains M (mkReInter x y) str ->
      RegLanContains M x str ∧ RegLanContains M y str := by
  intro hxEval hyEval hIn
  rcases hxEval with ⟨rx, hxEval⟩
  rcases hyEval with ⟨ry, hyEval⟩
  rcases hIn with ⟨r, hEval, hIn⟩
  change __smtx_model_eval M
      (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
    SmtValue.RegLan r at hEval
  simp only [__smtx_model_eval, __smtx_model_eval_re_inter, hxEval, hyEval] at hEval
  cases hEval
  simp [native_str_in_re_mk_inter_sem, Bool.and_eq_true] at hIn
  exact ⟨⟨rx, hxEval, hIn.1⟩, ⟨ry, hyEval, hIn.2⟩⟩

private def ReUnionListWF (M : SmtModel) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) xs =>
      RegLanEval M x ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
        ReUnionListWF M xs
  | t =>
      RegLanEval M t ∧
        __smtx_typeof (__eo_to_smt t) = SmtType.RegLan

private theorem reUnionListWF_eval_type
    (M : SmtModel) :
    (t : Term) -> ReUnionListWF M t ->
      RegLanEval M t ∧
        __smtx_typeof (__eo_to_smt t) = SmtType.RegLan
  | t, h => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case re_union =>
                    have hXs := reUnionListWF_eval_type M xs h.2.2
                    exact ⟨
                      reUnion_eval_reglan_of_reglan_args M x xs h.1 hXs.1,
                      reUnion_typeof_of_args x xs h.2.1 hXs.2⟩
                  all_goals
                    simpa [ReUnionListWF] using h
              | _ =>
                  simpa [ReUnionListWF] using h
          | _ =>
              simpa [ReUnionListWF] using h
      | _ =>
          simpa [ReUnionListWF] using h

private theorem reUnionListWF_eval
    {M : SmtModel} {t : Term} :
    ReUnionListWF M t -> RegLanEval M t := by
  intro h
  exact (reUnionListWF_eval_type M t h).1

private theorem reUnionListWF_type
    {M : SmtModel} {t : Term} :
    ReUnionListWF M t ->
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan := by
  intro h
  exact (reUnionListWF_eval_type M t h).2

private theorem reUnionListWF_of_type_eval
    (M : SmtModel) :
    (t : Term) -> (r : SmtRegLan) ->
      __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r ->
      ReUnionListWF M t
  | t, r, hTy, hEval => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case re_union =>
                    have hArgs := reUnion_args_of_reglan_type x xs hTy
                    change __smtx_model_eval M
                        (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt xs)) =
                      SmtValue.RegLan r at hEval
                    cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
                      cases hxs : __smtx_model_eval M (__eo_to_smt xs) <;>
                        simp [__smtx_model_eval, __smtx_model_eval_re_union,
                          hx, hxs] at hEval
                    case RegLan.RegLan rx rxs =>
                      exact ⟨⟨rx, hx⟩, hArgs.1,
                        reUnionListWF_of_type_eval M xs rxs hArgs.2 hxs⟩
                  all_goals
                    exact ⟨⟨r, hEval⟩, hTy⟩
              | _ =>
                  exact ⟨⟨r, hEval⟩, hTy⟩
          | _ =>
              exact ⟨⟨r, hEval⟩, hTy⟩
      | _ =>
          exact ⟨⟨r, hEval⟩, hTy⟩

private def ReInterListWF (M : SmtModel) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) xs =>
      RegLanEval M x ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
        ReInterListWF M xs
  | t =>
      RegLanEval M t ∧
        __smtx_typeof (__eo_to_smt t) = SmtType.RegLan

private theorem reInterListWF_eval_type
    (M : SmtModel) :
    (t : Term) -> ReInterListWF M t ->
      RegLanEval M t ∧
        __smtx_typeof (__eo_to_smt t) = SmtType.RegLan
  | t, h => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case re_inter =>
                    have hXs := reInterListWF_eval_type M xs h.2.2
                    exact ⟨
                      reInter_eval_reglan_of_reglan_args M x xs h.1 hXs.1,
                      reInter_typeof_of_args x xs h.2.1 hXs.2⟩
                  all_goals
                    simpa [ReInterListWF] using h
              | _ =>
                  simpa [ReInterListWF] using h
          | _ =>
              simpa [ReInterListWF] using h
      | _ =>
          simpa [ReInterListWF] using h

private theorem reInterListWF_eval
    {M : SmtModel} {t : Term} :
    ReInterListWF M t -> RegLanEval M t := by
  intro h
  exact (reInterListWF_eval_type M t h).1

private theorem reInterListWF_type
    {M : SmtModel} {t : Term} :
    ReInterListWF M t ->
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan := by
  intro h
  exact (reInterListWF_eval_type M t h).2

private theorem reInterListWF_of_type_eval
    (M : SmtModel) :
    (t : Term) -> (r : SmtRegLan) ->
      __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r ->
      ReInterListWF M t
  | t, r, hTy, hEval => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case re_inter =>
                    have hArgs := reInter_args_of_reglan_type x xs hTy
                    change __smtx_model_eval M
                        (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt xs)) =
                      SmtValue.RegLan r at hEval
                    cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
                      cases hxs : __smtx_model_eval M (__eo_to_smt xs) <;>
                        simp [__smtx_model_eval, __smtx_model_eval_re_inter,
                          hx, hxs] at hEval
                    case RegLan.RegLan rx rxs =>
                      exact ⟨⟨rx, hx⟩, hArgs.1,
                        reInterListWF_of_type_eval M xs rxs hArgs.2 hxs⟩
                  all_goals
                    exact ⟨⟨r, hEval⟩, hTy⟩
              | _ =>
                  exact ⟨⟨r, hEval⟩, hTy⟩
          | _ =>
              exact ⟨⟨r, hEval⟩, hTy⟩
      | _ =>
          exact ⟨⟨r, hEval⟩, hTy⟩

private def ReConcatListWF (M : SmtModel) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) xs =>
      RegLanEval M x ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
        ReConcatListWF M xs
  | t =>
      RegLanEval M t ∧
        __smtx_typeof (__eo_to_smt t) = SmtType.RegLan

private theorem reConcatListWF_eval_type
    (M : SmtModel) :
    (t : Term) -> ReConcatListWF M t ->
      RegLanEval M t ∧
        __smtx_typeof (__eo_to_smt t) = SmtType.RegLan
  | t, h => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case re_concat =>
                    have hXs := reConcatListWF_eval_type M xs h.2.2
                    exact ⟨
                      reConcat_eval_reglan_of_reglan_args M x xs h.1 hXs.1,
                      reConcat_typeof_of_args x xs h.2.1 hXs.2⟩
                  all_goals
                    simpa [ReConcatListWF] using h
              | _ =>
                  simpa [ReConcatListWF] using h
          | _ =>
              simpa [ReConcatListWF] using h
      | _ =>
          simpa [ReConcatListWF] using h

private theorem reConcatListWF_eval
    {M : SmtModel} {t : Term} :
    ReConcatListWF M t -> RegLanEval M t := by
  intro h
  exact (reConcatListWF_eval_type M t h).1

private theorem reConcatListWF_type
    {M : SmtModel} {t : Term} :
    ReConcatListWF M t ->
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan := by
  intro h
  exact (reConcatListWF_eval_type M t h).2

private theorem reConcatListWF_of_type_eval
    (M : SmtModel) :
    (t : Term) -> (r : SmtRegLan) ->
      __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r ->
      ReConcatListWF M t
  | t, r, hTy, hEval => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case re_concat =>
                    have hArgs := reConcat_args_of_reglan_type x xs hTy
                    change __smtx_model_eval M
                        (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt xs)) =
                      SmtValue.RegLan r at hEval
                    cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
                      cases hxs : __smtx_model_eval M (__eo_to_smt xs) <;>
                        simp [__smtx_model_eval, __smtx_model_eval_re_concat,
                          hx, hxs] at hEval
                    case RegLan.RegLan rx rxs =>
                      exact ⟨⟨rx, hx⟩, hArgs.1,
                        reConcatListWF_of_type_eval M xs rxs hArgs.2 hxs⟩
                  all_goals
                    exact ⟨⟨r, hEval⟩, hTy⟩
              | _ =>
                  exact ⟨⟨r, hEval⟩, hTy⟩
          | _ =>
              exact ⟨⟨r, hEval⟩, hTy⟩
      | _ =>
          exact ⟨⟨r, hEval⟩, hTy⟩

private theorem reConcat_nil_eq_empty_of_is_list_nil_true {nil : Term} :
    __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true ->
    nil = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
  intro hNil
  cases nil <;> try cases hNil
  case Apply f x =>
    cases f <;> try cases hNil
    case UOp op =>
      cases op <;> try cases hNil
      case str_to_re =>
        cases x <;> try cases hNil
        case String s =>
          cases s with
          | nil =>
            rfl
          | cons c cs =>
            cases hNil

private theorem reConcat_nil_eval_empty_of_is_list_nil_true
    (M : SmtModel) (nil : Term) :
    __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.RegLan (native_str_to_re []) := by
  intro hNilTrue
  have hNilEq := reConcat_nil_eq_empty_of_is_list_nil_true hNilTrue
  subst nil
  change __smtx_model_eval M
      (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtValue.RegLan (native_str_to_re [])
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
    ]

private theorem reConcat_list_concat_rec_rel_eval
    (M : SmtModel) :
    (a z : Term) ->
    __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.re_concat) z = Term.Boolean true ->
    ReConcatListWF M a ->
    ReConcatListWF M z ->
    __eo_is_list (Term.UOp UserOp.re_concat) (__eo_list_concat_rec a z) =
        Term.Boolean true ∧
      ReConcatListWF M (__eo_list_concat_rec a z) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
        (__smtx_model_eval M (__eo_to_smt (mkReConcat a z)))
  | a, z, hAList, hZList, hAWF, hZWF => by
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          cases (Term.UOp UserOp.re_concat) <;> simp [__eo_is_list] at hAList
      | case2 a hA =>
          cases (Term.UOp UserOp.re_concat) <;> simp [__eo_is_list] at hZList
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.re_concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_concat) g x y hAList
          subst g
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_concat) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_concat) x y hAList
          have hTailNe :
              __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list
              (Term.UOp UserOp.re_concat) y z hYList hZ
          have hXEval : RegLanEval M x := hAWF.1
          have hXTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
            hAWF.2.1
          have hYWF : ReConcatListWF M y := hAWF.2.2
          have hYEval : RegLanEval M y := reConcatListWF_eval hYWF
          have hZEval : RegLanEval M z := reConcatListWF_eval hZWF
          have hIH := ih hYList hZList hYWF hZWF
          rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
            (Term.UOp UserOp.re_concat) x y z hTailNe]
          have hTailWF :
              ReConcatListWF M (__eo_list_concat_rec y z) := hIH.2.1
          have hTailEval :
              RegLanEval M (__eo_list_concat_rec y z) :=
            reConcatListWF_eval hTailWF
          rcases hXEval with ⟨rx, hxEval⟩
          rcases hYEval with ⟨ry, hyEval⟩
          rcases hZEval with ⟨rz, hzEval⟩
          rcases hTailEval with ⟨rtail, hTailEval⟩
          have hYZEval :
              __smtx_model_eval M (__eo_to_smt (mkReConcat y z)) =
                SmtValue.RegLan (native_re_concat ry rz) := by
            change __smtx_model_eval M
                (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt z)) =
              SmtValue.RegLan (native_re_concat ry rz)
            simp [__smtx_model_eval, __smtx_model_eval_re_concat,
              hyEval, hzEval]
          have hTailRel :
              RuleProofs.smt_value_rel (SmtValue.RegLan rtail)
                (SmtValue.RegLan (native_re_concat ry rz)) := by
            have h := hIH.2.2
            rw [hTailEval, hYZEval] at h
            exact h
          have hLeftEval :
              __smtx_model_eval M
                  (__eo_to_smt
                    (mkReConcat x (__eo_list_concat_rec y z))) =
                SmtValue.RegLan (native_re_concat rx rtail) := by
            change __smtx_model_eval M
                (SmtTerm.re_concat (__eo_to_smt x)
                  (__eo_to_smt (__eo_list_concat_rec y z))) =
              SmtValue.RegLan (native_re_concat rx rtail)
            simp [__smtx_model_eval, __smtx_model_eval_re_concat,
              hxEval, hTailEval]
          have hRightEval :
              __smtx_model_eval M
                  (__eo_to_smt (mkReConcat x (mkReConcat y z))) =
                SmtValue.RegLan
                  (native_re_concat rx (native_re_concat ry rz)) := by
            change __smtx_model_eval M
                (SmtTerm.re_concat (__eo_to_smt x)
                  (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt z))) =
              SmtValue.RegLan
                (native_re_concat rx (native_re_concat ry rz))
            simp [__smtx_model_eval, __smtx_model_eval_re_concat,
              hxEval, hyEval, hzEval]
          have hAssocRightEval :
              __smtx_model_eval M
                  (__eo_to_smt (mkReConcat (mkReConcat x y) z)) =
                SmtValue.RegLan
                  (native_re_concat (native_re_concat rx ry) rz) := by
            change __smtx_model_eval M
                (SmtTerm.re_concat
                  (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt y))
                  (__eo_to_smt z)) =
              SmtValue.RegLan
                (native_re_concat (native_re_concat rx ry) rz)
            simp [__smtx_model_eval, __smtx_model_eval_re_concat,
              hxEval, hyEval, hzEval]
          have hCongr :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkReConcat x (__eo_list_concat_rec y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkReConcat x (mkReConcat y z)))) := by
            rw [hLeftEval, hRightEval]
            exact smt_value_rel_re_concat
              (RuleProofs.smt_value_rel_refl (SmtValue.RegLan rx)) hTailRel
          have hAssoc :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkReConcat x (mkReConcat y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkReConcat (mkReConcat x y) z))) := by
            rw [hRightEval, hAssocRightEval]
            exact RuleProofs.smt_value_rel_symm _ _
              (smt_value_rel_re_concat_assoc rx ry rz)
          exact ⟨
            eo_is_list_cons_self_true_of_tail_list
              (Term.UOp UserOp.re_concat) x (__eo_list_concat_rec y z)
              (by decide) hIH.1,
            ⟨⟨rx, hxEval⟩, hXTy, hIH.2.1⟩,
            RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M
                (__eo_to_smt (mkReConcat x (__eo_list_concat_rec y z))))
              (__smtx_model_eval M
                (__eo_to_smt (mkReConcat x (mkReConcat y z))))
              (__smtx_model_eval M
                (__eo_to_smt (mkReConcat (mkReConcat x y) z)))
              hCongr hAssoc⟩
      | case4 nil z hNil hZ hNot =>
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
                Term.Boolean true := by
            have hGet :=
              eo_get_nil_rec_ne_stuck_of_is_list_true
                (Term.UOp UserOp.re_concat) nil hAList
            have hReq :
                __eo_requires
                    (__eo_is_list_nil (Term.UOp UserOp.re_concat) nil)
                    (Term.Boolean true) nil ≠ Term.Stuck := by
              simpa [__eo_get_nil_rec] using hGet
            exact eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.re_concat) nil)
              (Term.Boolean true) nil hReq
          have hConcatEq : __eo_list_concat_rec nil z = z := by
            have hNilEq :=
              reConcat_nil_eq_empty_of_is_list_nil_true hNilTrue
            subst nil
            cases z <;> rfl
          rw [hConcatEq]
          rcases reConcatListWF_eval hZWF with ⟨rz, hzEval⟩
          have hNilEval :=
            reConcat_nil_eval_empty_of_is_list_nil_true M nil hNilTrue
          have hConcatEval :
              __smtx_model_eval M (__eo_to_smt (mkReConcat nil z)) =
                SmtValue.RegLan (native_re_concat (native_str_to_re []) rz) := by
            change __smtx_model_eval M
                (SmtTerm.re_concat (__eo_to_smt nil) (__eo_to_smt z)) =
              SmtValue.RegLan (native_re_concat (native_str_to_re []) rz)
            simp [__smtx_model_eval, __smtx_model_eval_re_concat,
              hNilEval, hzEval]
          have hNative :
              native_re_concat (native_str_to_re []) rz = rz := by
            simpa [native_str_to_re, impl_native_re_of_list] using
              native_re_mk_concat_left_epsilon rz
          have hLeftRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt (mkReConcat nil z)))
                (__smtx_model_eval M (__eo_to_smt z)) := by
            rw [hConcatEval, hNative, hzEval]
            exact RuleProofs.smt_value_rel_refl (SmtValue.RegLan rz)
          exact ⟨hZList, hZWF,
            RuleProofs.smt_value_rel_symm _ _ hLeftRel⟩

theorem reConcat_list_concat_rec_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hAList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (hBList :
      __eo_is_list (Term.UOp UserOp.re_concat) b = Term.Boolean true)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt (__eo_list_concat_rec a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_concat ra rb)) := by
  have hAWF : ReConcatListWF M a :=
    reConcatListWF_of_type_eval M a ra hATy hAEval
  have hBWF : ReConcatListWF M b :=
    reConcatListWF_of_type_eval M b rb hBTy hBEval
  have hConcat :=
    reConcat_list_concat_rec_rel_eval M a b hAList hBList hAWF hBWF
  rcases reConcatListWF_eval hConcat.2.1 with ⟨r, hRecEval⟩
  have hMkEval :
      __smtx_model_eval M (__eo_to_smt (mkReConcat a b)) =
        SmtValue.RegLan (native_re_concat ra rb) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.RegLan (native_re_concat ra rb)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hAEval, hBEval]
  have hRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_concat ra rb)) := by
    have h := hConcat.2.2
    rw [hRecEval, hMkEval] at h
    exact h
  exact ⟨r, hRecEval, reConcatListWF_type hConcat.2.1, hRel⟩

theorem reConcat_list_concat_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hAList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (hBList :
      __eo_is_list (Term.UOp UserOp.re_concat) b = Term.Boolean true)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_concat) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_concat) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_concat ra rb)) := by
  have hAWF : ReConcatListWF M a :=
    reConcatListWF_of_type_eval M a ra hATy hAEval
  have hBWF : ReConcatListWF M b :=
    reConcatListWF_of_type_eval M b rb hBTy hBEval
  have hConcat :=
    reConcat_list_concat_rec_rel_eval M a b hAList hBList hAWF hBWF
  have hConcatEq :
      __eo_list_concat (Term.UOp UserOp.re_concat) a b =
        __eo_list_concat_rec a b := by
    simp [__eo_list_concat, hAList, hBList, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not]
  rcases reConcatListWF_eval hConcat.2.1 with ⟨r, hRecEval⟩
  have hMkEval :
      __smtx_model_eval M (__eo_to_smt (mkReConcat a b)) =
        SmtValue.RegLan (native_re_concat ra rb) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.RegLan (native_re_concat ra rb)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hAEval, hBEval]
  have hRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_concat ra rb)) := by
    have h := hConcat.2.2
    rw [hRecEval, hMkEval] at h
    exact h
  refine ⟨r, ?_, ?_, hRel⟩
  · rw [hConcatEq]
    exact hRecEval
  · rw [hConcatEq]
    exact reConcatListWF_type hConcat.2.1

private theorem reUnion_is_list_true_ne_stuck {t : Term} :
    __eo_is_list (Term.UOp UserOp.re_union) t = Term.Boolean true ->
    t ≠ Term.Stuck := by
  intro hList hStuck
  subst t
  simp [__eo_is_list] at hList

private theorem reUnion_nil_eq_none_of_is_list_nil_true {nil : Term} :
    __eo_is_list_nil (Term.UOp UserOp.re_union) nil = Term.Boolean true ->
    nil = Term.UOp UserOp.re_none := by
  intro hNil
  cases nil <;> try cases hNil
  case UOp op =>
    cases op <;> try cases hNil
    rfl

private theorem reUnion_nil_eval_none_of_is_list_nil_true
    (M : SmtModel) (nil : Term) :
    __eo_is_list_nil (Term.UOp UserOp.re_union) nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.RegLan native_re_none := by
  intro hNilTrue
  have hNilEq := reUnion_nil_eq_none_of_is_list_nil_true hNilTrue
  subst nil
  change __smtx_model_eval M SmtTerm.re_none =
    SmtValue.RegLan native_re_none
  rw [__smtx_model_eval.eq_105]

private theorem reUnion_nil_not_contains
    (M : SmtModel) (nil : Term) (str : native_String) :
    __eo_is_list_nil (Term.UOp UserOp.re_union) nil = Term.Boolean true ->
    ¬ RegLanContains M nil str := by
  intro hNil hIn
  rcases hIn with ⟨r, hEval, hStr⟩
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.RegLan native_re_none :=
    reUnion_nil_eval_none_of_is_list_nil_true M nil hNil
  rw [hNilEval] at hEval
  cases hEval
  simpa [native_str_in_re_empty] using hStr

private theorem reUnion_list_concat_rec_wf_contains
    (M : SmtModel) :
    (a z : Term) ->
    __eo_is_list (Term.UOp UserOp.re_union) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.re_union) z = Term.Boolean true ->
    ReUnionListWF M a ->
    ReUnionListWF M z ->
    __eo_is_list (Term.UOp UserOp.re_union) (__eo_list_concat_rec a z) =
        Term.Boolean true ∧
      ReUnionListWF M (__eo_list_concat_rec a z) ∧
      ∀ str,
        RegLanContains M (__eo_list_concat_rec a z) str ↔
          RegLanContains M a str ∨ RegLanContains M z str
  | a, z, hAList, hZList, hAWF, hZWF => by
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          cases (Term.UOp UserOp.re_union) <;> simp [__eo_is_list] at hAList
      | case2 a hA =>
          cases (Term.UOp UserOp.re_union) <;> simp [__eo_is_list] at hZList
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.re_union :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_union) g x y hAList
          subst g
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_union) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_union) x y hAList
          have hTailNe :
              __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list
              (Term.UOp UserOp.re_union) y z hYList hZ
          have hXEval : RegLanEval M x := hAWF.1
          have hXTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
            hAWF.2.1
          have hYWF : ReUnionListWF M y := hAWF.2.2
          have hYEval : RegLanEval M y := reUnionListWF_eval hYWF
          have hIH := ih hYList hZList hYWF hZWF
          rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
            (Term.UOp UserOp.re_union) x y z hTailNe]
          have hTailWF :
              ReUnionListWF M (__eo_list_concat_rec y z) := hIH.2.1
          have hTailEval :
              RegLanEval M (__eo_list_concat_rec y z) :=
            reUnionListWF_eval hTailWF
          exact ⟨
            eo_is_list_cons_self_true_of_tail_list
              (Term.UOp UserOp.re_union) x (__eo_list_concat_rec y z)
              (by decide) hIH.1,
            ⟨hXEval, hXTy, hTailWF⟩,
            by
              intro str
              constructor
              · intro hIn
                rcases reUnion_contains_cases M x
                    (__eo_list_concat_rec y z) str hXEval hTailEval hIn with
                  hXIn | hTailIn
                · exact Or.inl
                    (reUnion_contains_left M x y str hXEval hYEval hXIn)
                · rcases (hIH.2.2 str).1 hTailIn with hYIn | hZIn
                  · exact Or.inl
                      (reUnion_contains_right M x y str hXEval hYEval hYIn)
                  · exact Or.inr hZIn
              · intro hIn
                rcases hIn with hAIn | hZIn
                · rcases reUnion_contains_cases M x y str hXEval hYEval hAIn with
                    hXIn | hYIn
                  · exact reUnion_contains_left M x
                      (__eo_list_concat_rec y z) str hXEval hTailEval hXIn
                  · have hTailIn :
                        RegLanContains M (__eo_list_concat_rec y z) str :=
                      (hIH.2.2 str).2 (Or.inl hYIn)
                    exact reUnion_contains_right M x
                      (__eo_list_concat_rec y z) str hXEval hTailEval hTailIn
                · have hTailIn :
                      RegLanContains M (__eo_list_concat_rec y z) str :=
                    (hIH.2.2 str).2 (Or.inr hZIn)
                  exact reUnion_contains_right M x
                    (__eo_list_concat_rec y z) str hXEval hTailEval hTailIn⟩
      | case4 nil z hNil hZ hNot =>
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.re_union) nil =
                Term.Boolean true := by
            have hGet :=
              eo_get_nil_rec_ne_stuck_of_is_list_true
                (Term.UOp UserOp.re_union) nil hAList
            have hReq :
                __eo_requires
                    (__eo_is_list_nil (Term.UOp UserOp.re_union) nil)
                    (Term.Boolean true) nil ≠ Term.Stuck := by
              simpa [__eo_get_nil_rec] using hGet
            exact eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.re_union) nil)
              (Term.Boolean true) nil hReq
          have hConcatEq : __eo_list_concat_rec nil z = z := by
            have hNilEq :=
              reUnion_nil_eq_none_of_is_list_nil_true hNilTrue
            subst nil
            cases z <;> rfl
          rw [hConcatEq]
          exact ⟨hZList, hZWF, by
            intro str
            constructor
            · intro hZIn
              exact Or.inr hZIn
            · intro hIn
              rcases hIn with hNilIn | hZIn
              · exact False.elim
                  ((reUnion_nil_not_contains M nil str hNilTrue) hNilIn)
              · exact hZIn⟩

private theorem native_str_in_re_re_union_eval_support
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, nativeListInRe, native_re_union,
      native_re_mk_union] using nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem reUnion_list_concat_eval_rel
    (M : SmtModel) (a z : Term) (ra rz : SmtRegLan)
    (hAList :
      __eo_is_list (Term.UOp UserOp.re_union) a = Term.Boolean true)
    (hZList :
      __eo_is_list (Term.UOp UserOp.re_union) z = Term.Boolean true)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hZEval : __smtx_model_eval M (__eo_to_smt z) = SmtValue.RegLan rz) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_union) a z)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_union) a z)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rz)) := by
  have hAWF : ReUnionListWF M a :=
    reUnionListWF_of_type_eval M a ra hATy hAEval
  have hZWF : ReUnionListWF M z :=
    reUnionListWF_of_type_eval M z rz hZTy hZEval
  have hConcat :=
    reUnion_list_concat_rec_wf_contains M a z hAList hZList hAWF hZWF
  rcases reUnionListWF_eval hConcat.2.1 with ⟨r, hRecEval⟩
  have hConcatEq :
      __eo_list_concat (Term.UOp UserOp.re_union) a z =
        __eo_list_concat_rec a z := by
    simp [__eo_list_concat, hAList, hZList, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not]
  have hRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rz)) := by
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]
    intro str _hValid
    have hRecIff :
        native_str_in_re str r = true ↔
          RegLanContains M (__eo_list_concat_rec a z) str := by
      constructor
      · intro hMem
        exact ⟨r, hRecEval, hMem⟩
      · intro hMem
        rcases hMem with ⟨r', hEval', hMem'⟩
        rw [hRecEval] at hEval'
        cases hEval'
        exact hMem'
    have hAIff :
        RegLanContains M a str ↔ native_str_in_re str ra = true := by
      constructor
      · intro hMem
        rcases hMem with ⟨r', hEval', hMem'⟩
        rw [hAEval] at hEval'
        cases hEval'
        exact hMem'
      · intro hMem
        exact ⟨ra, hAEval, hMem⟩
    have hZIff :
        RegLanContains M z str ↔ native_str_in_re str rz = true := by
      constructor
      · intro hMem
        rcases hMem with ⟨r', hEval', hMem'⟩
        rw [hZEval] at hEval'
        cases hEval'
        exact hMem'
      · intro hMem
        exact ⟨rz, hZEval, hMem⟩
    have hIff :
        native_str_in_re str r = true ↔
          native_str_in_re str ra = true ∨
            native_str_in_re str rz = true := by
      rw [hRecIff, hConcat.2.2 str, hAIff, hZIff]
    rw [native_str_in_re_re_union_eval_support]
    cases hr : native_str_in_re str r <;>
      cases ha : native_str_in_re str ra <;>
        cases hz : native_str_in_re str rz <;>
          simp [hr, ha, hz] at hIff ⊢
  refine ⟨r, ?_, ?_, hRel⟩
  · rw [hConcatEq]
    exact hRecEval
  · rw [hConcatEq]
    exact reUnionListWF_type hConcat.2.1

private theorem reUnion_smt_value_rel_right_none_eval
    (M : SmtModel) (x id : Term) (r : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan r ->
    __smtx_model_eval M (__eo_to_smt id) =
      SmtValue.RegLan native_re_none ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkReUnion x id)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hxEval hIdEval
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt id)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_re_union, hxEval, hIdEval]
  change SmtValue.Boolean (native_re_ext_eq (native_re_union r native_re_none) r) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_union_eval_support]
  have hNone : native_str_in_re str native_re_none = false := by
    simpa [native_str_in_re, hValid, native_re_none, nativeListInRe] using
      nativeListInRe_empty str
  cases native_str_in_re str r <;> simp [hNone]

private theorem reUnion_is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.re_union) t =
      Term.Boolean b := by
  intro hNe
  cases t
  case Stuck =>
      exact False.elim (hNe rfl)
  case UOp op =>
      cases op
      case re_none =>
        exact ⟨true, by simp [__eo_is_list_nil]⟩
      all_goals
        exact ⟨false, by simp [__eo_is_list_nil]⟩
  all_goals
      exact ⟨false, by simp [__eo_is_list_nil]⟩

theorem reUnion_singleton_elim_rel_eval
    (M : SmtModel) (c : Term) :
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true ->
    RegLanEval M c ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.re_union) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hCan
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.re_union) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.re_union :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_union) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.re_union) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_union) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases reUnion_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact RuleProofs.smt_value_rel_refl
              (__smtx_model_eval M (__eo_to_smt (mkReUnion head tail)))
          · rcases hCan with ⟨rUnion, hUnionEval⟩
            have hUnionEval' :
                __smtx_model_eval_re_union
                    (__smtx_model_eval M (__eo_to_smt head))
                    (__smtx_model_eval M (__eo_to_smt tail)) =
                  SmtValue.RegLan rUnion := by
              change __smtx_model_eval M
                  (SmtTerm.re_union (__eo_to_smt head) (__eo_to_smt tail)) =
                SmtValue.RegLan rUnion at hUnionEval
              simpa [__smtx_model_eval] using hUnionEval
            cases hHeadEval : __smtx_model_eval M (__eo_to_smt head) with
            | RegLan rHead =>
                exact RuleProofs.smt_value_rel_symm _ _
                  (reUnion_smt_value_rel_right_none_eval M
                    head tail rHead hHeadEval
                    (reUnion_nil_eval_none_of_is_list_nil_true M tail hNil))
            | NotValue =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Boolean b =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Numeral n =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Rational q =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Binary i n =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Fun s T U =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Char c =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Seq s =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Map m =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Set m =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | UValue i e =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | DtCons s d i =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
            | Apply f x =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_union, hHeadEval, hTailEval] at hUnionEval'
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

theorem reUnion_singleton_elim_list_of_ne_stuck (c : Term) :
    __eo_list_singleton_elim (Term.UOp UserOp.re_union) c ≠ Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_union) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c) ≠
        Term.Stuck := by
    simpa [__eo_list_singleton_elim] using h
  exact eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.re_union) c)
    (Term.Boolean true) (__eo_list_singleton_elim_2 c) hReq

theorem reUnion_singleton_elim_has_reglan_type (c : Term) :
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.RegLan ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.re_union) c)) =
      SmtType.RegLan := by
  intro hList hTy
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.re_union) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))) =
    SmtType.RegLan
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.re_union :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_union) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.re_union) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_union) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases reUnion_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          have hArgs := reUnion_args_of_reglan_type head tail hTy
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact hTy
          · exact hArgs.1
      | _ =>
          simpa [__eo_list_singleton_elim_2] using hTy
  | _ =>
      simpa [__eo_list_singleton_elim_2] using hTy

private theorem reInter_smt_value_rel_right_all_eval
    (M : SmtModel) (x id : Term) (r : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan r ->
    __smtx_model_eval M (__eo_to_smt id) =
      SmtValue.RegLan native_re_all ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkReInter x id)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hxEval hIdEval
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt id)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_re_inter, hxEval, hIdEval]
  change SmtValue.Boolean (native_re_ext_eq (native_re_inter r native_re_all) r) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_mk_inter_sem]
  simp [native_str_in_re_all_valid_local str hValid]

private theorem reInter_is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.re_inter) t =
      Term.Boolean b := by
  intro hNe
  cases t
  case Stuck =>
      exact False.elim (hNe rfl)
  case UOp op =>
      cases op
      case re_all =>
        exact ⟨true, by simp [__eo_is_list_nil]⟩
      all_goals
        exact ⟨false, by simp [__eo_is_list_nil]⟩
  all_goals
      exact ⟨false, by simp [__eo_is_list_nil]⟩

theorem reInter_singleton_elim_rel_eval
    (M : SmtModel) (c : Term) :
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true ->
    RegLanEval M c ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.re_inter) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hCan
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_inter) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.re_inter) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_inter) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases reInter_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact RuleProofs.smt_value_rel_refl
              (__smtx_model_eval M (__eo_to_smt (mkReInter head tail)))
          · rcases hCan with ⟨rInter, hInterEval⟩
            have hInterEval' :
                __smtx_model_eval_re_inter
                    (__smtx_model_eval M (__eo_to_smt head))
                    (__smtx_model_eval M (__eo_to_smt tail)) =
                  SmtValue.RegLan rInter := by
              change __smtx_model_eval M
                  (SmtTerm.re_inter (__eo_to_smt head) (__eo_to_smt tail)) =
                SmtValue.RegLan rInter at hInterEval
              simpa [__smtx_model_eval] using hInterEval
            cases hHeadEval : __smtx_model_eval M (__eo_to_smt head) with
            | RegLan rHead =>
                exact RuleProofs.smt_value_rel_symm _ _
                  (reInter_smt_value_rel_right_all_eval M
                    head tail rHead hHeadEval
                    (by
                      have hTailEq : tail = Term.UOp UserOp.re_all := by
                        cases tail <;> try cases hNil
                        case UOp op =>
                          cases op <;> try cases hNil
                          rfl
                      subst tail
                      change __smtx_model_eval M SmtTerm.re_all =
                        SmtValue.RegLan native_re_all
                      rw [__smtx_model_eval.eq_106]))
            | NotValue =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Boolean b =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Numeral n =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Rational q =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Binary i n =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Fun s T U =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Char c =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Seq s =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Map m =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Set m =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | UValue i e =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | DtCons s d i =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
            | Apply f x =>
                cases hTailEval : __smtx_model_eval M (__eo_to_smt tail) <;>
                  simp [__smtx_model_eval_re_inter, hHeadEval, hTailEval] at hInterEval'
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

theorem reInter_singleton_elim_list_of_ne_stuck (c : Term) :
    __eo_list_singleton_elim (Term.UOp UserOp.re_inter) c ≠ Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c) ≠
        Term.Stuck := by
    simpa [__eo_list_singleton_elim] using h
  exact eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.re_inter) c)
    (Term.Boolean true) (__eo_list_singleton_elim_2 c) hReq

theorem reInter_singleton_elim_has_reglan_type (c : Term) :
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.RegLan ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.re_inter) c)) =
      SmtType.RegLan := by
  intro hList hTy
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))) =
    SmtType.RegLan
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_inter) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.re_inter) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_inter) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases reInter_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          have hArgs := reInter_args_of_reglan_type head tail hTy
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact hTy
          · exact hArgs.1
      | _ =>
          simpa [__eo_list_singleton_elim_2] using hTy
  | _ =>
      simpa [__eo_list_singleton_elim_2] using hTy

private theorem reUnion_list_erase_rec_cons_eq
    (x xs e : Term) :
    x = e ->
    x ≠ Term.Stuck ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec (mkReUnion x xs) e = xs := by
  intro hEq hX hE
  have hEqTerm : __eo_eq x e = Term.Boolean true :=
    eo_eq_eq_true_of_eq_local hEq hX hE
  simp [mkReUnion, __eo_list_erase_rec, hEqTerm, __eo_ite, native_ite,
    native_teq]

private theorem reUnion_list_erase_rec_cons_ne
    (x xs e : Term) :
    x ≠ e ->
    x ≠ Term.Stuck ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec xs e ≠ Term.Stuck ->
    __eo_list_erase_rec (mkReUnion x xs) e =
      mkReUnion x (__eo_list_erase_rec xs e) := by
  intro hNe hX hE hTail
  have hEqTerm : __eo_eq x e = Term.Boolean false :=
    eo_eq_eq_false_of_ne_local hNe hX hE
  cases hRec : __eo_list_erase_rec xs e <;>
    simp [mkReUnion, __eo_list_erase_rec, hEqTerm, __eo_ite,
      __eo_mk_apply, native_ite, native_teq, hRec] at hTail ⊢

private theorem reUnion_erase_rec_preserves_wf_list
    (M : SmtModel) :
    (c e : Term) ->
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true ->
    ReUnionListWF M c ->
    ReUnionListWF M e ->
    __eo_is_list (Term.UOp UserOp.re_union) (__eo_list_erase_rec c e) =
        Term.Boolean true ∧
      ReUnionListWF M (__eo_list_erase_rec c e)
  | c, e, hCList, hCWF, hEWF => by
      induction c, e using __eo_list_erase_rec.induct with
      | case1 e =>
          simp [__eo_is_list] at hCList
      | case2 c hEStuck =>
          exact False.elim ((regLanEval_ne_stuck (reUnionListWF_eval hEWF)) rfl)
      | case3 f x y e hENotStuck ih =>
          have hf : f = Term.UOp UserOp.re_union :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_union) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_union) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_union) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hXTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
            hCWF.2.1
          have hYWF : ReUnionListWF M y := hCWF.2.2
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hENe : e ≠ Term.Stuck :=
            regLanEval_ne_stuck (reUnionListWF_eval hEWF)
          by_cases hEq : x = e
          · rw [reUnion_list_erase_rec_cons_eq x y e hEq hXNe hENe]
            exact ⟨hYList, hYWF⟩
          · have hTail := ih hYList hYWF hEWF
            have hTailNe : __eo_list_erase_rec y e ≠ Term.Stuck :=
              reUnion_is_list_true_ne_stuck hTail.1
            rw [reUnion_list_erase_rec_cons_ne x y e hEq hXNe hENe
              hTailNe]
            exact ⟨
              eo_is_list_cons_self_true_of_tail_list
                (Term.UOp UserOp.re_union) x (__eo_list_erase_rec y e)
                (by decide) hTail.1,
              ⟨hXEval, hXTy, hTail.2⟩⟩
      | case4 nil e hNil hE hNot =>
          simpa [__eo_list_erase_rec] using And.intro hCList hCWF

private theorem reUnion_erase_rec_contains_implies_original_contains
    (M : SmtModel) :
    (c e : Term) -> (str : native_String) ->
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true ->
    ReUnionListWF M c ->
    ReUnionListWF M e ->
    RegLanContains M (__eo_list_erase_rec c e) str ->
    RegLanContains M c str
  | c, e, str, hCList, hCWF, hEWF, hEraseIn => by
      induction c, e using __eo_list_erase_rec.induct with
      | case1 e =>
          simp [__eo_is_list] at hCList
      | case2 c hEStuck =>
          exact False.elim ((regLanEval_ne_stuck (reUnionListWF_eval hEWF)) rfl)
      | case3 f x y e hENotStuck ih =>
          have hf : f = Term.UOp UserOp.re_union :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_union) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_union) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_union) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hYWF : ReUnionListWF M y := hCWF.2.2
          have hYEval : RegLanEval M y := reUnionListWF_eval hYWF
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hENe : e ≠ Term.Stuck :=
            regLanEval_ne_stuck (reUnionListWF_eval hEWF)
          by_cases hEq : x = e
          · have hEraseEq :
                __eo_list_erase_rec (mkReUnion x y) e = y :=
              reUnion_list_erase_rec_cons_eq x y e hEq hXNe hENe
            rw [hEraseEq] at hEraseIn
            exact reUnion_contains_right M x y str hXEval hYEval hEraseIn
          · have hTail := reUnion_erase_rec_preserves_wf_list M y e
              hYList hYWF hEWF
            have hTailEval :
                RegLanEval M (__eo_list_erase_rec y e) :=
              reUnionListWF_eval hTail.2
            have hTailNe :
                __eo_list_erase_rec y e ≠ Term.Stuck :=
              reUnion_is_list_true_ne_stuck hTail.1
            have hEraseEq :
                __eo_list_erase_rec (mkReUnion x y) e =
                  mkReUnion x (__eo_list_erase_rec y e) :=
              reUnion_list_erase_rec_cons_ne x y e hEq hXNe hENe hTailNe
            rw [hEraseEq] at hEraseIn
            rcases reUnion_contains_cases M x (__eo_list_erase_rec y e) str
                hXEval hTailEval hEraseIn with hXIn | hTailIn
            · exact reUnion_contains_left M x y str hXEval hYEval hXIn
            · have hYIn : RegLanContains M y str :=
                ih hYList hYWF hEWF hTailIn
              exact reUnion_contains_right M x y str hXEval hYEval hYIn
      | case4 nil e hNil hE hNot =>
          simpa [__eo_list_erase_rec] using hEraseIn

private theorem reUnion_erase_rec_changed_and_lit_contains_implies_original_contains
    (M : SmtModel) :
    (c e : Term) -> (str : native_String) ->
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true ->
    ReUnionListWF M c ->
    ReUnionListWF M e ->
    RegLanContains M e str ->
    __eo_list_erase_rec c e ≠ c ->
    RegLanContains M c str
  | c, e, str, hCList, hCWF, hEWF, hEIn, hChanged => by
      induction c, e using __eo_list_erase_rec.induct with
      | case1 e =>
          simp [__eo_is_list] at hCList
      | case2 c hEStuck =>
          exact False.elim ((regLanEval_ne_stuck (reUnionListWF_eval hEWF)) rfl)
      | case3 f x y e hENotStuck ih =>
          have hf : f = Term.UOp UserOp.re_union :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_union) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_union) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_union) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hYWF : ReUnionListWF M y := hCWF.2.2
          have hYEval : RegLanEval M y := reUnionListWF_eval hYWF
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hENe : e ≠ Term.Stuck :=
            regLanEval_ne_stuck (reUnionListWF_eval hEWF)
          by_cases hEq : x = e
          · have hXIn : RegLanContains M x str := by
              simpa [hEq] using hEIn
            exact reUnion_contains_left M x y str hXEval hYEval hXIn
          · have hTail := reUnion_erase_rec_preserves_wf_list M y e
              hYList hYWF hEWF
            have hTailNe :
                __eo_list_erase_rec y e ≠ Term.Stuck :=
              reUnion_is_list_true_ne_stuck hTail.1
            have hTailChanged : __eo_list_erase_rec y e ≠ y := by
              intro hTailEq
              apply hChanged
              rw [reUnion_list_erase_rec_cons_ne x y e hEq hXNe hENe
                hTailNe, hTailEq]
            have hYIn : RegLanContains M y str :=
              ih hYList hYWF hEWF hEIn hTailChanged
            exact reUnion_contains_right M x y str hXEval hYEval hYIn
      | case4 nil e hNil hE hNot =>
          exfalso
          apply hChanged
          simp [__eo_list_erase_rec]

private theorem reUnion_list_find_rec_nonneg_contains
    (M : SmtModel) :
    (c e n : Term) -> (str : native_String) ->
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true ->
    ReUnionListWF M c ->
    ReUnionListWF M e ->
    __eo_is_neg (__eo_list_find_rec c e n) = Term.Boolean false ->
    RegLanContains M e str ->
    RegLanContains M c str
  | c, e, n, str, hCList, hCWF, hEWF, hFind, hEIn => by
      induction c, e, n using __eo_list_find_rec.induct with
      | case1 e n =>
          simp [__eo_is_list] at hCList
      | case2 c n hCNe =>
          exact False.elim ((regLanEval_ne_stuck (reUnionListWF_eval hEWF)) rfl)
      | case3 c e hENe hCNe =>
          simp [__eo_list_find_rec, __eo_is_neg] at hFind
      | case4 f x y z n hZNe hNNe ih =>
          have hf : f = Term.UOp UserOp.re_union :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_union) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_union) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_union) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hYWF : ReUnionListWF M y := hCWF.2.2
          have hYEval : RegLanEval M y := reUnionListWF_eval hYWF
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hZWF : ReUnionListWF M z := hEWF
          have hZNe : z ≠ Term.Stuck :=
            regLanEval_ne_stuck (reUnionListWF_eval hZWF)
          by_cases hEq : x = z
          · have hXIn : RegLanContains M x str := by
              simpa [hEq] using hEIn
            exact reUnion_contains_left M x y str hXEval hYEval hXIn
          · have hEqTerm : __eo_eq x z = Term.Boolean false :=
              eo_eq_eq_false_of_ne_local hEq hXNe hZNe
            have hTailFind :
                __eo_is_neg
                    (__eo_list_find_rec y z
                      (__eo_add n (Term.Numeral 1))) =
                  Term.Boolean false := by
              simpa [__eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
                native_teq] using hFind
            have hYIn : RegLanContains M y str :=
              ih hYList hYWF hZWF hTailFind hEIn
            exact reUnion_contains_right M x y str hXEval hYEval hYIn
      | case5 nil z n hNilNe hZNe hNNe hNot =>
          have hNeg : native_zlt (-1 : native_Int) 0 = true := by
            native_decide
          simp [__eo_list_find_rec, __eo_is_neg, hNeg] at hFind

private theorem reUnion_list_find_nonneg_contains
    (M : SmtModel) (c e : Term) (str : native_String) :
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true ->
    ReUnionListWF M c ->
    ReUnionListWF M e ->
    __eo_is_neg (__eo_list_find (Term.UOp UserOp.re_union) c e) =
      Term.Boolean false ->
    RegLanContains M e str ->
    RegLanContains M c str := by
  intro hCList hCWF hEWF hFind hEIn
  have hFindRec :
      __eo_is_neg (__eo_list_find_rec c e (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hCList, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not] using hFind
  exact reUnion_list_find_rec_nonneg_contains M c e (Term.Numeral 0) str
    hCList hCWF hEWF hFindRec hEIn

private theorem reUnion_list_diff_rec_wf_contains
    (M : SmtModel) :
    (c d : Term) ->
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.re_union) d = Term.Boolean true ->
    ReUnionListWF M c ->
    ReUnionListWF M d ->
    __eo_is_list (Term.UOp UserOp.re_union) (__eo_list_diff_rec c d) =
        Term.Boolean true ∧
      ReUnionListWF M (__eo_list_diff_rec c d) ∧
      ∀ str,
        (RegLanContains M (__eo_list_diff_rec c d) str ∨
            RegLanContains M d str) ↔
          (RegLanContains M c str ∨ RegLanContains M d str)
  | c, d, hCList, hDList, hCWF, hDWF => by
      induction c, d using __eo_list_diff_rec.induct with
      | case1 d =>
          simp [__eo_is_list] at hCList
      | case2 c hDStuck =>
          exact False.elim ((regLanEval_ne_stuck (reUnionListWF_eval hDWF)) rfl)
      | case3 f x y d hDNotStuck v0 ih =>
          have hf : f = Term.UOp UserOp.re_union :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_union) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_union) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_union) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hXTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
            hCWF.2.1
          have hXWF : ReUnionListWF M x := by
            rcases hXEval with ⟨rx, hxEval⟩
            exact reUnionListWF_of_type_eval M x rx hXTy hxEval
          have hYWF : ReUnionListWF M y := hCWF.2.2
          have hYEval : RegLanEval M y := reUnionListWF_eval hYWF
          have hDNe : d ≠ Term.Stuck :=
            regLanEval_ne_stuck (reUnionListWF_eval hDWF)
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hErase :=
            reUnion_erase_rec_preserves_wf_list M d x hDList hDWF hXWF
          have hEraseNe : __eo_list_erase_rec d x ≠ Term.Stuck :=
            reUnion_is_list_true_ne_stuck hErase.1
          have hIH := ih hYList hErase.1 hYWF hErase.2
          by_cases hSame : __eo_list_erase_rec d x = d
          · have hEqTerm :
                __eo_eq (__eo_list_erase_rec d x) d =
                  Term.Boolean true :=
              eo_eq_eq_true_of_eq_local hSame hEraseNe hDNe
            have hEqSelf : __eo_eq d d = Term.Boolean true :=
              eo_eq_eq_true_of_eq_local rfl hDNe hDNe
            have hv0 : v0 = d := by
              simpa [v0] using hSame
            have hIHD :
                __eo_is_list (Term.UOp UserOp.re_union)
                    (__eo_list_diff_rec y d) =
                    Term.Boolean true ∧
                  ReUnionListWF M (__eo_list_diff_rec y d) ∧
                  ∀ str,
                    (RegLanContains M (__eo_list_diff_rec y d) str ∨
                        RegLanContains M d str) ↔
                      (RegLanContains M y str ∨ RegLanContains M d str) := by
              simpa [hv0] using hIH
            have hRecNe : __eo_list_diff_rec y d ≠ Term.Stuck :=
              reUnion_is_list_true_ne_stuck hIHD.1
            have hDiffEq :
                __eo_list_diff_rec (mkReUnion x y) d =
                  mkReUnion x (__eo_list_diff_rec y d) := by
              simp [mkReUnion, __eo_list_diff_rec, hEqSelf, __eo_prepend_if, hSame]
            rw [hDiffEq]
            have hDiffEval :
                RegLanEval M (__eo_list_diff_rec y d) :=
              reUnionListWF_eval hIHD.2.1
            exact ⟨
              eo_is_list_cons_self_true_of_tail_list
                (Term.UOp UserOp.re_union) x (__eo_list_diff_rec y d)
                (by decide) hIHD.1,
              ⟨hXEval, hXTy, hIHD.2.1⟩,
              by
                intro str
                constructor
                · intro hIn
                  rcases hIn with hResIn | hDIn
                  · rcases reUnion_contains_cases M x
                        (__eo_list_diff_rec y d) str hXEval hDiffEval
                        hResIn with hXIn | hDiffIn
                    · exact Or.inl
                        (reUnion_contains_left M x y str hXEval hYEval
                          hXIn)
                    · rcases (hIHD.2.2 str).1 (Or.inl hDiffIn) with
                        hYIn | hDIn
                      · exact Or.inl
                          (reUnion_contains_right M x y str hXEval hYEval
                            hYIn)
                      · exact Or.inr hDIn
                  · exact Or.inr hDIn
                · intro hIn
                  rcases hIn with hCIn | hDIn
                  · rcases reUnion_contains_cases M x y str hXEval hYEval
                        hCIn with hXIn | hYIn
                    · exact Or.inl
                        (reUnion_contains_left M x
                          (__eo_list_diff_rec y d) str hXEval hDiffEval
                          hXIn)
                    · rcases (hIHD.2.2 str).2 (Or.inl hYIn) with
                        hDiffIn | hDIn
                      · exact Or.inl
                          (reUnion_contains_right M x
                            (__eo_list_diff_rec y d) str hXEval hDiffEval
                            hDiffIn)
                      · exact Or.inr hDIn
                  · exact Or.inr hDIn⟩
          · have hEqTerm :
                __eo_eq (__eo_list_erase_rec d x) d =
                  Term.Boolean false :=
              eo_eq_eq_false_of_ne_local hSame hEraseNe hDNe
            have hRecNe :
                __eo_list_diff_rec y (__eo_list_erase_rec d x) ≠
                  Term.Stuck := by
              change __eo_list_diff_rec y v0 ≠ Term.Stuck
              exact reUnion_is_list_true_ne_stuck hIH.1
            have hDiffEq :
                __eo_list_diff_rec (mkReUnion x y) d =
                  __eo_list_diff_rec y (__eo_list_erase_rec d x) := by
              simp [mkReUnion, __eo_list_diff_rec, hEqTerm,
                __eo_prepend_if]
            rw [hDiffEq]
            exact ⟨hIH.1, hIH.2.1, by
              intro str
              constructor
              · intro hIn
                rcases hIn with hDiffIn | hDIn
                · rcases (hIH.2.2 str).1 (Or.inl hDiffIn) with
                    hYIn | hEraseIn
                  · exact Or.inl
                      (reUnion_contains_right M x y str hXEval hYEval
                        hYIn)
                  · exact Or.inr
                      (reUnion_erase_rec_contains_implies_original_contains
                        M d x str hDList hDWF hXWF hEraseIn)
                · exact Or.inr hDIn
              · intro hIn
                rcases hIn with hCIn | hDIn
                · rcases reUnion_contains_cases M x y str hXEval hYEval
                    hCIn with hXIn | hYIn
                  · exact Or.inr
                      (reUnion_erase_rec_changed_and_lit_contains_implies_original_contains
                        M d x str hDList hDWF hXWF hXIn hSame)
                  · rcases (hIH.2.2 str).2 (Or.inl hYIn) with
                      hDiffIn | hEraseIn
                    · exact Or.inl hDiffIn
                    · exact Or.inr
                        (reUnion_erase_rec_contains_implies_original_contains
                          M d x str hDList hDWF hXWF hEraseIn)
                · exact Or.inr hDIn⟩
      | case4 nil d hNil hD hNot =>
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.re_union) nil =
                Term.Boolean true := by
            have hGet :=
              eo_get_nil_rec_ne_stuck_of_is_list_true
                (Term.UOp UserOp.re_union) nil hCList
            have hReq :
                __eo_requires
                    (__eo_is_list_nil (Term.UOp UserOp.re_union) nil)
                    (Term.Boolean true) nil ≠ Term.Stuck := by
              simpa [__eo_get_nil_rec] using hGet
            exact eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.re_union) nil)
              (Term.Boolean true) nil hReq
          have hDiffEq : __eo_list_diff_rec nil d = nil := by
            have hNilEq :=
              reUnion_nil_eq_none_of_is_list_nil_true hNilTrue
            subst nil
            cases d
            case Stuck =>
              exact False.elim (hD rfl)
            all_goals rfl
          rw [hDiffEq]
          exact ⟨hCList, hCWF, by
            intro str
            constructor
            · intro hIn
              rcases hIn with hNilIn | hDIn
              · exact False.elim
                  ((reUnion_nil_not_contains M nil str hNilTrue) hNilIn)
              · exact Or.inr hDIn
            · intro hIn
              rcases hIn with hNilIn | hDIn
              · exact False.elim
                  ((reUnion_nil_not_contains M nil str hNilTrue) hNilIn)
              · exact Or.inr hDIn⟩

private theorem reInter_is_list_true_ne_stuck {t : Term} :
    __eo_is_list (Term.UOp UserOp.re_inter) t = Term.Boolean true ->
    t ≠ Term.Stuck := by
  intro hList hStuck
  subst t
  simp [__eo_is_list] at hList

private theorem reInter_nil_eq_all_of_is_list_nil_true {nil : Term} :
    __eo_is_list_nil (Term.UOp UserOp.re_inter) nil = Term.Boolean true ->
    nil = Term.UOp UserOp.re_all := by
  intro hNil
  cases nil <;> try cases hNil
  case UOp op =>
    cases op <;> try cases hNil
    rfl

private theorem reInter_nil_eval_all_of_is_list_nil_true
    (M : SmtModel) (nil : Term) :
    __eo_is_list_nil (Term.UOp UserOp.re_inter) nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.RegLan native_re_all := by
  intro hNilTrue
  have hNilEq := reInter_nil_eq_all_of_is_list_nil_true hNilTrue
  subst nil
  change __smtx_model_eval M SmtTerm.re_all =
    SmtValue.RegLan native_re_all
  simp [__smtx_model_eval]

private theorem reInter_nil_contains
    (M : SmtModel) (nil : Term) (str : native_String) :
    __eo_is_list_nil (Term.UOp UserOp.re_inter) nil = Term.Boolean true ->
    native_string_valid str = true ->
    RegLanContains M nil str := by
  intro hNil hValid
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.RegLan native_re_all :=
    reInter_nil_eval_all_of_is_list_nil_true M nil hNil
  exact ⟨native_re_all, hNilEval, native_str_in_re_all_valid_local str hValid⟩

private theorem reInter_list_concat_rec_wf_contains
    (M : SmtModel) :
    (a z : Term) ->
    __eo_is_list (Term.UOp UserOp.re_inter) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.re_inter) z = Term.Boolean true ->
    ReInterListWF M a ->
    ReInterListWF M z ->
    __eo_is_list (Term.UOp UserOp.re_inter) (__eo_list_concat_rec a z) =
        Term.Boolean true ∧
      ReInterListWF M (__eo_list_concat_rec a z) ∧
      ∀ str,
        RegLanContains M (__eo_list_concat_rec a z) str ↔
          RegLanContains M a str ∧ RegLanContains M z str
  | a, z, hAList, hZList, hAWF, hZWF => by
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          cases (Term.UOp UserOp.re_inter) <;> simp [__eo_is_list] at hAList
      | case2 a hA =>
          cases (Term.UOp UserOp.re_inter) <;> simp [__eo_is_list] at hZList
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_inter) g x y hAList
          subst g
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_inter) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_inter) x y hAList
          have hTailNe :
              __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list
              (Term.UOp UserOp.re_inter) y z hYList hZ
          have hXEval : RegLanEval M x := hAWF.1
          have hXTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
            hAWF.2.1
          have hYWF : ReInterListWF M y := hAWF.2.2
          have hYEval : RegLanEval M y := reInterListWF_eval hYWF
          have hIH := ih hYList hZList hYWF hZWF
          rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
            (Term.UOp UserOp.re_inter) x y z hTailNe]
          have hTailWF :
              ReInterListWF M (__eo_list_concat_rec y z) := hIH.2.1
          have hTailEval :
              RegLanEval M (__eo_list_concat_rec y z) :=
            reInterListWF_eval hTailWF
          exact ⟨
            eo_is_list_cons_self_true_of_tail_list
              (Term.UOp UserOp.re_inter) x (__eo_list_concat_rec y z)
              (by decide) hIH.1,
            ⟨hXEval, hXTy, hTailWF⟩,
            by
              intro str
              constructor
              · intro hIn
                rcases reInter_contains_cases M x
                    (__eo_list_concat_rec y z) str hXEval hTailEval hIn with
                  ⟨hXIn, hTailIn⟩
                rcases (hIH.2.2 str).1 hTailIn with ⟨hYIn, hZIn⟩
                exact ⟨
                  reInter_contains M x y str hXEval hYEval hXIn hYIn,
                  hZIn⟩
              · intro hIn
                rcases hIn with ⟨hAIn, hZIn⟩
                rcases reInter_contains_cases M x y str hXEval hYEval hAIn with
                  ⟨hXIn, hYIn⟩
                have hTailIn :
                    RegLanContains M (__eo_list_concat_rec y z) str :=
                  (hIH.2.2 str).2 ⟨hYIn, hZIn⟩
                exact reInter_contains M x
                  (__eo_list_concat_rec y z) str hXEval hTailEval
                  hXIn hTailIn⟩
      | case4 nil z hNil hZ hNot =>
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.re_inter) nil =
                Term.Boolean true := by
            have hGet :=
              eo_get_nil_rec_ne_stuck_of_is_list_true
                (Term.UOp UserOp.re_inter) nil hAList
            have hReq :
                __eo_requires
                    (__eo_is_list_nil (Term.UOp UserOp.re_inter) nil)
                    (Term.Boolean true) nil ≠ Term.Stuck := by
              simpa [__eo_get_nil_rec] using hGet
            exact eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.re_inter) nil)
              (Term.Boolean true) nil hReq
          have hConcatEq : __eo_list_concat_rec nil z = z := by
            have hNilEq :=
              reInter_nil_eq_all_of_is_list_nil_true hNilTrue
            subst nil
            cases z <;> rfl
          rw [hConcatEq]
          exact ⟨hZList, hZWF, by
            intro str
            constructor
            · intro hZIn
              exact ⟨
                reInter_nil_contains M nil str hNilTrue
                  (native_string_valid_of_reglan_contains hZIn),
                hZIn⟩
            · intro hIn
              exact hIn.2⟩

theorem reInter_list_concat_eval_rel
    (M : SmtModel) (a z : Term) (ra rz : SmtRegLan)
    (hAList :
      __eo_is_list (Term.UOp UserOp.re_inter) a = Term.Boolean true)
    (hZList :
      __eo_is_list (Term.UOp UserOp.re_inter) z = Term.Boolean true)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hZEval : __smtx_model_eval M (__eo_to_smt z) = SmtValue.RegLan rz) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_inter) a z)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_inter) a z)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rz)) := by
  have hAWF : ReInterListWF M a :=
    reInterListWF_of_type_eval M a ra hATy hAEval
  have hZWF : ReInterListWF M z :=
    reInterListWF_of_type_eval M z rz hZTy hZEval
  have hConcat :=
    reInter_list_concat_rec_wf_contains M a z
      hAList hZList hAWF hZWF
  have hConcatEq :
      __eo_list_concat (Term.UOp UserOp.re_inter) a z =
        __eo_list_concat_rec a z := by
    simp [__eo_list_concat, hAList, hZList, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not]
  rcases reInterListWF_eval hConcat.2.1 with ⟨r, hRecEval⟩
  have hRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rz)) :=
    smt_value_rel_reglan_native_inter_of_contains_iff
      M (__eo_list_concat_rec a z) a z r ra rz
        hRecEval hAEval hZEval hConcat.2.2
  refine ⟨r, ?_, ?_, hRel⟩
  · rw [hConcatEq]
    exact hRecEval
  · rw [hConcatEq]
    exact reInterListWF_type hConcat.2.1

private theorem reInter_list_erase_rec_cons_eq
    (x xs e : Term) :
    x = e ->
    x ≠ Term.Stuck ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec (mkReInter x xs) e = xs := by
  intro hEq hX hE
  have hEqTerm : __eo_eq x e = Term.Boolean true :=
    eo_eq_eq_true_of_eq_local hEq hX hE
  simp [mkReInter, __eo_list_erase_rec, hEqTerm, __eo_ite, native_ite,
    native_teq]

private theorem reInter_list_erase_rec_cons_ne
    (x xs e : Term) :
    x ≠ e ->
    x ≠ Term.Stuck ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec xs e ≠ Term.Stuck ->
    __eo_list_erase_rec (mkReInter x xs) e =
      mkReInter x (__eo_list_erase_rec xs e) := by
  intro hNe hX hE hTail
  have hEqTerm : __eo_eq x e = Term.Boolean false :=
    eo_eq_eq_false_of_ne_local hNe hX hE
  cases hRec : __eo_list_erase_rec xs e <;>
    simp [mkReInter, __eo_list_erase_rec, hEqTerm, __eo_ite,
      __eo_mk_apply, native_ite, native_teq, hRec] at hTail ⊢

private theorem reInter_erase_rec_preserves_wf_list
    (M : SmtModel) :
    (c e : Term) ->
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true ->
    ReInterListWF M c ->
    ReInterListWF M e ->
    __eo_is_list (Term.UOp UserOp.re_inter) (__eo_list_erase_rec c e) =
        Term.Boolean true ∧
      ReInterListWF M (__eo_list_erase_rec c e)
  | c, e, hCList, hCWF, hEWF => by
      induction c, e using __eo_list_erase_rec.induct with
      | case1 e =>
          simp [__eo_is_list] at hCList
      | case2 c hEStuck =>
          exact False.elim ((regLanEval_ne_stuck (reInterListWF_eval hEWF)) rfl)
      | case3 f x y e hENotStuck ih =>
          have hf : f = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_inter) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_inter) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_inter) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hXTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
            hCWF.2.1
          have hYWF : ReInterListWF M y := hCWF.2.2
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hENe : e ≠ Term.Stuck :=
            regLanEval_ne_stuck (reInterListWF_eval hEWF)
          by_cases hEq : x = e
          · rw [reInter_list_erase_rec_cons_eq x y e hEq hXNe hENe]
            exact ⟨hYList, hYWF⟩
          · have hTail := ih hYList hYWF hEWF
            have hTailNe : __eo_list_erase_rec y e ≠ Term.Stuck :=
              reInter_is_list_true_ne_stuck hTail.1
            rw [reInter_list_erase_rec_cons_ne x y e hEq hXNe hENe
              hTailNe]
            exact ⟨
              eo_is_list_cons_self_true_of_tail_list
                (Term.UOp UserOp.re_inter) x (__eo_list_erase_rec y e)
                (by decide) hTail.1,
              ⟨hXEval, hXTy, hTail.2⟩⟩
      | case4 nil e hNil hE hNot =>
          simpa [__eo_list_erase_rec] using And.intro hCList hCWF

private theorem reInter_erase_rec_original_contains_implies_erase_contains
    (M : SmtModel) :
    (c e : Term) -> (str : native_String) ->
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true ->
    ReInterListWF M c ->
    ReInterListWF M e ->
    RegLanContains M c str ->
    RegLanContains M (__eo_list_erase_rec c e) str
  | c, e, str, hCList, hCWF, hEWF, hCIn => by
      induction c, e using __eo_list_erase_rec.induct with
      | case1 e =>
          simp [__eo_is_list] at hCList
      | case2 c hEStuck =>
          exact False.elim ((regLanEval_ne_stuck (reInterListWF_eval hEWF)) rfl)
      | case3 f x y e hENotStuck ih =>
          have hf : f = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_inter) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_inter) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_inter) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hYWF : ReInterListWF M y := hCWF.2.2
          have hYEval : RegLanEval M y := reInterListWF_eval hYWF
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hENe : e ≠ Term.Stuck :=
            regLanEval_ne_stuck (reInterListWF_eval hEWF)
          rcases reInter_contains_cases M x y str hXEval hYEval hCIn with
            ⟨hXIn, hYIn⟩
          by_cases hEq : x = e
          · have hEraseEq :
                __eo_list_erase_rec (mkReInter x y) e = y :=
              reInter_list_erase_rec_cons_eq x y e hEq hXNe hENe
            rw [hEraseEq]
            exact hYIn
          · have hTail := reInter_erase_rec_preserves_wf_list M y e
              hYList hYWF hEWF
            have hTailEval :
                RegLanEval M (__eo_list_erase_rec y e) :=
              reInterListWF_eval hTail.2
            have hTailNe :
                __eo_list_erase_rec y e ≠ Term.Stuck :=
              reInter_is_list_true_ne_stuck hTail.1
            have hEraseEq :
                __eo_list_erase_rec (mkReInter x y) e =
                  mkReInter x (__eo_list_erase_rec y e) :=
              reInter_list_erase_rec_cons_ne x y e hEq hXNe hENe hTailNe
            rw [hEraseEq]
            have hTailIn : RegLanContains M (__eo_list_erase_rec y e) str :=
              ih hYList hYWF hEWF hYIn
            exact reInter_contains M x (__eo_list_erase_rec y e) str
              hXEval hTailEval hXIn hTailIn
      | case4 nil e hNil hE hNot =>
          simpa [__eo_list_erase_rec] using hCIn

private theorem reInter_erase_rec_changed_and_original_contains_implies_lit_contains
    (M : SmtModel) :
    (c e : Term) -> (str : native_String) ->
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true ->
    ReInterListWF M c ->
    ReInterListWF M e ->
    RegLanContains M c str ->
    __eo_list_erase_rec c e ≠ c ->
    RegLanContains M e str
  | c, e, str, hCList, hCWF, hEWF, hCIn, hChanged => by
      induction c, e using __eo_list_erase_rec.induct with
      | case1 e =>
          simp [__eo_is_list] at hCList
      | case2 c hEStuck =>
          exact False.elim ((regLanEval_ne_stuck (reInterListWF_eval hEWF)) rfl)
      | case3 f x y e hENotStuck ih =>
          have hf : f = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_inter) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_inter) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_inter) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hYWF : ReInterListWF M y := hCWF.2.2
          have hYEval : RegLanEval M y := reInterListWF_eval hYWF
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hENe : e ≠ Term.Stuck :=
            regLanEval_ne_stuck (reInterListWF_eval hEWF)
          rcases reInter_contains_cases M x y str hXEval hYEval hCIn with
            ⟨hXIn, hYIn⟩
          by_cases hEq : x = e
          · simpa [hEq] using hXIn
          · have hTail := reInter_erase_rec_preserves_wf_list M y e
              hYList hYWF hEWF
            have hTailNe :
                __eo_list_erase_rec y e ≠ Term.Stuck :=
              reInter_is_list_true_ne_stuck hTail.1
            have hTailChanged : __eo_list_erase_rec y e ≠ y := by
              intro hTailEq
              apply hChanged
              rw [reInter_list_erase_rec_cons_ne x y e hEq hXNe hENe
                hTailNe, hTailEq]
            exact ih hYList hYWF hEWF hYIn hTailChanged
      | case4 nil e hNil hE hNot =>
          exfalso
          apply hChanged
          simp [__eo_list_erase_rec]

private theorem reInter_list_find_rec_nonneg_contains
    (M : SmtModel) :
    (c e n : Term) -> (str : native_String) ->
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true ->
    ReInterListWF M c ->
    ReInterListWF M e ->
    __eo_is_neg (__eo_list_find_rec c e n) = Term.Boolean false ->
    RegLanContains M c str ->
    RegLanContains M e str
  | c, e, n, str, hCList, hCWF, hEWF, hFind, hCIn => by
      induction c, e, n using __eo_list_find_rec.induct with
      | case1 e n =>
          simp [__eo_is_list] at hCList
      | case2 c n hCNe =>
          exact False.elim ((regLanEval_ne_stuck (reInterListWF_eval hEWF)) rfl)
      | case3 c e hENe hCNe =>
          simp [__eo_list_find_rec, __eo_is_neg] at hFind
      | case4 f x y z n hZNe hNNe ih =>
          have hf : f = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_inter) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_inter) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_inter) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hYWF : ReInterListWF M y := hCWF.2.2
          have hYEval : RegLanEval M y := reInterListWF_eval hYWF
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hZWF : ReInterListWF M z := hEWF
          have hZNe : z ≠ Term.Stuck :=
            regLanEval_ne_stuck (reInterListWF_eval hZWF)
          rcases reInter_contains_cases M x y str hXEval hYEval hCIn with
            ⟨hXIn, hYIn⟩
          by_cases hEq : x = z
          · simpa [hEq] using hXIn
          · have hEqTerm : __eo_eq x z = Term.Boolean false :=
              eo_eq_eq_false_of_ne_local hEq hXNe hZNe
            have hTailFind :
                __eo_is_neg
                    (__eo_list_find_rec y z
                      (__eo_add n (Term.Numeral 1))) =
                  Term.Boolean false := by
              simpa [__eo_list_find_rec, hEqTerm, __eo_ite, native_ite,
                native_teq] using hFind
            exact ih hYList hYWF hZWF hTailFind hYIn
      | case5 nil z n hNilNe hZNe hNNe hNot =>
          have hNeg : native_zlt (-1 : native_Int) 0 = true := by
            native_decide
          simp [__eo_list_find_rec, __eo_is_neg, hNeg] at hFind

private theorem reInter_list_find_nonneg_contains
    (M : SmtModel) (c e : Term) (str : native_String) :
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true ->
    ReInterListWF M c ->
    ReInterListWF M e ->
    __eo_is_neg (__eo_list_find (Term.UOp UserOp.re_inter) c e) =
      Term.Boolean false ->
    RegLanContains M c str ->
    RegLanContains M e str := by
  intro hCList hCWF hEWF hFind hCIn
  have hFindRec :
      __eo_is_neg (__eo_list_find_rec c e (Term.Numeral 0)) =
        Term.Boolean false := by
    simpa [__eo_list_find, hCList, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not] using hFind
  exact reInter_list_find_rec_nonneg_contains M c e (Term.Numeral 0) str
    hCList hCWF hEWF hFindRec hCIn

private theorem reInter_list_diff_rec_wf_contains
    (M : SmtModel) :
    (c d : Term) ->
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.re_inter) d = Term.Boolean true ->
    ReInterListWF M c ->
    ReInterListWF M d ->
    __eo_is_list (Term.UOp UserOp.re_inter) (__eo_list_diff_rec c d) =
        Term.Boolean true ∧
      ReInterListWF M (__eo_list_diff_rec c d) ∧
      ∀ str,
        (RegLanContains M (__eo_list_diff_rec c d) str ∧
            RegLanContains M d str) ↔
          (RegLanContains M c str ∧ RegLanContains M d str)
  | c, d, hCList, hDList, hCWF, hDWF => by
      induction c, d using __eo_list_diff_rec.induct with
      | case1 d =>
          simp [__eo_is_list] at hCList
      | case2 c hDStuck =>
          exact False.elim ((regLanEval_ne_stuck (reInterListWF_eval hDWF)) rfl)
      | case3 f x y d hDNotStuck v0 ih =>
          have hf : f = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.re_inter) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.re_inter) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.re_inter) x y hCList
          have hXEval : RegLanEval M x := hCWF.1
          have hXTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
            hCWF.2.1
          have hXWF : ReInterListWF M x := by
            rcases hXEval with ⟨rx, hxEval⟩
            exact reInterListWF_of_type_eval M x rx hXTy hxEval
          have hYWF : ReInterListWF M y := hCWF.2.2
          have hYEval : RegLanEval M y := reInterListWF_eval hYWF
          have hDNe : d ≠ Term.Stuck :=
            regLanEval_ne_stuck (reInterListWF_eval hDWF)
          have hXNe : x ≠ Term.Stuck := regLanEval_ne_stuck hXEval
          have hErase :=
            reInter_erase_rec_preserves_wf_list M d x hDList hDWF hXWF
          have hEraseNe : __eo_list_erase_rec d x ≠ Term.Stuck :=
            reInter_is_list_true_ne_stuck hErase.1
          have hIH := ih hYList hErase.1 hYWF hErase.2
          by_cases hSame : __eo_list_erase_rec d x = d
          · have hEqTerm :
                __eo_eq (__eo_list_erase_rec d x) d =
                  Term.Boolean true :=
              eo_eq_eq_true_of_eq_local hSame hEraseNe hDNe
            have hEqSelf : __eo_eq d d = Term.Boolean true :=
              eo_eq_eq_true_of_eq_local rfl hDNe hDNe
            have hv0 : v0 = d := by
              simpa [v0] using hSame
            have hIHD :
                __eo_is_list (Term.UOp UserOp.re_inter)
                    (__eo_list_diff_rec y d) =
                    Term.Boolean true ∧
                  ReInterListWF M (__eo_list_diff_rec y d) ∧
                  ∀ str,
                    (RegLanContains M (__eo_list_diff_rec y d) str ∧
                        RegLanContains M d str) ↔
                      (RegLanContains M y str ∧ RegLanContains M d str) := by
              simpa [hv0] using hIH
            have hRecNe : __eo_list_diff_rec y d ≠ Term.Stuck :=
              reInter_is_list_true_ne_stuck hIHD.1
            have hDiffEq :
                __eo_list_diff_rec (mkReInter x y) d =
                  mkReInter x (__eo_list_diff_rec y d) := by
              simp [mkReInter, __eo_list_diff_rec, hEqSelf, __eo_prepend_if, hSame]
            rw [hDiffEq]
            have hDiffEval :
                RegLanEval M (__eo_list_diff_rec y d) :=
              reInterListWF_eval hIHD.2.1
            exact ⟨
              eo_is_list_cons_self_true_of_tail_list
                (Term.UOp UserOp.re_inter) x (__eo_list_diff_rec y d)
                (by decide) hIHD.1,
              ⟨hXEval, hXTy, hIHD.2.1⟩,
              by
                intro str
                constructor
                · intro hIn
                  rcases hIn with ⟨hResIn, hDIn⟩
                  rcases reInter_contains_cases M x
                      (__eo_list_diff_rec y d) str hXEval hDiffEval
                      hResIn with ⟨hXIn, hDiffIn⟩
                  rcases (hIHD.2.2 str).1 ⟨hDiffIn, hDIn⟩ with
                    ⟨hYIn, hDIn'⟩
                  exact ⟨
                    reInter_contains M x y str hXEval hYEval hXIn hYIn,
                    hDIn'⟩
                · intro hIn
                  rcases hIn with ⟨hCIn, hDIn⟩
                  rcases reInter_contains_cases M x y str hXEval hYEval
                      hCIn with ⟨hXIn, hYIn⟩
                  rcases (hIHD.2.2 str).2 ⟨hYIn, hDIn⟩ with
                    ⟨hDiffIn, hDIn'⟩
                  exact ⟨
                    reInter_contains M x (__eo_list_diff_rec y d) str
                      hXEval hDiffEval hXIn hDiffIn,
                    hDIn'⟩⟩
          · have hEqTerm :
                __eo_eq (__eo_list_erase_rec d x) d =
                  Term.Boolean false :=
              eo_eq_eq_false_of_ne_local hSame hEraseNe hDNe
            have hRecNe :
                __eo_list_diff_rec y (__eo_list_erase_rec d x) ≠
                  Term.Stuck := by
              change __eo_list_diff_rec y v0 ≠ Term.Stuck
              exact reInter_is_list_true_ne_stuck hIH.1
            have hDiffEq :
                __eo_list_diff_rec (mkReInter x y) d =
                  __eo_list_diff_rec y (__eo_list_erase_rec d x) := by
              simp [mkReInter, __eo_list_diff_rec, hEqTerm,
                __eo_prepend_if]
            rw [hDiffEq]
            exact ⟨hIH.1, hIH.2.1, by
              intro str
              constructor
              · intro hIn
                rcases hIn with ⟨hDiffIn, hDIn⟩
                have hEraseIn :
                    RegLanContains M (__eo_list_erase_rec d x) str :=
                  reInter_erase_rec_original_contains_implies_erase_contains
                    M d x str hDList hDWF hXWF hDIn
                rcases (hIH.2.2 str).1 ⟨hDiffIn, hEraseIn⟩ with
                  ⟨hYIn, _hEraseIn'⟩
                have hXIn : RegLanContains M x str :=
                  reInter_erase_rec_changed_and_original_contains_implies_lit_contains
                    M d x str hDList hDWF hXWF hDIn hSame
                exact ⟨
                  reInter_contains M x y str hXEval hYEval hXIn hYIn,
                  hDIn⟩
              · intro hIn
                rcases hIn with ⟨hCIn, hDIn⟩
                rcases reInter_contains_cases M x y str hXEval hYEval
                    hCIn with ⟨_hXIn, hYIn⟩
                have hEraseIn :
                    RegLanContains M (__eo_list_erase_rec d x) str :=
                  reInter_erase_rec_original_contains_implies_erase_contains
                    M d x str hDList hDWF hXWF hDIn
                rcases (hIH.2.2 str).2 ⟨hYIn, hEraseIn⟩ with
                  ⟨hDiffIn, _hEraseIn'⟩
                exact ⟨hDiffIn, hDIn⟩⟩
      | case4 nil d hNil hD hNot =>
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.re_inter) nil =
                Term.Boolean true := by
            have hGet :=
              eo_get_nil_rec_ne_stuck_of_is_list_true
                (Term.UOp UserOp.re_inter) nil hCList
            have hReq :
                __eo_requires
                    (__eo_is_list_nil (Term.UOp UserOp.re_inter) nil)
                    (Term.Boolean true) nil ≠ Term.Stuck := by
              simpa [__eo_get_nil_rec] using hGet
            exact eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.re_inter) nil)
              (Term.Boolean true) nil hReq
          have hDiffEq : __eo_list_diff_rec nil d = nil := by
            have hNilEq :=
              reInter_nil_eq_all_of_is_list_nil_true hNilTrue
            subst nil
            cases d
            case Stuck =>
              exact False.elim (hD rfl)
            all_goals rfl
          rw [hDiffEq]
          exact ⟨hCList, hCWF, by
            intro str
            constructor
            · intro hIn
              exact hIn
            · intro hIn
              exact hIn⟩

private theorem reUnion_l4_union_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (mkReUnion a (mkReUnion b (Term.UOp UserOp.re_none)))) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (mkReUnion a (mkReUnion b (Term.UOp UserOp.re_none)))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  refine ⟨native_re_union ra (native_re_union rb native_re_none), ?_, ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt a)
          (SmtTerm.re_union (__eo_to_smt b) SmtTerm.re_none)) =
      SmtValue.RegLan (native_re_union ra (native_re_union rb native_re_none))
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hAEval, hBEval]
  · exact reUnion_typeof_of_args a (mkReUnion b (Term.UOp UserOp.re_none))
      hATy (reUnion_typeof_of_args b (Term.UOp UserOp.re_none) hBTy
        (by native_decide))
  · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]
    intro str _hValid
    simp [native_str_in_re_mk_union_sem,
      native_str_in_re_empty]

private theorem re_ac_merge_union_l4_eq (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __eo_l_4___re_ac_merge (Term.UOp UserOp.re_union) a b =
      mkReUnion a (mkReUnion b (Term.UOp UserOp.re_none)) := by
  intro hA hB
  cases a <;> cases b <;>
    simp [__eo_l_4___re_ac_merge, __eo_mk_apply, __eo_nil] at hA hB ⊢

private theorem re_ac_merge_union_l4_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hA : a ≠ Term.Stuck)
    (hB : b ≠ Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  rw [re_ac_merge_union_l4_eq a b hA hB]
  exact reUnion_l4_union_eval_rel M a b ra rb hATy hBTy hAEval hBEval

private theorem reUnion_swap_union_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt (mkReUnion b a)) =
        SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt (mkReUnion b a)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  refine ⟨native_re_union rb ra, ?_, ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt b) (__eo_to_smt a)) =
      SmtValue.RegLan (native_re_union rb ra)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hAEval, hBEval]
  · exact reUnion_typeof_of_args b a hBTy hATy
  · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]
    intro str _hValid
    simp [native_str_in_re_mk_union_sem, Bool.or_comm]

private theorem reUnion_pair_union_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt (mkReUnion a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt (mkReUnion a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  refine ⟨native_re_union ra rb, ?_, ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.RegLan (native_re_union ra rb)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hAEval, hBEval]
  · exact reUnion_typeof_of_args a b hATy hBTy
  · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]

private theorem reUnion_subsumed_right_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hSub :
      ∀ str, RegLanContains M b str -> RegLanContains M a str) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  refine ⟨ra, hAEval, hATy, ?_⟩
  exact smt_value_rel_reglan_native_union_of_contains_iff
    M a a b ra ra rb hAEval hAEval hBEval (by
      intro str
      constructor
      · intro hAIn
        exact Or.inl hAIn
      · intro hIn
        rcases hIn with hAIn | hBIn
        · exact hAIn
        · exact hSub str hBIn)

private theorem reUnion_subsumed_left_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hSub :
      ∀ str, RegLanContains M a str -> RegLanContains M b str) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  refine ⟨rb, hBEval, hBTy, ?_⟩
  exact smt_value_rel_reglan_native_union_of_contains_iff
    M b a b rb ra rb hBEval hAEval hBEval (by
      intro str
      constructor
      · intro hBIn
        exact Or.inr hBIn
      · intro hIn
        rcases hIn with hAIn | hBIn
        · exact hSub str hAIn
        · exact hBIn)

private theorem reUnion_concat_diff_union_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hAList :
      __eo_is_list (Term.UOp UserOp.re_union) a = Term.Boolean true)
    (hBList :
      __eo_is_list (Term.UOp UserOp.re_union) b = Term.Boolean true)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_union)
              (__eo_list_diff (Term.UOp UserOp.re_union) a b) b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_union)
              (__eo_list_diff (Term.UOp UserOp.re_union) a b) b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  have hAWF : ReUnionListWF M a :=
    reUnionListWF_of_type_eval M a ra hATy hAEval
  have hBWF : ReUnionListWF M b :=
    reUnionListWF_of_type_eval M b rb hBTy hBEval
  have hDiff :=
    reUnion_list_diff_rec_wf_contains M a b hAList hBList hAWF hBWF
  have hDiffEq :
      __eo_list_diff (Term.UOp UserOp.re_union) a b =
        __eo_list_diff_rec a b := by
    simp [__eo_list_diff, hAList, hBList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not]
  have hConcat :=
    reUnion_list_concat_rec_wf_contains M (__eo_list_diff_rec a b) b
      hDiff.1 hBList hDiff.2.1 hBWF
  have hConcatEq :
      __eo_list_concat (Term.UOp UserOp.re_union)
          (__eo_list_diff (Term.UOp UserOp.re_union) a b) b =
        __eo_list_concat_rec (__eo_list_diff_rec a b) b := by
    simp [__eo_list_concat, hDiffEq, hDiff.1, hBList, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not]
  rcases reUnionListWF_eval hConcat.2.1 with ⟨r, hRecEval⟩
  have hRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) :=
    smt_value_rel_reglan_native_union_of_contains_iff M
      (__eo_list_concat_rec (__eo_list_diff_rec a b) b) a b
      r ra rb hRecEval hAEval hBEval (by
        intro str
        exact Iff.trans (hConcat.2.2 str) (hDiff.2.2 str))
  refine ⟨r, ?_, ?_, hRel⟩
  · rw [hConcatEq]
    exact hRecEval
  · rw [hConcatEq]
    exact reUnionListWF_type hConcat.2.1

private theorem eo_eq_re_union_true
    (f : Term) :
    __eo_eq (Term.UOp UserOp.re_union) f = Term.Boolean true ->
    f = Term.UOp UserOp.re_union := by
  intro h
  cases f <;> simp [__eo_eq, native_teq] at h
  case UOp op =>
    cases op <;> simp  at h ⊢

private theorem eo_and_true_cases
    (x y : Term) :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not, SmtEval.native_and] at h ⊢
  all_goals
    try (split at h <;> simp at h)
  simpa using h

private theorem reUnion_list_find_list_true_of_nonneg
    (c e : Term) :
    __eo_is_neg (__eo_list_find (Term.UOp UserOp.re_union) c e) =
      Term.Boolean false ->
    __eo_is_list (Term.UOp UserOp.re_union) c = Term.Boolean true := by
  intro hFind
  have hFindNe :
      __eo_list_find (Term.UOp UserOp.re_union) c e ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hFind
    simp [__eo_is_neg] at hFind
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_union) c)
          (Term.Boolean true)
          (__eo_list_find_rec c e (Term.Numeral 0)) ≠ Term.Stuck := by
    simpa [__eo_list_find] using hFindNe
  exact eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.re_union) c)
    (Term.Boolean true)
    (__eo_list_find_rec c e (Term.Numeral 0)) hReq

private theorem reUnion_lists_of_concat_diff_union_ne_stuck
    (a b : Term) :
    __eo_list_concat (Term.UOp UserOp.re_union)
        (__eo_list_diff (Term.UOp UserOp.re_union) a b) b ≠
      Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.re_union) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_union) b = Term.Boolean true := by
  intro hConcatNe
  let diff := __eo_list_diff (Term.UOp UserOp.re_union) a b
  have hOuterReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_union) diff)
          (Term.Boolean true)
          (__eo_requires (__eo_is_list (Term.UOp UserOp.re_union) b)
            (Term.Boolean true) (__eo_list_concat_rec diff b)) ≠
        Term.Stuck := by
    simpa [diff, __eo_list_concat] using hConcatNe
  have hDiffList :
      __eo_is_list (Term.UOp UserOp.re_union) diff =
        Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.re_union) diff)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.re_union) b)
        (Term.Boolean true) (__eo_list_concat_rec diff b))
      hOuterReq
  have hInnerReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_union) b)
          (Term.Boolean true) (__eo_list_concat_rec diff b) ≠
        Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.re_union) diff)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.re_union) b)
        (Term.Boolean true) (__eo_list_concat_rec diff b))
      hOuterReq
  have hBList :
      __eo_is_list (Term.UOp UserOp.re_union) b =
        Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.re_union) b)
      (Term.Boolean true) (__eo_list_concat_rec diff b) hInnerReq
  have hDiffNe : diff ≠ Term.Stuck :=
    reUnion_is_list_true_ne_stuck hDiffList
  have hDiffReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_union) a)
          (Term.Boolean true)
          (__eo_requires (__eo_is_list (Term.UOp UserOp.re_union) b)
            (Term.Boolean true) (__eo_list_diff_rec a b)) ≠
        Term.Stuck := by
    simpa [diff, __eo_list_diff] using hDiffNe
  have hAList :
      __eo_is_list (Term.UOp UserOp.re_union) a =
        Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.re_union) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.re_union) b)
        (Term.Boolean true) (__eo_list_diff_rec a b))
      hDiffReq
  exact ⟨hAList, hBList⟩

private theorem reInter_l4_inter_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (mkReInter a (mkReInter b (Term.UOp UserOp.re_all)))) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (mkReInter a (mkReInter b (Term.UOp UserOp.re_all)))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  refine ⟨native_re_inter ra (native_re_inter rb native_re_all), ?_, ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt a)
          (SmtTerm.re_inter (__eo_to_smt b) SmtTerm.re_all)) =
      SmtValue.RegLan (native_re_inter ra (native_re_inter rb native_re_all))
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hAEval, hBEval]
  · exact reInter_typeof_of_args a (mkReInter b (Term.UOp UserOp.re_all))
      hATy (reInter_typeof_of_args b (Term.UOp UserOp.re_all) hBTy
        (by native_decide))
  · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]
    intro str hValid
    simp [native_str_in_re_mk_inter_sem,
      native_str_in_re_all_valid_local str hValid]

private theorem re_ac_merge_inter_l4_eq (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __eo_l_4___re_ac_merge (Term.UOp UserOp.re_inter) a b =
      mkReInter a (mkReInter b (Term.UOp UserOp.re_all)) := by
  intro hA hB
  cases a <;> cases b <;>
    simp [__eo_l_4___re_ac_merge, __eo_mk_apply, __eo_nil] at hA hB ⊢

private theorem re_ac_merge_inter_l4_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hA : a ≠ Term.Stuck)
    (hB : b ≠ Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  rw [re_ac_merge_inter_l4_eq a b hA hB]
  exact reInter_l4_inter_eval_rel M a b ra rb hATy hBTy hAEval hBEval

private theorem reInter_swap_inter_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt (mkReInter b a)) =
        SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt (mkReInter b a)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  refine ⟨native_re_inter rb ra, ?_, ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt b) (__eo_to_smt a)) =
      SmtValue.RegLan (native_re_inter rb ra)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hAEval, hBEval]
  · exact reInter_typeof_of_args b a hBTy hATy
  · exact smt_value_rel_re_inter_comm rb ra

private theorem reInter_pair_inter_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt (mkReInter a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt (mkReInter a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  refine ⟨native_re_inter ra rb, ?_, ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.RegLan (native_re_inter ra rb)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hAEval, hBEval]
  · exact reInter_typeof_of_args a b hATy hBTy
  · exact RuleProofs.smt_value_rel_refl
      (SmtValue.RegLan (native_re_inter ra rb))

private theorem reInter_subsumed_right_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hSub :
      ∀ str, RegLanContains M a str -> RegLanContains M b str) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  refine ⟨ra, hAEval, hATy, ?_⟩
  exact smt_value_rel_reglan_native_inter_of_contains_iff
    M a a b ra ra rb hAEval hAEval hBEval (by
      intro str
      constructor
      · intro hAIn
        exact ⟨hAIn, hSub str hAIn⟩
      · intro hIn
        exact hIn.1)

private theorem reInter_subsumed_left_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hSub :
      ∀ str, RegLanContains M b str -> RegLanContains M a str) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  refine ⟨rb, hBEval, hBTy, ?_⟩
  exact smt_value_rel_reglan_native_inter_of_contains_iff
    M b a b rb ra rb hBEval hAEval hBEval (by
      intro str
      constructor
      · intro hBIn
        exact ⟨hSub str hBIn, hBIn⟩
      · intro hIn
        exact hIn.2)

private theorem reInter_concat_diff_inter_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hAList :
      __eo_is_list (Term.UOp UserOp.re_inter) a = Term.Boolean true)
    (hBList :
      __eo_is_list (Term.UOp UserOp.re_inter) b = Term.Boolean true)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_inter)
              (__eo_list_diff (Term.UOp UserOp.re_inter) a b) b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.re_inter)
              (__eo_list_diff (Term.UOp UserOp.re_inter) a b) b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  have hAWF : ReInterListWF M a :=
    reInterListWF_of_type_eval M a ra hATy hAEval
  have hBWF : ReInterListWF M b :=
    reInterListWF_of_type_eval M b rb hBTy hBEval
  have hDiff :=
    reInter_list_diff_rec_wf_contains M a b hAList hBList hAWF hBWF
  have hDiffEq :
      __eo_list_diff (Term.UOp UserOp.re_inter) a b =
        __eo_list_diff_rec a b := by
    simp [__eo_list_diff, hAList, hBList, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not]
  have hConcat :=
    reInter_list_concat_rec_wf_contains M (__eo_list_diff_rec a b) b
      hDiff.1 hBList hDiff.2.1 hBWF
  have hConcatEq :
      __eo_list_concat (Term.UOp UserOp.re_inter)
          (__eo_list_diff (Term.UOp UserOp.re_inter) a b) b =
        __eo_list_concat_rec (__eo_list_diff_rec a b) b := by
    simp [__eo_list_concat, hDiffEq, hDiff.1, hBList, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not]
  rcases reInterListWF_eval hConcat.2.1 with ⟨r, hRecEval⟩
  have hRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) :=
    smt_value_rel_reglan_native_inter_of_contains_iff M
      (__eo_list_concat_rec (__eo_list_diff_rec a b) b) a b
      r ra rb hRecEval hAEval hBEval (by
        intro str
        exact Iff.trans (hConcat.2.2 str) (hDiff.2.2 str))
  refine ⟨r, ?_, ?_, hRel⟩
  · rw [hConcatEq]
    exact hRecEval
  · rw [hConcatEq]
    exact reInterListWF_type hConcat.2.1

private theorem eo_eq_re_inter_true
    (f : Term) :
    __eo_eq (Term.UOp UserOp.re_inter) f = Term.Boolean true ->
    f = Term.UOp UserOp.re_inter := by
  intro h
  cases f <;> simp [__eo_eq, native_teq] at h
  case UOp op =>
    cases op <;> simp  at h ⊢

private theorem reInter_list_find_list_true_of_nonneg
    (c e : Term) :
    __eo_is_neg (__eo_list_find (Term.UOp UserOp.re_inter) c e) =
      Term.Boolean false ->
    __eo_is_list (Term.UOp UserOp.re_inter) c = Term.Boolean true := by
  intro hFind
  have hFindNe :
      __eo_list_find (Term.UOp UserOp.re_inter) c e ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hFind
    simp [__eo_is_neg] at hFind
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) c)
          (Term.Boolean true)
          (__eo_list_find_rec c e (Term.Numeral 0)) ≠ Term.Stuck := by
    simpa [__eo_list_find] using hFindNe
  exact eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.re_inter) c)
    (Term.Boolean true)
    (__eo_list_find_rec c e (Term.Numeral 0)) hReq

private theorem reInter_lists_of_concat_diff_inter_ne_stuck
    (a b : Term) :
    __eo_list_concat (Term.UOp UserOp.re_inter)
        (__eo_list_diff (Term.UOp UserOp.re_inter) a b) b ≠
      Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.re_inter) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_inter) b = Term.Boolean true := by
  intro hConcatNe
  let diff := __eo_list_diff (Term.UOp UserOp.re_inter) a b
  have hOuterReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) diff)
          (Term.Boolean true)
          (__eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) b)
            (Term.Boolean true) (__eo_list_concat_rec diff b)) ≠
        Term.Stuck := by
    simpa [diff, __eo_list_concat] using hConcatNe
  have hDiffList :
      __eo_is_list (Term.UOp UserOp.re_inter) diff =
        Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.re_inter) diff)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) b)
        (Term.Boolean true) (__eo_list_concat_rec diff b))
      hOuterReq
  have hInnerReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) b)
          (Term.Boolean true) (__eo_list_concat_rec diff b) ≠
        Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.re_inter) diff)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) b)
        (Term.Boolean true) (__eo_list_concat_rec diff b))
      hOuterReq
  have hBList :
      __eo_is_list (Term.UOp UserOp.re_inter) b =
        Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.re_inter) b)
      (Term.Boolean true) (__eo_list_concat_rec diff b) hInnerReq
  have hDiffNe : diff ≠ Term.Stuck :=
    reInter_is_list_true_ne_stuck hDiffList
  have hDiffReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) a)
          (Term.Boolean true)
          (__eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) b)
            (Term.Boolean true) (__eo_list_diff_rec a b)) ≠
        Term.Stuck := by
    simpa [diff, __eo_list_diff] using hDiffNe
  have hAList :
      __eo_is_list (Term.UOp UserOp.re_inter) a =
        Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.re_inter) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.re_inter) b)
        (Term.Boolean true) (__eo_list_diff_rec a b))
      hDiffReq
  exact ⟨hAList, hBList⟩

private theorem re_ac_merge_union_l3_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe :
      __eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a b ≠
        Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
  by_cases hBShape :
      ∃ f r rr, b = Term.Apply (Term.Apply f r) rr
  · rcases hBShape with ⟨f, r, rr, rfl⟩
    have hShape :
        __eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a
            (Term.Apply (Term.Apply f r) rr) =
          __eo_ite (__eo_eq (Term.UOp UserOp.re_union) f)
            (__eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_union)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                  a))
              (mkReUnion a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
            (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_union) a
              (Term.Apply (Term.Apply f r) rr)) := by
      cases a <;> simp_all [__eo_l_3___re_ac_merge]
    have hTopNe :
        __eo_ite (__eo_eq (Term.UOp UserOp.re_union) f)
            (__eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_union)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                  a))
              (mkReUnion a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
            (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_union) a
              (Term.Apply (Term.Apply f r) rr)) ≠ Term.Stuck := by
      rwa [← hShape]
    rcases eo_ite_cases_of_ne_stuck
        (__eo_eq (Term.UOp UserOp.re_union) f)
        (__eo_ite
          (__eo_is_neg
            (__eo_list_find (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) a))
          (mkReUnion a
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
        (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_union) a
          (Term.Apply (Term.Apply f r) rr))
        hTopNe with hHead | hHead
    · have hf : f = Term.UOp UserOp.re_union :=
        eo_eq_re_union_true f hHead
      subst f
      have hBranchNe :
          __eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_union)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                  a))
              (mkReUnion a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) ≠
            Term.Stuck := by
        exact hTopNe
      rcases eo_ite_cases_of_ne_stuck
          (__eo_is_neg
            (__eo_list_find (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) a))
          (mkReUnion a
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
          hBranchNe with hFind | hFind
      · have hEq :
            __eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) =
              mkReUnion a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) := by
          rw [hShape, hHead, hFind]
          rfl
        rw [hEq]
        exact reUnion_pair_union_eval_rel M a
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
          ra rb hATy hBTy hAEval hBEval
      · have hList :
            __eo_is_list (Term.UOp UserOp.re_union)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) =
              Term.Boolean true :=
          reUnion_list_find_list_true_of_nonneg
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
            a hFind
        have hBWF : ReUnionListWF M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) :=
          reUnionListWF_of_type_eval M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
            rb hBTy hBEval
        have hAWF : ReUnionListWF M a :=
          reUnionListWF_of_type_eval M a ra hATy hAEval
        have hSub :
            ∀ str,
              RegLanContains M a str ->
                RegLanContains M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                  str := by
          intro str hIn
          exact reUnion_list_find_nonneg_contains M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
            a str hList hBWF hAWF hFind hIn
        have hEq :
            __eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) =
              Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr := by
          rw [hShape, hHead, hFind]
          rfl
        rw [hEq]
        exact reUnion_subsumed_left_eval_rel M a
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
          ra rb hBTy hAEval hBEval hSub
    · have hEq :
          __eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a
              (Term.Apply (Term.Apply f r) rr) =
            __eo_l_4___re_ac_merge (Term.UOp UserOp.re_union) a
              (Term.Apply (Term.Apply f r) rr) := by
        rw [hShape, hHead]
        rfl
      rw [hEq]
      exact re_ac_merge_union_l4_eval_rel M a
        (Term.Apply (Term.Apply f r) rr) ra rb hATy hBTy hAEval hBEval
        hANe hBNe
  · have hEq :
        __eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a b =
          __eo_l_4___re_ac_merge (Term.UOp UserOp.re_union) a b := by
      cases b
      case Apply bf rr =>
        cases bf <;> cases a <;> simp_all [__eo_l_3___re_ac_merge]
      all_goals
        cases a <;> simp_all [__eo_l_3___re_ac_merge]
    rw [hEq]
    exact re_ac_merge_union_l4_eval_rel M a b ra rb hATy hBTy hAEval
      hBEval hANe hBNe

private theorem re_ac_merge_union_l2_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe :
      __eo_l_2___re_ac_merge (Term.UOp UserOp.re_union) a b ≠
        Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
  by_cases hAShape :
      ∃ f r rr, a = Term.Apply (Term.Apply f r) rr
  · rcases hAShape with ⟨f, r, rr, rfl⟩
    have hShape :
        __eo_l_2___re_ac_merge (Term.UOp UserOp.re_union)
            (Term.Apply (Term.Apply f r) rr) b =
          __eo_ite (__eo_eq (Term.UOp UserOp.re_union) f)
            (__eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_union)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                  b))
              (mkReUnion b
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
            (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply f r) rr) b) := by
      cases b <;> simp_all [__eo_l_2___re_ac_merge]
    have hTopNe :
        __eo_ite (__eo_eq (Term.UOp UserOp.re_union) f)
            (__eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_union)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                  b))
              (mkReUnion b
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
            (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply f r) rr) b) ≠ Term.Stuck := by
      rwa [← hShape]
    rcases eo_ite_cases_of_ne_stuck
        (__eo_eq (Term.UOp UserOp.re_union) f)
        (__eo_ite
          (__eo_is_neg
            (__eo_list_find (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) b))
          (mkReUnion b
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
        (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_union)
          (Term.Apply (Term.Apply f r) rr) b)
        hTopNe with hHead | hHead
    · have hf : f = Term.UOp UserOp.re_union :=
        eo_eq_re_union_true f hHead
      subst f
      have hBranchNe :
          __eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_union)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                  b))
              (mkReUnion b
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) ≠
            Term.Stuck := by
        exact hTopNe
      rcases eo_ite_cases_of_ne_stuck
          (__eo_is_neg
            (__eo_list_find (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) b))
          (mkReUnion b
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
          hBranchNe with hFind | hFind
      · have hEq :
            __eo_l_2___re_ac_merge (Term.UOp UserOp.re_union)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                b =
              mkReUnion b
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) := by
          rw [hShape, hHead, hFind]
          rfl
        rw [hEq]
        exact reUnion_swap_union_eval_rel M
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) b
          ra rb hATy hBTy hAEval hBEval
      · have hList :
            __eo_is_list (Term.UOp UserOp.re_union)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) =
              Term.Boolean true :=
          reUnion_list_find_list_true_of_nonneg
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
            b hFind
        have hAWF : ReUnionListWF M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr) :=
          reUnionListWF_of_type_eval M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
            ra hATy hAEval
        have hBWF : ReUnionListWF M b :=
          reUnionListWF_of_type_eval M b rb hBTy hBEval
        have hSub :
            ∀ str,
              RegLanContains M b str ->
                RegLanContains M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                  str := by
          intro str hIn
          exact reUnion_list_find_nonneg_contains M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
            b str hList hAWF hBWF hFind hIn
        have hEq :
            __eo_l_2___re_ac_merge (Term.UOp UserOp.re_union)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                b =
              Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr := by
          rw [hShape, hHead, hFind]
          rfl
        rw [hEq]
        exact reUnion_subsumed_right_eval_rel M
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
          b ra rb hATy hAEval hBEval hSub
    · have hEq :
          __eo_l_2___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply f r) rr) b =
            __eo_l_3___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply f r) rr) b := by
        rw [hShape, hHead]
        rfl
      rw [hEq]
      exact re_ac_merge_union_l3_eval_rel M
        (Term.Apply (Term.Apply f r) rr) b ra rb hATy hBTy hAEval
        hBEval (by rwa [← hEq])
  · have hEq :
        __eo_l_2___re_ac_merge (Term.UOp UserOp.re_union) a b =
          __eo_l_3___re_ac_merge (Term.UOp UserOp.re_union) a b := by
      cases a
      case Apply af rr =>
        cases af <;> cases b <;> simp_all [__eo_l_2___re_ac_merge]
      all_goals
        cases b <;> simp_all [__eo_l_2___re_ac_merge]
    rw [hEq]
    exact re_ac_merge_union_l3_eval_rel M a b ra rb hATy hBTy hAEval
      hBEval (by rwa [← hEq])

private theorem re_ac_merge_union_l1_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe :
      __eo_l_1___re_ac_merge (Term.UOp UserOp.re_union) a b ≠
        Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_1___re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_1___re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
  by_cases hBothShape :
      ∃ f r rr g s ss,
        a = Term.Apply (Term.Apply f r) rr ∧
          b = Term.Apply (Term.Apply g s) ss
  · rcases hBothShape with ⟨f, r, rr, g, s, ss, rfl, rfl⟩
    have hShape :
        __eo_l_1___re_ac_merge (Term.UOp UserOp.re_union)
            (Term.Apply (Term.Apply f r) rr)
            (Term.Apply (Term.Apply g s) ss) =
          __eo_ite
            (__eo_and (__eo_eq (Term.UOp UserOp.re_union) f)
              (__eo_eq (Term.UOp UserOp.re_union) g))
            (__eo_list_concat (Term.UOp UserOp.re_union)
              (__eo_list_diff (Term.UOp UserOp.re_union)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss))
            (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply f r) rr)
              (Term.Apply (Term.Apply g s) ss)) := by
      rfl
    have hTopNe :
        __eo_ite
            (__eo_and (__eo_eq (Term.UOp UserOp.re_union) f)
              (__eo_eq (Term.UOp UserOp.re_union) g))
            (__eo_list_concat (Term.UOp UserOp.re_union)
              (__eo_list_diff (Term.UOp UserOp.re_union)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss))
            (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply f r) rr)
              (Term.Apply (Term.Apply g s) ss)) ≠ Term.Stuck := by
      rwa [← hShape]
    rcases eo_ite_cases_of_ne_stuck
        (__eo_and (__eo_eq (Term.UOp UserOp.re_union) f)
          (__eo_eq (Term.UOp UserOp.re_union) g))
        (__eo_list_concat (Term.UOp UserOp.re_union)
          (__eo_list_diff (Term.UOp UserOp.re_union)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss))
        (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_union)
          (Term.Apply (Term.Apply f r) rr)
          (Term.Apply (Term.Apply g s) ss))
        hTopNe with hHead | hHead
    · rcases eo_and_true_cases
          (__eo_eq (Term.UOp UserOp.re_union) f)
          (__eo_eq (Term.UOp UserOp.re_union) g) hHead with
        ⟨hF, hG⟩
      have hf : f = Term.UOp UserOp.re_union :=
        eo_eq_re_union_true f hF
      have hg : g = Term.UOp UserOp.re_union :=
        eo_eq_re_union_true g hG
      subst f
      subst g
      have hConcatNe :
          __eo_list_concat (Term.UOp UserOp.re_union)
              (__eo_list_diff (Term.UOp UserOp.re_union)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss) ≠
            Term.Stuck := by
        exact hTopNe
      rcases reUnion_lists_of_concat_diff_union_ne_stuck
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss)
          hConcatNe with ⟨hAList, hBList⟩
      have hEq :
          __eo_l_1___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss) =
            __eo_list_concat (Term.UOp UserOp.re_union)
              (__eo_list_diff (Term.UOp UserOp.re_union)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss) := by
        rw [hShape, hHead]
        rfl
      rw [hEq]
      exact reUnion_concat_diff_union_eval_rel M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) rr)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) s) ss)
        ra rb hAList hBList hATy hBTy hAEval hBEval
    · have hEq :
          __eo_l_1___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply f r) rr)
              (Term.Apply (Term.Apply g s) ss) =
            __eo_l_2___re_ac_merge (Term.UOp UserOp.re_union)
              (Term.Apply (Term.Apply f r) rr)
              (Term.Apply (Term.Apply g s) ss) := by
        rw [hShape, hHead]
        rfl
      rw [hEq]
      exact re_ac_merge_union_l2_eval_rel M
        (Term.Apply (Term.Apply f r) rr)
        (Term.Apply (Term.Apply g s) ss) ra rb hATy hBTy hAEval hBEval
        (by rwa [← hEq])
  · have hEq :
        __eo_l_1___re_ac_merge (Term.UOp UserOp.re_union) a b =
          __eo_l_2___re_ac_merge (Term.UOp UserOp.re_union) a b := by
      cases a
      case Apply af arr =>
        cases af
        case Apply f r =>
          cases b
          case Apply bf brr =>
            cases bf <;> simp_all [__eo_l_1___re_ac_merge]
          all_goals
            simp_all [__eo_l_1___re_ac_merge]
        all_goals
          cases b <;> simp_all [__eo_l_1___re_ac_merge]
      all_goals
        cases b <;> simp_all [__eo_l_1___re_ac_merge]
    rw [hEq]
    exact re_ac_merge_union_l2_eval_rel M a b ra rb hATy hBTy hAEval
      hBEval (by rwa [← hEq])

private theorem re_ac_merge_union_self_eq (a : Term) :
    a ≠ Term.Stuck ->
    __re_ac_merge (Term.UOp UserOp.re_union) a a = a := by
  intro hA
  have hEqTerm : __eo_eq a a = Term.Boolean true :=
    eo_eq_eq_true_of_eq_local rfl hA hA
  cases a <;> try
    simp [__re_ac_merge, hEqTerm, __eo_ite, native_ite, native_teq] at hA ⊢
  case UOp op =>
    cases op <;>
      simp [hEqTerm]

private theorem re_ac_merge_union_none_left_eq (b : Term) :
    b ≠ Term.Stuck ->
    __re_ac_merge (Term.UOp UserOp.re_union)
      (Term.UOp UserOp.re_none) b = b := by
  intro hB
  cases b <;> simp [__re_ac_merge] at hB ⊢

private theorem re_ac_merge_union_eq_l1
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    a ≠ Term.UOp UserOp.re_none ->
    a ≠ b ->
    __re_ac_merge (Term.UOp UserOp.re_union) a b =
      __eo_l_1___re_ac_merge (Term.UOp UserOp.re_union) a b := by
  intro hA hB hNone hEq
  have hEqTerm :
      __eo_eq a b = Term.Boolean false :=
    eo_eq_eq_false_of_ne_local hEq hA hB
  have hShape :
      __re_ac_merge (Term.UOp UserOp.re_union) a b =
        __eo_ite (__eo_eq a b) a
          (__eo_l_1___re_ac_merge (Term.UOp UserOp.re_union) a b) := by
    cases a <;> try simp_all
    case UOp op =>
      cases op <;> cases b <;> simp_all [__re_ac_merge]
    all_goals
      cases b <;> simp_all [__re_ac_merge]
  rw [hShape, hEqTerm]
  rfl

private theorem re_ac_merge_union_none_left_eval_rel
    (M : SmtModel) (b : Term) (ra rb : SmtRegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval :
      __smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_none)) =
        SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_ac_merge (Term.UOp UserOp.re_union)
              (Term.UOp UserOp.re_none) b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_ac_merge (Term.UOp UserOp.re_union)
              (Term.UOp UserOp.re_none) b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  have hRa : ra = native_re_none := by
    have hAEval' : SmtValue.RegLan native_re_none = SmtValue.RegLan ra := by
      simpa [__smtx_model_eval] using hAEval
    cases hAEval'
    rfl
  have hMergeEq :
      __re_ac_merge (Term.UOp UserOp.re_union)
        (Term.UOp UserOp.re_none) b = b :=
    re_ac_merge_union_none_left_eq b (regLanEval_ne_stuck ⟨rb, hBEval⟩)
  subst ra
  refine ⟨rb, ?_, ?_, ?_⟩
  · rw [hMergeEq]
    exact hBEval
  · rw [hMergeEq]
    exact hBTy
  · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]
    intro str _hValid
    simp [native_str_in_re_mk_union_sem,
      native_str_in_re_empty]

private theorem re_ac_merge_union_self_eval_rel
    (M : SmtModel) (a : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_ac_merge (Term.UOp UserOp.re_union) a a)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_ac_merge (Term.UOp UserOp.re_union) a a)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  have hAStuck : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hMergeEq :
      __re_ac_merge (Term.UOp UserOp.re_union) a a = a :=
    re_ac_merge_union_self_eq a hAStuck
  have hRb : rb = ra := by
    rw [hAEval] at hBEval
    cases hBEval
    rfl
  subst rb
  refine ⟨ra, ?_, ?_, ?_⟩
  · rw [hMergeEq]
    exact hAEval
  · rw [hMergeEq]
    exact hATy
  · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]
    intro str _hValid
    simp [native_str_in_re_mk_union_sem]

private theorem re_ac_merge_union_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe :
      __re_ac_merge (Term.UOp UserOp.re_union) a b ≠ Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt (__re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt (__re_ac_merge (Term.UOp UserOp.re_union) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_union ra rb)) := by
  by_cases hNone : a = Term.UOp UserOp.re_none
  · subst a
    exact re_ac_merge_union_none_left_eval_rel M b ra rb hBTy hAEval hBEval
  · by_cases hEq : a = b
    · subst b
      exact re_ac_merge_union_self_eval_rel M a ra rb hATy hAEval hBEval
    · have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
      have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
      have hMergeEq :
          __re_ac_merge (Term.UOp UserOp.re_union) a b =
            __eo_l_1___re_ac_merge (Term.UOp UserOp.re_union) a b :=
        re_ac_merge_union_eq_l1 a b hANe hBNe hNone hEq
      rw [hMergeEq]
      exact re_ac_merge_union_l1_eval_rel M a b ra rb hATy hBTy hAEval
        hBEval (by rwa [← hMergeEq])

private theorem re_ac_merge_inter_l3_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe :
      __eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a b ≠
        Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
  by_cases hBShape :
      ∃ f r rr, b = Term.Apply (Term.Apply f r) rr
  · rcases hBShape with ⟨f, r, rr, rfl⟩
    have hShape :
        __eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a
            (Term.Apply (Term.Apply f r) rr) =
          __eo_ite (__eo_eq (Term.UOp UserOp.re_inter) f)
            (__eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_inter)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                  a))
              (mkReInter a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
            (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_inter) a
              (Term.Apply (Term.Apply f r) rr)) := by
      cases a <;> simp_all [__eo_l_3___re_ac_merge]
    have hTopNe :
        __eo_ite (__eo_eq (Term.UOp UserOp.re_inter) f)
            (__eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_inter)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                  a))
              (mkReInter a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
            (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_inter) a
              (Term.Apply (Term.Apply f r) rr)) ≠ Term.Stuck := by
      rwa [← hShape]
    rcases eo_ite_cases_of_ne_stuck
        (__eo_eq (Term.UOp UserOp.re_inter) f)
        (__eo_ite
          (__eo_is_neg
            (__eo_list_find (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) a))
          (mkReInter a
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
        (__eo_l_4___re_ac_merge (Term.UOp UserOp.re_inter) a
          (Term.Apply (Term.Apply f r) rr))
        hTopNe with hHead | hHead
    · have hf : f = Term.UOp UserOp.re_inter :=
        eo_eq_re_inter_true f hHead
      subst f
      have hBranchNe :
          __eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_inter)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                  a))
              (mkReInter a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) ≠
            Term.Stuck := by
        exact hTopNe
      rcases eo_ite_cases_of_ne_stuck
          (__eo_is_neg
            (__eo_list_find (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) a))
          (mkReInter a
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
          hBranchNe with hFind | hFind
      · have hEq :
            __eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) =
              mkReInter a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) := by
          rw [hShape, hHead, hFind]
          rfl
        rw [hEq]
        exact reInter_pair_inter_eval_rel M a
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
          ra rb hATy hBTy hAEval hBEval
      · have hList :
            __eo_is_list (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) =
              Term.Boolean true :=
          reInter_list_find_list_true_of_nonneg
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
            a hFind
        have hBWF : ReInterListWF M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) :=
          reInterListWF_of_type_eval M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
            rb hBTy hBEval
        have hAWF : ReInterListWF M a :=
          reInterListWF_of_type_eval M a ra hATy hAEval
        have hSub :
            ∀ str,
              RegLanContains M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                  str ->
                RegLanContains M a str := by
          intro str hIn
          exact reInter_list_find_nonneg_contains M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
            a str hList hBWF hAWF hFind hIn
        have hEq :
            __eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) =
              Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr := by
          rw [hShape, hHead, hFind]
          rfl
        rw [hEq]
        exact reInter_subsumed_left_eval_rel M a
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
          ra rb hBTy hAEval hBEval hSub
    · have hEq :
          __eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a
              (Term.Apply (Term.Apply f r) rr) =
            __eo_l_4___re_ac_merge (Term.UOp UserOp.re_inter) a
              (Term.Apply (Term.Apply f r) rr) := by
        rw [hShape, hHead]
        rfl
      rw [hEq]
      exact re_ac_merge_inter_l4_eval_rel M a
        (Term.Apply (Term.Apply f r) rr) ra rb hATy hBTy hAEval hBEval
        hANe hBNe
  · have hEq :
        __eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a b =
          __eo_l_4___re_ac_merge (Term.UOp UserOp.re_inter) a b := by
      cases b
      case Apply bf rr =>
        cases bf <;> cases a <;> simp_all [__eo_l_3___re_ac_merge]
      all_goals
        cases a <;> simp_all [__eo_l_3___re_ac_merge]
    rw [hEq]
    exact re_ac_merge_inter_l4_eval_rel M a b ra rb hATy hBTy hAEval
      hBEval hANe hBNe

private theorem re_ac_merge_inter_l2_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe :
      __eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter) a b ≠
        Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
  by_cases hAShape :
      ∃ f r rr, a = Term.Apply (Term.Apply f r) rr
  · rcases hAShape with ⟨f, r, rr, rfl⟩
    have hShape :
        __eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter)
            (Term.Apply (Term.Apply f r) rr) b =
          __eo_ite (__eo_eq (Term.UOp UserOp.re_inter) f)
            (__eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_inter)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                  b))
              (mkReInter b
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
            (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply f r) rr) b) := by
      cases b <;> simp_all [__eo_l_2___re_ac_merge]
    have hTopNe :
        __eo_ite (__eo_eq (Term.UOp UserOp.re_inter) f)
            (__eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_inter)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                  b))
              (mkReInter b
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
            (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply f r) rr) b) ≠ Term.Stuck := by
      rwa [← hShape]
    rcases eo_ite_cases_of_ne_stuck
        (__eo_eq (Term.UOp UserOp.re_inter) f)
        (__eo_ite
          (__eo_is_neg
            (__eo_list_find (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) b))
          (mkReInter b
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
        (__eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter)
          (Term.Apply (Term.Apply f r) rr) b)
        hTopNe with hHead | hHead
    · have hf : f = Term.UOp UserOp.re_inter :=
        eo_eq_re_inter_true f hHead
      subst f
      have hBranchNe :
          __eo_ite
              (__eo_is_neg
                (__eo_list_find (Term.UOp UserOp.re_inter)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                  b))
              (mkReInter b
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) ≠
            Term.Stuck := by
        exact hTopNe
      rcases eo_ite_cases_of_ne_stuck
          (__eo_is_neg
            (__eo_list_find (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) b))
          (mkReInter b
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
          hBranchNe with hFind | hFind
      · have hEq :
            __eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                b =
              mkReInter b
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) := by
          rw [hShape, hHead, hFind]
          rfl
        rw [hEq]
        exact reInter_swap_inter_eval_rel M
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) b
          ra rb hATy hBTy hAEval hBEval
      · have hList :
            __eo_is_list (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) =
              Term.Boolean true :=
          reInter_list_find_list_true_of_nonneg
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
            b hFind
        have hAWF : ReInterListWF M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr) :=
          reInterListWF_of_type_eval M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
            ra hATy hAEval
        have hBWF : ReInterListWF M b :=
          reInterListWF_of_type_eval M b rb hBTy hBEval
        have hSub :
            ∀ str,
              RegLanContains M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                  str ->
                RegLanContains M b str := by
          intro str hIn
          exact reInter_list_find_nonneg_contains M
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
            b str hList hAWF hBWF hFind hIn
        have hEq :
            __eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                b =
              Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr := by
          rw [hShape, hHead, hFind]
          rfl
        rw [hEq]
        exact reInter_subsumed_right_eval_rel M
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
          b ra rb hATy hAEval hBEval hSub
    · have hEq :
          __eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply f r) rr) b =
            __eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply f r) rr) b := by
        rw [hShape, hHead]
        rfl
      rw [hEq]
      exact re_ac_merge_inter_l3_eval_rel M
        (Term.Apply (Term.Apply f r) rr) b ra rb hATy hBTy hAEval
        hBEval (by rwa [← hEq])
  · have hEq :
        __eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter) a b =
          __eo_l_3___re_ac_merge (Term.UOp UserOp.re_inter) a b := by
      cases a
      case Apply af rr =>
        cases af <;> cases b <;> simp_all [__eo_l_2___re_ac_merge]
      all_goals
        cases b <;> simp_all [__eo_l_2___re_ac_merge]
    rw [hEq]
    exact re_ac_merge_inter_l3_eval_rel M a b ra rb hATy hBTy hAEval
      hBEval (by rwa [← hEq])

private theorem re_ac_merge_inter_l1_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe :
      __eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter) a b ≠
        Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
  by_cases hBothShape :
      ∃ f r rr g s ss,
        a = Term.Apply (Term.Apply f r) rr ∧
          b = Term.Apply (Term.Apply g s) ss
  · rcases hBothShape with ⟨f, r, rr, g, s, ss, rfl, rfl⟩
    have hShape :
        __eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter)
            (Term.Apply (Term.Apply f r) rr)
            (Term.Apply (Term.Apply g s) ss) =
          __eo_ite
            (__eo_and (__eo_eq (Term.UOp UserOp.re_inter) f)
              (__eo_eq (Term.UOp UserOp.re_inter) g))
            (__eo_list_concat (Term.UOp UserOp.re_inter)
              (__eo_list_diff (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss))
            (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply f r) rr)
              (Term.Apply (Term.Apply g s) ss)) := by
      rfl
    have hTopNe :
        __eo_ite
            (__eo_and (__eo_eq (Term.UOp UserOp.re_inter) f)
              (__eo_eq (Term.UOp UserOp.re_inter) g))
            (__eo_list_concat (Term.UOp UserOp.re_inter)
              (__eo_list_diff (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss))
            (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply f r) rr)
              (Term.Apply (Term.Apply g s) ss)) ≠ Term.Stuck := by
      rwa [← hShape]
    rcases eo_ite_cases_of_ne_stuck
        (__eo_and (__eo_eq (Term.UOp UserOp.re_inter) f)
          (__eo_eq (Term.UOp UserOp.re_inter) g))
        (__eo_list_concat (Term.UOp UserOp.re_inter)
          (__eo_list_diff (Term.UOp UserOp.re_inter)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss))
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss))
        (__eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter)
          (Term.Apply (Term.Apply f r) rr)
          (Term.Apply (Term.Apply g s) ss))
        hTopNe with hHead | hHead
    · rcases eo_and_true_cases
          (__eo_eq (Term.UOp UserOp.re_inter) f)
          (__eo_eq (Term.UOp UserOp.re_inter) g) hHead with
        ⟨hF, hG⟩
      have hf : f = Term.UOp UserOp.re_inter :=
        eo_eq_re_inter_true f hF
      have hg : g = Term.UOp UserOp.re_inter :=
        eo_eq_re_inter_true g hG
      subst f
      subst g
      have hConcatNe :
          __eo_list_concat (Term.UOp UserOp.re_inter)
              (__eo_list_diff (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss) ≠
            Term.Stuck := by
        exact hTopNe
      rcases reInter_lists_of_concat_diff_inter_ne_stuck
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss)
          hConcatNe with ⟨hAList, hBList⟩
      have hEq :
          __eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss) =
            __eo_list_concat (Term.UOp UserOp.re_inter)
              (__eo_list_diff (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss) := by
        rw [hShape, hHead]
        rfl
      rw [hEq]
      exact reInter_concat_diff_inter_eval_rel M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) rr)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) s) ss)
        ra rb hAList hBList hATy hBTy hAEval hBEval
    · have hEq :
          __eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply f r) rr)
              (Term.Apply (Term.Apply g s) ss) =
            __eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.Apply (Term.Apply f r) rr)
              (Term.Apply (Term.Apply g s) ss) := by
        rw [hShape, hHead]
        rfl
      rw [hEq]
      exact re_ac_merge_inter_l2_eval_rel M
        (Term.Apply (Term.Apply f r) rr)
        (Term.Apply (Term.Apply g s) ss) ra rb hATy hBTy hAEval hBEval
        (by rwa [← hEq])
  · have hEq :
        __eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter) a b =
          __eo_l_2___re_ac_merge (Term.UOp UserOp.re_inter) a b := by
      cases a
      case Apply af arr =>
        cases af
        case Apply f r =>
          cases b
          case Apply bf brr =>
            cases bf <;> simp_all [__eo_l_1___re_ac_merge]
          all_goals
            simp_all [__eo_l_1___re_ac_merge]
        all_goals
          cases b <;> simp_all [__eo_l_1___re_ac_merge]
      all_goals
        cases b <;> simp_all [__eo_l_1___re_ac_merge]
    rw [hEq]
    exact re_ac_merge_inter_l2_eval_rel M a b ra rb hATy hBTy hAEval
      hBEval (by rwa [← hEq])

private theorem re_ac_merge_inter_self_eq (a : Term) :
    a ≠ Term.Stuck ->
    __re_ac_merge (Term.UOp UserOp.re_inter) a a = a := by
  intro hA
  have hEqTerm : __eo_eq a a = Term.Boolean true :=
    eo_eq_eq_true_of_eq_local rfl hA hA
  cases a <;> try
    simp [__re_ac_merge, hEqTerm, __eo_ite, native_ite, native_teq] at hA ⊢
  case UOp op =>
    cases op <;>
      simp [hEqTerm]

private theorem re_ac_merge_inter_none_left_eq (b : Term) :
    b ≠ Term.Stuck ->
    __re_ac_merge (Term.UOp UserOp.re_inter)
      (Term.UOp UserOp.re_none) b = Term.UOp UserOp.re_none := by
  intro hB
  cases b <;> simp [__re_ac_merge] at hB ⊢

private theorem re_ac_merge_inter_eq_l1
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    a ≠ Term.UOp UserOp.re_none ->
    a ≠ b ->
    __re_ac_merge (Term.UOp UserOp.re_inter) a b =
      __eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter) a b := by
  intro hA hB hNone hEq
  have hEqTerm :
      __eo_eq a b = Term.Boolean false :=
    eo_eq_eq_false_of_ne_local hEq hA hB
  have hShape :
      __re_ac_merge (Term.UOp UserOp.re_inter) a b =
        __eo_ite (__eo_eq a b) a
          (__eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter) a b) := by
    cases a <;> try simp_all
    case UOp op =>
      cases op <;> cases b <;> simp_all [__re_ac_merge]
    all_goals
      cases b <;> simp_all [__re_ac_merge]
  rw [hShape, hEqTerm]
  rfl

private theorem re_ac_merge_inter_none_left_eval_rel
    (M : SmtModel) (b : Term) (ra rb : SmtRegLan)
    (hAEval :
      __smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_none)) =
        SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.UOp UserOp.re_none) b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_ac_merge (Term.UOp UserOp.re_inter)
              (Term.UOp UserOp.re_none) b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  have hRa : ra = native_re_none := by
    have hAEval' : SmtValue.RegLan native_re_none = SmtValue.RegLan ra := by
      simpa [__smtx_model_eval] using hAEval
    cases hAEval'
    rfl
  have hMergeEq :
      __re_ac_merge (Term.UOp UserOp.re_inter)
        (Term.UOp UserOp.re_none) b = Term.UOp UserOp.re_none :=
    re_ac_merge_inter_none_left_eq b (regLanEval_ne_stuck ⟨rb, hBEval⟩)
  subst ra
  refine ⟨native_re_none, ?_, ?_, ?_⟩
  · rw [hMergeEq]
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_105]
  · rw [hMergeEq]
    change __smtx_typeof SmtTerm.re_none = SmtType.RegLan
    native_decide
  · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]
    intro str _hValid
    simp [native_str_in_re_mk_inter_sem,
      native_str_in_re_empty]

private theorem re_ac_merge_inter_self_eval_rel
    (M : SmtModel) (a : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_ac_merge (Term.UOp UserOp.re_inter) a a)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_ac_merge (Term.UOp UserOp.re_inter) a a)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  have hAStuck : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hMergeEq :
      __re_ac_merge (Term.UOp UserOp.re_inter) a a = a :=
    re_ac_merge_inter_self_eq a hAStuck
  have hRb : rb = ra := by
    rw [hAEval] at hBEval
    cases hBEval
    rfl
  subst rb
  refine ⟨ra, ?_, ?_, ?_⟩
  · rw [hMergeEq]
    exact hAEval
  · rw [hMergeEq]
    exact hATy
  · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_eq]
    intro str _hValid
    simp [native_str_in_re_mk_inter_sem]

private theorem re_ac_merge_inter_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe :
      __re_ac_merge (Term.UOp UserOp.re_inter) a b ≠ Term.Stuck) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt (__re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt (__re_ac_merge (Term.UOp UserOp.re_inter) a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_inter ra rb)) := by
  by_cases hNone : a = Term.UOp UserOp.re_none
  · subst a
    exact re_ac_merge_inter_none_left_eval_rel M b ra rb hAEval hBEval
  · by_cases hEq : a = b
    · subst b
      exact re_ac_merge_inter_self_eval_rel M a ra rb hATy hAEval hBEval
    · have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
      have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
      have hMergeEq :
          __re_ac_merge (Term.UOp UserOp.re_inter) a b =
            __eo_l_1___re_ac_merge (Term.UOp UserOp.re_inter) a b :=
        re_ac_merge_inter_eq_l1 a b hANe hBNe hNone hEq
      rw [hMergeEq]
      exact re_ac_merge_inter_l1_eval_rel M a b ra rb hATy hBTy hAEval
        hBEval (by rwa [← hMergeEq])

private theorem mkReConcat_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt (mkReConcat a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt (mkReConcat a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_concat ra rb)) := by
  refine ⟨native_re_concat ra rb, ?_, ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.RegLan (native_re_concat ra rb)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hAEval, hBEval]
  · exact reConcat_typeof_of_args a b hATy hBTy
  · exact RuleProofs.smt_value_rel_refl
      (SmtValue.RegLan (native_re_concat ra rb))

private theorem re_concat_merge_eval_rel
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hMergeNe : __re_concat_merge a b ≠ Term.Stuck) :
    ∃ r,
      __smtx_model_eval M (__eo_to_smt (__re_concat_merge a b)) =
        SmtValue.RegLan r ∧
      __smtx_typeof (__eo_to_smt (__re_concat_merge a b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_concat ra rb)) := by
  have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  have hBNe : b ≠ Term.Stuck := regLanEval_ne_stuck ⟨rb, hBEval⟩
  by_cases hBoth :
      ∃ ar arr br brr,
        a = mkReConcat ar arr ∧ b = mkReConcat br brr
  · rcases hBoth with ⟨ar, arr, br, brr, rfl, rfl⟩
    have hConcatNe :
        __eo_list_concat (Term.UOp UserOp.re_concat)
            (mkReConcat ar arr) (mkReConcat br brr) ≠ Term.Stuck := by
      simpa [__re_concat_merge, mkReConcat] using hMergeNe
    have hOuterReq :
        __eo_requires
            (__eo_is_list (Term.UOp UserOp.re_concat) (mkReConcat ar arr))
            (Term.Boolean true)
            (__eo_requires
              (__eo_is_list (Term.UOp UserOp.re_concat) (mkReConcat br brr))
              (Term.Boolean true)
              (__eo_list_concat_rec (mkReConcat ar arr)
                (mkReConcat br brr))) ≠ Term.Stuck := by
      simpa [__eo_list_concat] using hConcatNe
    have hAList :
        __eo_is_list (Term.UOp UserOp.re_concat) (mkReConcat ar arr) =
          Term.Boolean true :=
      eo_requires_eq_of_ne_stuck _ _ _ hOuterReq
    have hInnerNe :
        __eo_requires
              (__eo_is_list (Term.UOp UserOp.re_concat) (mkReConcat br brr))
              (Term.Boolean true)
              (__eo_list_concat_rec (mkReConcat ar arr)
                (mkReConcat br brr)) ≠ Term.Stuck :=
      eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hOuterReq
    have hBList :
        __eo_is_list (Term.UOp UserOp.re_concat) (mkReConcat br brr) =
          Term.Boolean true :=
      eo_requires_eq_of_ne_stuck _ _ _ hInnerNe
    exact reConcat_list_concat_eval_rel M (mkReConcat ar arr)
      (mkReConcat br brr) ra rb hAList hBList hATy hBTy hAEval hBEval
  · by_cases hNone : a = Term.UOp UserOp.re_none
    · subst a
      change __smtx_model_eval M SmtTerm.re_none =
        SmtValue.RegLan ra at hAEval
      rw [__smtx_model_eval.eq_105] at hAEval
      cases hAEval
      have hMergeEq :
          __re_concat_merge (Term.UOp UserOp.re_none) b =
            Term.UOp UserOp.re_none := by
        cases b <;> simp [__re_concat_merge] at hBNe ⊢
      refine ⟨native_re_none, ?_, ?_, ?_⟩
      · rw [hMergeEq]
        change __smtx_model_eval M SmtTerm.re_none =
          SmtValue.RegLan native_re_none
        rw [__smtx_model_eval.eq_105]
      · rw [hMergeEq]
        change __smtx_typeof SmtTerm.re_none = SmtType.RegLan
        native_decide
      · exact smt_value_rel_reglan_of_eq (by
          simp [native_re_concat, native_re_none])
    · by_cases hBConcat : ∃ br brr, b = mkReConcat br brr
      · rcases hBConcat with ⟨br, brr, rfl⟩
        have hMergeEq :
            __re_concat_merge a (mkReConcat br brr) =
              mkReConcat a (mkReConcat br brr) := by
          cases a <;> simp [__re_concat_merge, mkReConcat] at hANe hNone hBoth ⊢
          case Apply af ax =>
            cases af <;> simp  at hBoth ⊢
            case Apply aff ar =>
              cases aff <;> simp  at hBoth ⊢
              case UOp op =>
                cases op <;> simp  at hBoth ⊢
        rw [hMergeEq]
        exact mkReConcat_eval_rel M a (mkReConcat br brr) ra rb
          hATy hBTy hAEval hBEval
      · by_cases hAEps :
          a = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        · subst a
          change __smtx_model_eval M
              (SmtTerm.str_to_re (SmtTerm.String [])) =
            SmtValue.RegLan ra at hAEval
          simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
            ] at hAEval
          cases hAEval
          have hMergeEq :
              __re_concat_merge
                  (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
                  b = b := by
            cases b <;> simp [__re_concat_merge, mkReConcat] at hBNe hBConcat ⊢
            case Apply bf bx =>
              cases bf <;> simp  at hBConcat ⊢
              case Apply bff br =>
                cases bff <;> simp  at hBConcat ⊢
                case UOp op =>
                  cases op <;> simp  at hBConcat ⊢
          refine ⟨rb, ?_, ?_, ?_⟩
          · rw [hMergeEq]
            exact hBEval
          · rw [hMergeEq]
            exact hBTy
          · exact smt_value_rel_reglan_of_eq (by
              change rb = native_re_concat (native_str_to_re []) rb
              simpa [native_str_to_re, impl_native_re_of_list] using
                (native_re_mk_concat_left_epsilon rb).symm)
        · by_cases hBEps :
            b = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          · subst b
            change __smtx_model_eval M
                (SmtTerm.str_to_re (SmtTerm.String [])) =
              SmtValue.RegLan rb at hBEval
            simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
              ] at hBEval
            cases hBEval
            have hMergeEq :
                __re_concat_merge a
                    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
                  a := by
              cases a <;> simp [__re_concat_merge] at hANe hNone hAEps ⊢
            refine ⟨ra, ?_, ?_, ?_⟩
            · rw [hMergeEq]
              exact hAEval
            · rw [hMergeEq]
              exact hATy
            · exact smt_value_rel_reglan_of_eq (by
                change ra = native_re_concat ra (native_str_to_re [])
                simpa [native_str_to_re, impl_native_re_of_list] using
                  (native_re_mk_concat_right_epsilon ra).symm)
          · have hMergeEq :
                __re_concat_merge a b =
                  mkReConcat a
                    (mkReConcat b
                      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) := by
              cases b <;>
                simp [__re_concat_merge, mkReConcat] at hBNe hBConcat hBEps ⊢
              case Apply bf bx =>
                cases bf <;>
                  simp  at hBConcat hBEps ⊢
                case UOp op =>
                  cases op <;>
                    simp  at hBEps ⊢
                  case str_to_re =>
                    cases bx <;>
                      simp  at hBEps ⊢
                    case String s =>
                      cases s <;>
                        simp  at hBEps ⊢
                case Apply bff br =>
                  cases bff <;>
                    simp  at hBConcat ⊢
                  case UOp op =>
                    cases op <;>
                      simp  at hBConcat ⊢
              all_goals
                cases a <;>
                  simp [__re_concat_merge, mkReConcat] at hANe hNone hAEps ⊢
              all_goals
                try
                  rename_i af ax
                  cases af <;>
                    simp [__re_concat_merge, mkReConcat] at hAEps ⊢
              all_goals
                try
                  rename_i aff ar
                  cases aff <;>
                    simp [__re_concat_merge, mkReConcat] at hAEps ⊢
              all_goals
                try
                  rename_i op
                  cases op <;>
                    simp [__re_concat_merge, mkReConcat] at hAEps ⊢
            rw [hMergeEq]
            let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
            have hEpsEval :
                __smtx_model_eval M (__eo_to_smt eps) =
                  SmtValue.RegLan (native_str_to_re []) := by
              dsimp [eps]
              change __smtx_model_eval M
                  (SmtTerm.str_to_re (SmtTerm.String [])) =
                SmtValue.RegLan (native_str_to_re [])
              simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
                ]
            have hEpsTy :
                __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan := by
              dsimp [eps]
              change __smtx_typeof
                  (SmtTerm.str_to_re (SmtTerm.String [])) =
                SmtType.RegLan
              rw [typeof_str_to_re_eq, __smtx_typeof.eq_4]
              simp [native_string_valid, native_ite, native_Teq]
            have hBEpsConcatEval :
                __smtx_model_eval M (__eo_to_smt (mkReConcat b eps)) =
                  SmtValue.RegLan
                    (native_re_concat rb (native_str_to_re [])) := by
              change __smtx_model_eval M
                  (SmtTerm.re_concat (__eo_to_smt b) (__eo_to_smt eps)) =
                SmtValue.RegLan (native_re_concat rb (native_str_to_re []))
              simp [__smtx_model_eval, __smtx_model_eval_re_concat,
                hBEval, hEpsEval]
            refine ⟨native_re_concat ra
                (native_re_concat rb (native_str_to_re [])), ?_, ?_, ?_⟩
            · change __smtx_model_eval M
                  (SmtTerm.re_concat (__eo_to_smt a)
                    (SmtTerm.re_concat (__eo_to_smt b) (__eo_to_smt eps))) =
                SmtValue.RegLan
                  (native_re_concat ra
                    (native_re_concat rb (native_str_to_re [])))
              simp [__smtx_model_eval, __smtx_model_eval_re_concat,
                hAEval, hBEval, hEpsEval]
            · apply reConcat_typeof_of_args
              · exact hATy
              · exact reConcat_typeof_of_args b eps hBTy hEpsTy
            · have hAssoc :
                  RuleProofs.smt_value_rel
                    (SmtValue.RegLan
                      (native_re_concat ra
                        (native_re_concat rb (native_str_to_re []))))
                    (SmtValue.RegLan
                      (native_re_concat (native_re_concat ra rb)
                        (native_str_to_re []))) :=
                RuleProofs.smt_value_rel_symm _ _
                  (smt_value_rel_re_concat_assoc ra rb (native_str_to_re []))
              have hRight :
                  RuleProofs.smt_value_rel
                    (SmtValue.RegLan
                      (native_re_concat (native_re_concat ra rb)
                        (native_str_to_re [])))
                    (SmtValue.RegLan (native_re_concat ra rb)) :=
                smt_value_rel_reglan_of_eq (by
                  simpa [native_str_to_re, impl_native_re_of_list] using
                    native_re_mk_concat_right_epsilon
                      (native_re_concat ra rb))
              exact RuleProofs.smt_value_rel_trans _ _ _ hAssoc hRight

private theorem re_concat_merge_re_mult_default_eq
    (a x : Term)
    (hANe : a ≠ Term.Stuck)
    (hANone : a ≠ Term.UOp UserOp.re_none)
    (hAEps :
      a ≠ Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) :
    __re_concat_merge a (Term.Apply (Term.UOp UserOp.re_mult) x) =
      Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.UOp UserOp.re_mult) x))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) := by
  cases a <;> simp [__re_concat_merge] at hANe hANone hAEps ⊢

private theorem re_concat_merge_re_mult_eval_rel
    (M : SmtModel) (a x : Term) (ra rx : SmtRegLan)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hXEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan rx) :
    ∃ r,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_concat_merge a (Term.Apply (Term.UOp UserOp.re_mult) x))) =
        SmtValue.RegLan r ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_concat_merge a (Term.Apply (Term.UOp UserOp.re_mult) x))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r)
        (SmtValue.RegLan (native_re_concat ra (native_re_mult rx))) := by
  have hANe : a ≠ Term.Stuck := regLanEval_ne_stuck ⟨ra, hAEval⟩
  by_cases hNone : a = Term.UOp UserOp.re_none
  · subst a
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan ra at hAEval
    rw [__smtx_model_eval.eq_105] at hAEval
    cases hAEval
    refine ⟨native_re_none, ?_, ?_, ?_⟩
    · change __smtx_model_eval M SmtTerm.re_none =
        SmtValue.RegLan native_re_none
      rw [__smtx_model_eval.eq_105]
    · change __smtx_typeof SmtTerm.re_none = SmtType.RegLan
      native_decide
    · exact smt_value_rel_reglan_of_eq (by
        simp [native_re_concat, native_re_none])
  · by_cases hEps :
        a = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    · subst a
      change __smtx_model_eval M
          (SmtTerm.str_to_re (SmtTerm.String [])) =
        SmtValue.RegLan ra at hAEval
      simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
        ] at hAEval
      cases hAEval
      refine ⟨native_re_mult rx, ?_, ?_, ?_⟩
      · have hStarEval :
            __smtx_model_eval M
                (SmtTerm.re_mult (__eo_to_smt x)) =
              SmtValue.RegLan (native_re_mult rx) := by
          simp [__smtx_model_eval, __smtx_model_eval_re_mult, hXEval]
        exact hStarEval
      · have hStarTy :
            __smtx_typeof (SmtTerm.re_mult (__eo_to_smt x)) =
              SmtType.RegLan := by
          rw [typeof_re_mult_eq]
          simp [hXTy, native_ite, native_Teq]
        exact hStarTy
      · exact smt_value_rel_reglan_of_eq (by
          change native_re_mult rx =
            native_re_concat (native_str_to_re []) (native_re_mult rx)
          simpa [native_str_to_re, impl_native_re_of_list] using
            (native_re_mk_concat_left_epsilon (native_re_mult rx)).symm)
    · have hMergeEq :=
        re_concat_merge_re_mult_default_eq a x hANe hNone hEps
      rw [hMergeEq]
      refine ⟨native_re_concat ra (native_re_mult rx), ?_, ?_, ?_⟩
      · change __smtx_model_eval M
            (SmtTerm.re_concat (__eo_to_smt a)
              (SmtTerm.re_concat (SmtTerm.re_mult (__eo_to_smt x))
                (SmtTerm.str_to_re (SmtTerm.String [])))) =
          SmtValue.RegLan (native_re_concat ra (native_re_mult rx))
        simp [__smtx_model_eval, __smtx_model_eval_re_concat,
          __smtx_model_eval_re_mult, __smtx_model_eval_str_to_re,
          hAEval, hXEval,
          native_re_concat, native_str_to_re, impl_native_re_of_list]
        change native_re_mk_concat ra
            (native_re_mk_concat (native_re_mult rx) SmtRegLan.epsilon) =
          native_re_mk_concat ra (native_re_mult rx)
        rw [native_re_mk_concat_right_epsilon]
      · change __smtx_typeof
            (SmtTerm.re_concat (__eo_to_smt a)
              (SmtTerm.re_concat (SmtTerm.re_mult (__eo_to_smt x))
                (SmtTerm.str_to_re (SmtTerm.String [])))) =
          SmtType.RegLan
        rw [typeof_re_concat_eq, typeof_re_concat_eq, typeof_re_mult_eq,
          typeof_str_to_re_eq, __smtx_typeof.eq_4]
        simp [hATy, hXTy, native_ite, native_Teq, native_string_valid]
      · exact RuleProofs.smt_value_rel_refl
          (SmtValue.RegLan (native_re_concat ra (native_re_mult rx)))

private theorem smt_value_rel_re_comp
    {r s : SmtRegLan}
    (hRel : RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s)) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_comp r))
      (SmtValue.RegLan (native_re_comp s)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [native_str_in_re_re_comp, native_str_in_re_re_comp]
  rw [smt_value_rel_reglan_valid_eq hRel hValid]

private theorem native_string_valid_cons_of_parts
    {c : native_Char} {cs : native_String}
    (hc : native_char_valid c = true)
    (hcs : native_string_valid cs = true) :
    native_string_valid (c :: cs) = true := by
  change (native_char_valid c && native_string_valid cs) = true
  simp [hc, hcs]

private theorem smt_value_rel_deriv_comp
    (c : native_Char) (r : SmtRegLan)
    (hc : native_char_valid c = true) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_comp (native_re_deriv c r)))
      (SmtValue.RegLan (native_re_deriv c (native_re_comp r))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hCons : native_string_valid (c :: str) = true :=
    native_string_valid_cons_of_parts hc hValid
  calc
    native_str_in_re str (native_re_comp (native_re_deriv c r))
        = (native_string_valid str &&
            Bool.not (native_str_in_re str (native_re_deriv c r))) := by
          rw [native_str_in_re_re_comp]
    _ = Bool.not (native_str_in_re str (native_re_deriv c r)) := by
          simp [hValid]
    _ = Bool.not (native_str_in_re (c :: str) r) := by
          rw [native_str_in_re_cons hCons]
    _ = native_str_in_re (c :: str) (native_re_comp r) := by
          simpa [impl_native_string_to_values, hCons] using
            (native_str_in_re_re_comp (c :: str) r).symm
      _ = native_str_in_re str (native_re_deriv c (native_re_comp r)) := by
            rw [native_str_in_re_cons hCons]

private theorem native_str_in_re_re_concat_left_congr_valid
    (str : native_String) (r r' s : SmtRegLan)
    (hValid : native_string_valid str = true)
    (hRel : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r')) :
    native_str_in_re str (native_re_concat r s) =
      native_str_in_re str (native_re_concat r' s) := by
  simpa [native_str_in_re, hValid, native_re_concat, native_re_mk_concat,
    nativeListInRe] using
    nativeListInRe_mk_concat_congr_valid str r r' s s hValid
      (by
        intro ys hys
        simpa [native_str_in_re, hys, nativeListInRe] using
          smt_value_rel_reglan_valid_eq hRel hys)
      (by
        intro ys _hys
        rfl)

private theorem native_str_in_re_deriv_mult_raw
    (str : native_String) (c : native_Char) (r : SmtRegLan)
    (hValid : native_string_valid str = true) :
    native_str_in_re str
        (native_re_concat (native_re_deriv c r) (native_re_mult r)) =
      native_str_in_re str (native_re_deriv c (native_re_mult r)) := by
  cases r with
  | star r =>
      -- bridge to `nativeListInRe` explicitly: v4.33's `simp` drives the goal
      -- all the way to the fold form, which no longer matches the lemma.
      have hBridge : ∀ R, native_str_in_re str R = nativeListInRe str R := by
        intro R
        simp [native_str_in_re, hValid, nativeListInRe]
      rw [hBridge, hBridge]
      exact nativeListInRe_concat_star_absorb str (native_re_deriv c r) r
  | empty =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]
  | epsilon =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]
  | char d =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]
  | range lo hi =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]
  | allchar =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]
  | concat r s =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]
  | union r s =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]
  | inter r s =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]
  | comp r =>
      simp [native_str_in_re, hValid, native_re_concat, native_re_mult,
        native_re_deriv]

private theorem smt_value_rel_deriv_mult_of_rel
    (c : native_Char) (r d : SmtRegLan)
    (hRel : RuleProofs.smt_value_rel (SmtValue.RegLan d)
      (SmtValue.RegLan (native_re_deriv c r))) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat d (native_re_mult r)))
      (SmtValue.RegLan (native_re_deriv c (native_re_mult r))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  calc
    native_str_in_re str (native_re_concat d (native_re_mult r)) =
        native_str_in_re str
          (native_re_concat (native_re_deriv c r) (native_re_mult r)) := by
          exact native_str_in_re_re_concat_left_congr_valid str d
            (native_re_deriv c r) (native_re_mult r) hValid hRel
    _ = native_str_in_re str (native_re_deriv c (native_re_mult r)) := by
          exact native_str_in_re_deriv_mult_raw str c r hValid

private theorem smt_value_rel_deriv_concat_not_nullable
    (c : native_Char) (ry rx dy : SmtRegLan)
    (hNull : native_re_nullable ry = false)
    (hDy : RuleProofs.smt_value_rel (SmtValue.RegLan dy)
      (SmtValue.RegLan (native_re_deriv c ry))) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat dy rx))
      (SmtValue.RegLan (native_re_deriv c (native_re_concat ry rx))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hUnionEmpty :
      nativeListInRe str
          (native_re_mk_union
            (native_re_mk_concat (native_re_deriv c ry) rx)
            SmtRegLan.empty) =
        nativeListInRe str
          (native_re_mk_concat (native_re_deriv c ry) rx) := by
    rw [nativeListInRe_mk_union]
    simp [nativeListInRe_empty]
  calc
    native_str_in_re str (native_re_concat dy rx) =
        native_str_in_re str
          (native_re_concat (native_re_deriv c ry) rx) := by
          exact native_str_in_re_re_concat_left_congr_valid str dy
            (native_re_deriv c ry) rx hValid hDy
    _ = native_str_in_re str
        (native_re_deriv c (native_re_concat ry rx)) := by
          have hDeriv :
              nativeListInRe str
                  (native_re_mk_concat (native_re_deriv c ry) rx) =
                nativeListInRe str
                  (native_re_deriv c (native_re_mk_concat ry rx)) := by
            simpa [hNull, hUnionEmpty] using
              (nativeListInRe_deriv_mk_concat str c ry rx).symm
          have hBridge : ∀ R, native_str_in_re str R = nativeListInRe str R := by
            intro R
            simp [native_str_in_re, native_re_str_valid_string, hValid,
              nativeListInRe]
          simp only [hBridge]
          exact hDeriv

private theorem smt_value_rel_deriv_concat_nullable
    (c : native_Char) (ry rx dy dx : SmtRegLan)
    (hNull : native_re_nullable ry = true)
    (hDy : RuleProofs.smt_value_rel (SmtValue.RegLan dy)
      (SmtValue.RegLan (native_re_deriv c ry)))
    (hDx : RuleProofs.smt_value_rel (SmtValue.RegLan dx)
      (SmtValue.RegLan (native_re_deriv c rx))) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_union dx (native_re_concat dy rx)))
      (SmtValue.RegLan (native_re_deriv c (native_re_concat ry rx))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hConcat :
      native_str_in_re str (native_re_concat dy rx) =
        native_str_in_re str
          (native_re_concat (native_re_deriv c ry) rx) :=
    native_str_in_re_re_concat_left_congr_valid str dy
      (native_re_deriv c ry) rx hValid hDy
  calc
    native_str_in_re str (native_re_union dx (native_re_concat dy rx)) =
        (native_str_in_re str dx ||
          native_str_in_re str (native_re_concat dy rx)) := by
          simp [native_str_in_re_mk_union_sem]
    _ =
        (native_str_in_re str (native_re_deriv c rx) ||
          native_str_in_re str
            (native_re_concat (native_re_deriv c ry) rx)) := by
          rw [smt_value_rel_reglan_valid_eq hDx hValid, hConcat]
    _ =
        (native_str_in_re str
            (native_re_concat (native_re_deriv c ry) rx) ||
          native_str_in_re str (native_re_deriv c rx)) := by
          simp [Bool.or_comm]
    _ = native_str_in_re str
        (native_re_deriv c (native_re_concat ry rx)) := by
          have hDeriv :
              nativeListInRe str
                  (native_re_mk_union
                    (native_re_mk_concat (native_re_deriv c ry) rx)
                    (native_re_deriv c rx)) =
                nativeListInRe str
                  (native_re_deriv c (native_re_mk_concat ry rx)) := by
            simpa [hNull] using
              (nativeListInRe_deriv_mk_concat str c ry rx).symm
          have hUnion :
              nativeListInRe str
                  (native_re_mk_union
                    (native_re_mk_concat (native_re_deriv c ry) rx)
                    (native_re_deriv c rx)) =
                (nativeListInRe str
                    (native_re_mk_concat (native_re_deriv c ry) rx) ||
                  nativeListInRe str (native_re_deriv c rx)) :=
            nativeListInRe_mk_union str
              (native_re_mk_concat (native_re_deriv c ry) rx)
              (native_re_deriv c rx)
          rw [hUnion] at hDeriv
          have hBridge : ∀ R, native_str_in_re str R = nativeListInRe str R := by
            intro R
            simp [native_str_in_re, native_re_str_valid_string, hValid,
              nativeListInRe]
          simp only [hBridge]
          exact hDeriv

private theorem native_re_deriv_all_valid
    (c : native_Char) (hc : native_char_valid c = true) :
    native_re_deriv c native_re_all = native_re_all := by
  exact native_re_deriv_re_all_valid_local c hc

private theorem native_re_deriv_allchar_valid
    (c : native_Char) (hc : native_char_valid c = true) :
    native_re_deriv c native_re_allchar = native_str_to_re [] := by
  simp [native_re_allchar, native_str_to_re, impl_native_re_of_list,
    native_re_deriv, native_re_elem_valid, hc]

private theorem native_re_deriv_str_to_re_cons_valid
    (c d : native_Char) (ds : native_String)
    (hc : native_char_valid c = true) :
    native_re_deriv c (native_str_to_re (d :: ds)) =
      if d = c then native_str_to_re ds else native_re_none := by
  cases ds with
  | nil =>
      by_cases hdc : d = c
      · subst d
        simp [impl_native_string_to_values, native_str_to_re, impl_native_re_of_list,
          native_re_concat, native_re_deriv]
      · have hNe : ¬ (c = d) := by
          intro h
          exact hdc h.symm
        simp [impl_native_string_to_values, native_str_to_re, impl_native_re_of_list,
          native_re_concat, native_re_deriv,
          native_re_none, hdc, hNe]
  | cons e es =>
      have hTail := native_re_of_list_cons_ne_empty_and_epsilon e es
      have hConcat :
          native_re_mk_concat (SmtRegLan.char d)
              (impl_native_re_of_list (e :: es)) =
            SmtRegLan.concat (SmtRegLan.char d)
              (impl_native_re_of_list (e :: es)) := by
        simp [native_re_mk_concat, native_re_concat, hTail.1, hTail.2]
      by_cases hdc : d = c
      · subst d
        simp only
        change
          native_re_deriv c
              (native_re_mk_concat (SmtRegLan.char c)
                (impl_native_re_of_list (e :: es))) =
            native_str_to_re (e :: es)
        rw [hConcat]
        simp only [native_str_to_re, native_re_deriv,
          native_re_nullable]
        simp
        rw [show native_re_concat SmtRegLan.epsilon
            (impl_native_re_of_list (e :: es)) = impl_native_re_of_list (e :: es) by
              exact native_re_mk_concat_left_epsilon _]
        exact native_re_mk_union_right_empty _
      · have hNe : ¬ (c = d) := by
          intro h
          exact hdc h.symm
        simp only [if_neg hdc]
        change
          native_re_deriv c
              (native_re_mk_concat (SmtRegLan.char d)
                (impl_native_re_of_list (e :: es))) =
            native_re_none
        rw [hConcat]
        simp only [native_re_deriv,
          native_re_nullable, native_re_none]
        simp
        simp only [if_neg hNe]
        rw [show native_re_concat SmtRegLan.empty
            (impl_native_re_of_list (e :: es)) = SmtRegLan.empty by
              exact native_re_mk_concat_left_empty _]
        exact native_re_mk_union_right_empty _

@[simp] private theorem native_zeq_one_str_len_nil :
    native_zeq 1 (native_str_len ([] : native_String)) = false := by
  native_decide

@[simp] private theorem native_zeq_one_str_len_single (c : native_Char) :
    native_zeq 1 (native_str_len [c]) = true := by
  simp [native_zeq, native_str_len]

@[simp] private theorem native_zeq_one_str_len_cons_cons
    (c d : native_Char) (ds : native_String) :
    native_zeq 1 (native_str_len (c :: d :: ds)) = false := by
  unfold native_zeq native_str_len
  simp
  intro h
  have hNat : (1 : Nat) = ds.length + 1 + 1 := by
    exact Int.ofNat.inj (by simpa [Int.natCast_add] using h)
  generalize hn : ds.length = n at hNat
  cases n <;> simp at hNat

private theorem str_to_re_derivative_arg_cases
    (c : native_Char) (x : Term) :
    __derivative (Term.String [c])
        (Term.Apply (Term.UOp UserOp.str_to_re) x) ≠ Term.Stuck ->
      (∃ s : native_String, x = Term.String s) ∨
        (∃ w n : native_Int, x = Term.Binary w n) := by
  intro hDerNe
  cases x <;>
    simp [__derivative, __eo_extract, __eo_eq, __eo_len, __eo_add,
      __eo_mk_apply, native_ite, native_teq] at hDerNe ⊢

private theorem seq_char_to_z_ne_stuck_singleton
    (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hZ : __eo_to_z t ≠ Term.Stuck) :
    ∃ c : native_Char, t = Term.String [c] := by
  cases t <;>
    simp [__eo_to_z, __smtx_typeof, native_ite, native_str_to_code] at hTy hZ ⊢
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral n) =
      SmtType.Seq SmtType.Char at hTy
    simp [__smtx_typeof] at hTy
  case Rational r =>
    change __smtx_typeof (SmtTerm.Rational r) =
      SmtType.Seq SmtType.Char at hTy
    simp [__smtx_typeof] at hTy
  case Binary w n =>
    change __smtx_typeof (SmtTerm.Binary w n) =
      SmtType.Seq SmtType.Char at hTy
    simp [__smtx_typeof] at hTy
    cases hCond :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hCond] at hTy
  case String s =>
    cases s with
    | nil =>
        simp  at hZ
    | cons c s =>
        cases s with
        | nil =>
            exact ⟨c, rfl⟩
        | cons d ds =>
            simp  at hZ

private theorem re_range_derivative_left_to_z_ne_stuck
    (c : native_Char) (y x : Term)
    (hDerNe :
      __derivative (Term.String [c])
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) y) x) ≠
        Term.Stuck) :
    __eo_to_z y ≠ Term.Stuck := by
  intro hY
  apply hDerNe
  have hCz :
      ∃ z : native_Int, __eo_to_z (Term.String [c]) = Term.Numeral z := by
    refine ⟨native_str_to_code [c], ?_⟩
    simp [__eo_to_z, native_str_to_code, native_ite]
  rcases hCz with ⟨z, hCz⟩
  simp [__derivative, hY, hCz, __eo_eq, __eo_gt, __eo_and,
    __eo_ite, native_ite, native_teq]

private theorem re_range_derivative_right_to_z_ne_stuck
    (c : native_Char) (y x : Term)
    (hDerNe :
      __derivative (Term.String [c])
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) y) x) ≠
        Term.Stuck) :
    __eo_to_z x ≠ Term.Stuck := by
  intro hX
  apply hDerNe
  have hCz :
      ∃ z : native_Int, __eo_to_z (Term.String [c]) = Term.Numeral z := by
    refine ⟨native_str_to_code [c], ?_⟩
    simp [__eo_to_z, native_str_to_code, native_ite]
  rcases hCz with ⟨z, hCz⟩
  simp [__derivative, hX, hCz, __eo_eq, __eo_gt, __eo_and,
    __eo_ite, native_ite, native_teq]

private theorem re_range_derivative_arg_singletons
    (c : native_Char) (y x : Term)
    (hc : native_char_valid c = true)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) y) x)) =
        SmtType.RegLan)
    (hDerNe :
      __derivative (Term.String [c])
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) y) x) ≠
        Term.Stuck) :
    ∃ lo hi : native_Char, y = Term.String [lo] ∧ x = Term.String [hi] := by
  have hArgs :=
    seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
      (typeof_re_range_eq (__eo_to_smt y) (__eo_to_smt x)) (by
        unfold term_has_non_none_type
        change __smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) y) x)) ≠
          SmtType.None
        rw [hTy]
        simp)
  have hYz := re_range_derivative_left_to_z_ne_stuck c y x hDerNe
  have hXz := re_range_derivative_right_to_z_ne_stuck c y x hDerNe
  rcases seq_char_to_z_ne_stuck_singleton y hArgs.1 hYz with ⟨lo, rfl⟩
  rcases seq_char_to_z_ne_stuck_singleton x hArgs.2 hXz with ⟨hi, rfl⟩
  exact ⟨lo, hi, rfl, rfl⟩

private theorem re_range_lower_cond_true
    (c lo : native_Char) (h : lo ≤ c) :
    __eo_ite (__eo_eq (Term.Numeral (Int.ofNat c))
          (Term.Numeral (Int.ofNat lo)))
        (Term.Boolean true)
        (__eo_gt (Term.Numeral (Int.ofNat c))
          (Term.Numeral (Int.ofNat lo))) =
      Term.Boolean true := by
  rcases Nat.eq_or_lt_of_le h with hEq | hLt
  · subst c
    simp [__eo_eq, __eo_ite, native_ite, native_teq]
  · have hNe : ¬ lo = c := Nat.ne_of_lt hLt
    have hNeInt : ¬ Int.ofNat lo = Int.ofNat c := by
      intro hEq
      exact hNe (Int.ofNat.inj hEq)
    have hLtInt : native_zlt (Int.ofNat lo) (Int.ofNat c) = true := by
      simp [native_zlt, Int.ofNat_lt, hLt]
    have hEqFalse :
        __eo_eq (Term.Numeral (Int.ofNat c))
            (Term.Numeral (Int.ofNat lo)) =
          Term.Boolean false := by
      simp [__eo_eq, native_teq]
      exact hNeInt
    rw [hEqFalse]
    change Term.Boolean (native_zlt (Int.ofNat lo) (Int.ofNat c)) =
      Term.Boolean true
    rw [hLtInt]

private theorem re_range_lower_cond_false
    (c lo : native_Char) (h : ¬ lo ≤ c) :
    __eo_ite (__eo_eq (Term.Numeral (Int.ofNat c))
          (Term.Numeral (Int.ofNat lo)))
        (Term.Boolean true)
        (__eo_gt (Term.Numeral (Int.ofNat c))
          (Term.Numeral (Int.ofNat lo))) =
      Term.Boolean false := by
  have hNe : ¬ lo = c := by
    intro hEq
    subst c
    exact h (Nat.le_refl _)
  have hNeInt : ¬ Int.ofNat lo = Int.ofNat c := by
    intro hEq
    exact hNe (Int.ofNat.inj hEq)
  have hNotLt : ¬ lo < c := by
    intro hLt
    exact h (Nat.le_of_lt hLt)
  have hLtInt : native_zlt (Int.ofNat lo) (Int.ofNat c) = false := by
    simp [native_zlt, Int.ofNat_lt, hNotLt]
  have hEqFalse :
      __eo_eq (Term.Numeral (Int.ofNat c))
          (Term.Numeral (Int.ofNat lo)) =
        Term.Boolean false := by
    simp [__eo_eq, native_teq]
    exact hNeInt
  rw [hEqFalse]
  change Term.Boolean (native_zlt (Int.ofNat lo) (Int.ofNat c)) =
    Term.Boolean false
  rw [hLtInt]

private theorem re_range_upper_cond_true
    (c hi : native_Char) (h : c ≤ hi) :
    __eo_ite (__eo_eq (Term.Numeral (Int.ofNat hi))
          (Term.Numeral (Int.ofNat c)))
        (Term.Boolean true)
        (__eo_gt (Term.Numeral (Int.ofNat hi))
          (Term.Numeral (Int.ofNat c))) =
      Term.Boolean true := by
  rcases Nat.eq_or_lt_of_le h with hEq | hLt
  · subst hi
    simp [__eo_eq, __eo_ite, native_ite, native_teq]
  · have hNe : ¬ c = hi := Nat.ne_of_lt hLt
    have hNeInt : ¬ Int.ofNat c = Int.ofNat hi := by
      intro hEq
      exact hNe (Int.ofNat.inj hEq)
    have hLtInt : native_zlt (Int.ofNat c) (Int.ofNat hi) = true := by
      simp [native_zlt, Int.ofNat_lt, hLt]
    have hEqFalse :
        __eo_eq (Term.Numeral (Int.ofNat hi))
            (Term.Numeral (Int.ofNat c)) =
          Term.Boolean false := by
      simp [__eo_eq, native_teq]
      exact hNeInt
    rw [hEqFalse]
    change Term.Boolean (native_zlt (Int.ofNat c) (Int.ofNat hi)) =
      Term.Boolean true
    rw [hLtInt]

private theorem re_range_upper_cond_false
    (c hi : native_Char) (h : ¬ c ≤ hi) :
    __eo_ite (__eo_eq (Term.Numeral (Int.ofNat hi))
          (Term.Numeral (Int.ofNat c)))
        (Term.Boolean true)
        (__eo_gt (Term.Numeral (Int.ofNat hi))
          (Term.Numeral (Int.ofNat c))) =
      Term.Boolean false := by
  have hNe : ¬ c = hi := by
    intro hEq
    subst hi
    exact h (Nat.le_refl _)
  have hNeInt : ¬ Int.ofNat c = Int.ofNat hi := by
    intro hEq
    exact hNe (Int.ofNat.inj hEq)
  have hNotLt : ¬ c < hi := by
    intro hLt
    exact h (Nat.le_of_lt hLt)
  have hLtInt : native_zlt (Int.ofNat c) (Int.ofNat hi) = false := by
    simp [native_zlt, Int.ofNat_lt, hNotLt]
  have hEqFalse :
      __eo_eq (Term.Numeral (Int.ofNat hi))
          (Term.Numeral (Int.ofNat c)) =
        Term.Boolean false := by
    simp [__eo_eq, native_teq]
    exact hNeInt
  rw [hEqFalse]
  change Term.Boolean (native_zlt (Int.ofNat c) (Int.ofNat hi)) =
    Term.Boolean false
  rw [hLtInt]

private theorem re_range_derivative_singletons_eq
    (c lo hi : native_Char)
    (hc : native_char_valid c = true)
    (hloValid : native_char_valid lo = true)
    (hhiValid : native_char_valid hi = true)
    (bLo bHi : native_Bool)
    (hLower :
      __eo_ite (__eo_eq (Term.Numeral (Int.ofNat c))
            (Term.Numeral (Int.ofNat lo)))
          (Term.Boolean true)
          (__eo_gt (Term.Numeral (Int.ofNat c))
            (Term.Numeral (Int.ofNat lo))) =
        Term.Boolean bLo)
    (hUpper :
      __eo_ite (__eo_eq (Term.Numeral (Int.ofNat hi))
            (Term.Numeral (Int.ofNat c)))
          (Term.Boolean true)
          (__eo_gt (Term.Numeral (Int.ofNat hi))
            (Term.Numeral (Int.ofNat c))) =
        Term.Boolean bHi) :
    __derivative (Term.String [c])
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_range) (Term.String [lo]))
          (Term.String [hi])) =
      if native_and bLo bHi then
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      else
        Term.UOp UserOp.re_none := by
  have hcZ :
      __eo_to_z (Term.String [c]) = Term.Numeral (Int.ofNat c) := by
    simp [__eo_to_z, native_str_to_code, native_ite, hc]
  have hloZ :
      __eo_to_z (Term.String [lo]) = Term.Numeral (Int.ofNat lo) := by
    simp [__eo_to_z, native_str_to_code, native_ite, hloValid]
  have hhiZ :
      __eo_to_z (Term.String [hi]) = Term.Numeral (Int.ofNat hi) := by
    simp [__eo_to_z, native_str_to_code, native_ite, hhiValid]
  simp only [__derivative]
  rw [hcZ, hloZ, hhiZ, hLower, hUpper]
  cases bLo <;> cases bHi <;>
    simp [__eo_and, __eo_ite, native_ite, native_teq,
      SmtEval.native_and]

theorem smtx_model_eval_derivative_single_rel
    (M : SmtModel) (hM : model_wf M) (c : native_Char)
    (hc : native_char_valid c = true) :
    (r : Term) -> (rv : SmtRegLan) ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __derivative (Term.String [c]) r ≠ Term.Stuck ->
      ∃ drv : SmtRegLan,
        __smtx_model_eval M
            (__eo_to_smt (__derivative (Term.String [c]) r)) =
          SmtValue.RegLan drv ∧
        __smtx_typeof (__eo_to_smt (__derivative (Term.String [c]) r)) =
          SmtType.RegLan ∧
        RuleProofs.smt_value_rel (SmtValue.RegLan drv)
          (SmtValue.RegLan (native_re_deriv c rv))
  | Term.UOp op, rv, _hRTy, hREval, hDerNe => by
      cases op <;>
        simp [__derivative] at hDerNe hREval ⊢
      case re_allchar =>
        change __smtx_model_eval M SmtTerm.re_allchar =
          SmtValue.RegLan rv at hREval
        rw [__smtx_model_eval.eq_104] at hREval
        cases hREval
        refine ⟨native_str_to_re [], ?_, ?_, ?_⟩
        · change __smtx_model_eval M
              (SmtTerm.str_to_re (SmtTerm.String [])) =
            SmtValue.RegLan (native_str_to_re [])
          simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
            ]
        · native_decide
        · exact smt_value_rel_reglan_of_eq
            (native_re_deriv_allchar_valid c hc).symm
      case re_none =>
        change __smtx_model_eval M SmtTerm.re_none =
          SmtValue.RegLan rv at hREval
        rw [__smtx_model_eval.eq_105] at hREval
        cases hREval
        refine ⟨native_re_none, ?_, ?_, ?_⟩
        · simp [__smtx_model_eval]
        · native_decide
        · exact smt_value_rel_reglan_of_eq (by
            simp [native_re_none, native_re_deriv])
      case re_all =>
        change __smtx_model_eval M SmtTerm.re_all =
          SmtValue.RegLan rv at hREval
        rw [__smtx_model_eval.eq_106] at hREval
        cases hREval
        refine ⟨native_re_all, ?_, ?_, ?_⟩
        · simp [__smtx_model_eval]
        · native_decide
        · exact smt_value_rel_reglan_of_eq
            (native_re_deriv_all_valid c hc).symm
  | Term.Apply f x, rv, hRTy, hREval, hDerNe => by
      cases f <;> try simp [__derivative] at hDerNe
      case UOp op =>
        cases op <;> try simp [__derivative] at hDerNe hREval ⊢
        case re_comp =>
          have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan := by
            change __smtx_typeof (SmtTerm.re_comp (__eo_to_smt x)) =
              SmtType.RegLan at hRTy
            exact reglan_arg_of_non_none (op := SmtTerm.re_comp)
              (typeof_re_comp_eq (__eo_to_smt x)) (by
                unfold term_has_non_none_type
                rw [hRTy]
                simp)
          have hDerXNe : __derivative (Term.String [c]) x ≠ Term.Stuck := by
            intro hDer
            rw [hDer] at hDerNe
            simp [__eo_mk_apply] at hDerNe
          change __smtx_model_eval M
              (SmtTerm.re_comp (__eo_to_smt x)) =
            SmtValue.RegLan rv at hREval
          cases hX : __smtx_model_eval M (__eo_to_smt x) <;>
            simp [__smtx_model_eval, __smtx_model_eval_re_comp, hX] at hREval
          case RegLan rx =>
            cases hREval
            rcases
              smtx_model_eval_derivative_single_rel M hM c hc x rx hXTy hX
                hDerXNe with
              ⟨drv, hDrvEval, hDrvTy, hDrvRel⟩
            refine ⟨native_re_comp drv, ?_, ?_, ?_⟩
            · have hMk :
                  __eo_mk_apply (Term.UOp UserOp.re_comp)
                      (__derivative (Term.String [c]) x) =
                    Term.Apply (Term.UOp UserOp.re_comp)
                      (__derivative (Term.String [c]) x) := by
                simp [__eo_mk_apply]
              rw [hMk]
              change __smtx_model_eval M
                    (SmtTerm.re_comp
                      (__eo_to_smt (__derivative (Term.String [c]) x))) =
                  SmtValue.RegLan (native_re_comp drv)
              simp [__smtx_model_eval, __smtx_model_eval_re_comp, hDrvEval]
            · have hMk :
                  __eo_mk_apply (Term.UOp UserOp.re_comp)
                      (__derivative (Term.String [c]) x) =
                    Term.Apply (Term.UOp UserOp.re_comp)
                      (__derivative (Term.String [c]) x) := by
                simp [__eo_mk_apply]
              rw [hMk]
              change __smtx_typeof
                    (SmtTerm.re_comp
                      (__eo_to_smt (__derivative (Term.String [c]) x))) =
                  SmtType.RegLan
              rw [typeof_re_comp_eq]
              simp [hDrvTy, native_ite, native_Teq]
            · exact RuleProofs.smt_value_rel_trans
                (SmtValue.RegLan (native_re_comp drv))
                (SmtValue.RegLan (native_re_comp (native_re_deriv c rx)))
                (SmtValue.RegLan
                  (native_re_deriv c (native_re_comp rx)))
                (smt_value_rel_re_comp hDrvRel)
                (smt_value_rel_deriv_comp c rx hc)
        case str_to_re =>
          rcases str_to_re_derivative_arg_cases c x hDerNe with
            ⟨str, rfl⟩ | ⟨w, n, rfl⟩
          ·
            cases str with
            | nil =>
                change __smtx_model_eval M
                    (SmtTerm.str_to_re (SmtTerm.String [])) =
                  SmtValue.RegLan rv at hREval
                simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
                  ] at hREval
                cases hREval
                refine ⟨native_re_none, ?_, ?_, ?_⟩
                · simp [__derivative, __smtx_model_eval]
                · have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String [])) =
                        Term.UOp UserOp.re_none := by
                    simp [__derivative]
                  simpa [hDerEq] using
                    (by native_decide :
                      __smtx_typeof
                          (__eo_to_smt (Term.UOp UserOp.re_none)) =
                        SmtType.RegLan)
                · exact smt_value_rel_reglan_of_eq (by
                    simp [native_re_none, native_str_to_re, impl_native_re_of_list,
                      native_re_deriv])
            | cons d ds =>
                have hArgTy :
                    __smtx_typeof (SmtTerm.String (d :: ds)) =
                      SmtType.Seq SmtType.Char := by
                  change __smtx_typeof
                      (SmtTerm.str_to_re (SmtTerm.String (d :: ds))) =
                    SmtType.RegLan at hRTy
                  exact seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
                    (typeof_str_to_re_eq (SmtTerm.String (d :: ds))) (by
                      unfold term_has_non_none_type
                      rw [hRTy]
                      simp)
                have hArgValid :
                    native_string_valid (d :: ds) = true :=
                  native_string_valid_of_smtx_typeof_eo_string (d :: ds)
                    (by exact hArgTy)
                have hDsValid : native_string_valid ds = true :=
                  (native_string_valid_cons_parts hArgValid).2
                change __smtx_model_eval M
                    (SmtTerm.str_to_re (SmtTerm.String (d :: ds))) =
                  SmtValue.RegLan rv at hREval
                simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
                  ] at hREval
                cases hREval
                by_cases hdc : d = c
                · subst d
                  refine ⟨native_str_to_re ds, ?_, ?_, ?_⟩
                  · have hDerEq :
                        __derivative (Term.String [c])
                            (Term.Apply (Term.UOp UserOp.str_to_re)
                              (Term.String (c :: ds))) =
                          Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String ds) := by
                      simp [__derivative, eo_extract_zero_zero_cons,
                        eo_extract_tail_cons, __eo_eq, native_teq, native_ite, __eo_mk_apply]
                    have hEval :
                        __smtx_model_eval M
                            (__eo_to_smt
                              (Term.Apply (Term.UOp UserOp.str_to_re)
                                (Term.String ds))) =
                          SmtValue.RegLan (native_str_to_re ds) := by
                      change __smtx_model_eval M
                          (SmtTerm.str_to_re (SmtTerm.String ds)) =
                        SmtValue.RegLan (native_str_to_re ds)
                      simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
                        ]
                    simpa [hDerEq] using hEval
                  · have hDerEq :
                        __derivative (Term.String [c])
                            (Term.Apply (Term.UOp UserOp.str_to_re)
                              (Term.String (c :: ds))) =
                          Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String ds) := by
                      simp [__derivative, eo_extract_zero_zero_cons,
                        eo_extract_tail_cons, __eo_eq, native_teq, native_ite, __eo_mk_apply]
                    have hTy :
                        __smtx_typeof
                            (__eo_to_smt
                              (Term.Apply (Term.UOp UserOp.str_to_re)
                                (Term.String ds))) =
                          SmtType.RegLan := by
                      have hDsTy :
                          __smtx_typeof (SmtTerm.String ds) =
                            SmtType.Seq SmtType.Char := by
                        rw [__smtx_typeof.eq_4]
                        simp [hDsValid, native_ite]
                      change __smtx_typeof
                          (SmtTerm.str_to_re (SmtTerm.String ds)) =
                        SmtType.RegLan
                      rw [typeof_str_to_re_eq]
                      simp [hDsTy, native_ite, native_Teq]
                    simpa [hDerEq] using hTy
                  · exact smt_value_rel_reglan_of_eq (by
                      rw [native_re_deriv_str_to_re_cons_valid c c ds hc]
                      simp )
                · refine ⟨native_re_none, ?_, ?_, ?_⟩
                  · have hNe : ¬ c = d := by
                      intro h
                      exact hdc h.symm
                    have hDerEq :
                        __derivative (Term.String [c])
                            (Term.Apply (Term.UOp UserOp.str_to_re)
                              (Term.String (d :: ds))) =
                          Term.UOp UserOp.re_none := by
                      simp [__derivative, eo_extract_zero_zero_cons,
                        eo_extract_tail_cons, __eo_eq, native_teq, hNe, native_ite]
                    have hEval :
                        __smtx_model_eval M
                        (__eo_to_smt (Term.UOp UserOp.re_none)) =
                          SmtValue.RegLan native_re_none := by
                      simp [__smtx_model_eval]
                    simpa [hDerEq] using hEval
                  · have hNe : ¬ c = d := by
                      intro h
                      exact hdc h.symm
                    have hDerEq :
                        __derivative (Term.String [c])
                            (Term.Apply (Term.UOp UserOp.str_to_re)
                              (Term.String (d :: ds))) =
                          Term.UOp UserOp.re_none := by
                      simp [__derivative, eo_extract_zero_zero_cons,
                        eo_extract_tail_cons, __eo_eq, native_teq, hNe, native_ite]
                    simpa [hDerEq] using
                      (by native_decide :
                        __smtx_typeof (__eo_to_smt (Term.UOp UserOp.re_none)) =
                          SmtType.RegLan)
                  · exact smt_value_rel_reglan_of_eq (by
                      rw [native_re_deriv_str_to_re_cons_valid c d ds hc]
                      simp [hdc, native_re_none])
          · change __smtx_model_eval M
                (SmtTerm.str_to_re (SmtTerm.Binary w n)) =
              SmtValue.RegLan rv at hREval
            simp [__smtx_model_eval, __smtx_model_eval_str_to_re] at hREval
        case re_mult =>
          have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan := by
            change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt x)) =
              SmtType.RegLan at hRTy
            exact reglan_arg_of_non_none (op := SmtTerm.re_mult)
              (typeof_re_mult_eq (__eo_to_smt x)) (by
                unfold term_has_non_none_type
                rw [hRTy]
                simp)
          have hDerXNe :
              __derivative (Term.String [c]) x ≠ Term.Stuck := by
            intro hDer
            apply hDerNe
            simp [hDer, __re_concat_merge]
          change __smtx_model_eval M
              (SmtTerm.re_mult (__eo_to_smt x)) =
            SmtValue.RegLan rv at hREval
          cases hXEval : __smtx_model_eval M (__eo_to_smt x) <;>
            simp [__smtx_model_eval, __smtx_model_eval_re_mult,
              hXEval] at hREval
          case RegLan rx =>
            cases hREval
            rcases
              smtx_model_eval_derivative_single_rel M hM c hc x rx hXTy
                hXEval hDerXNe with
              ⟨dx, hDxEval, hDxTy, hDxRel⟩
            rcases
              re_concat_merge_re_mult_eval_rel M
                (__derivative (Term.String [c]) x) x dx rx
                hDxTy hXTy hDxEval hXEval with
              ⟨drv, hDrvEval, hDrvTy, hMergeRel⟩
            refine ⟨drv, ?_, ?_, ?_⟩
            · simpa [__derivative] using hDrvEval
            · simpa [__derivative] using hDrvTy
            · exact RuleProofs.smt_value_rel_trans
                (SmtValue.RegLan drv)
                (SmtValue.RegLan (native_re_concat dx (native_re_mult rx)))
                (SmtValue.RegLan (native_re_deriv c (native_re_mult rx)))
                hMergeRel
                (smt_value_rel_deriv_mult_of_rel c rx dx hDxRel)
      case Apply g y =>
        cases g <;> try simp [__derivative] at hDerNe
        case UOp op =>
          cases op <;> try simp [__derivative] at hDerNe hREval ⊢
          case re_union =>
            have hArgs :=
              reglan_binop_args_of_non_none (op := SmtTerm.re_union)
                (typeof_re_union_eq (__eo_to_smt y) (__eo_to_smt x)) (by
                  unfold term_has_non_none_type
                  change __smtx_typeof
                      (__eo_to_smt
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.re_union) y) x)) ≠
                    SmtType.None
                  rw [hRTy]
                  exact smt_reglan_ne_none)
            change __smtx_model_eval M
                (SmtTerm.re_union (__eo_to_smt y) (__eo_to_smt x)) =
              SmtValue.RegLan rv at hREval
            cases hyEval : __smtx_model_eval M (__eo_to_smt y) <;>
              cases hxEval : __smtx_model_eval M (__eo_to_smt x) <;>
                simp [__smtx_model_eval, __smtx_model_eval_re_union,
                  hyEval, hxEval] at hREval
            case RegLan.RegLan ry rx =>
              cases hREval
              have hDerYNe :
                  __derivative (Term.String [c]) y ≠ Term.Stuck := by
                intro hDerY
                apply hDerNe
                simp [hDerY, __re_ac_merge]
              have hDerXNe :
                  __derivative (Term.String [c]) x ≠ Term.Stuck := by
                intro hDerX
                apply hDerNe
                cases hDerY : __derivative (Term.String [c]) y <;>
                  simp [hDerX, __re_ac_merge]
              rcases
                smtx_model_eval_derivative_single_rel M hM c hc y ry
                  hArgs.1 hyEval hDerYNe with
                ⟨dy, hDyEval, hDyTy, hDyRel⟩
              rcases
                smtx_model_eval_derivative_single_rel M hM c hc x rx
                  hArgs.2 hxEval hDerXNe with
                ⟨dx, hDxEval, hDxTy, hDxRel⟩
              have hMergeNe :
                  __re_ac_merge (Term.UOp UserOp.re_union)
                      (__derivative (Term.String [c]) y)
                      (__derivative (Term.String [c]) x) ≠
                    Term.Stuck := by
                simpa [__derivative] using hDerNe
              rcases
                re_ac_merge_union_eval_rel M
                  (__derivative (Term.String [c]) y)
                  (__derivative (Term.String [c]) x) dy dx
                  hDyTy hDxTy hDyEval hDxEval hMergeNe with
                ⟨drv, hDrvEval, hDrvTy, hMergeRel⟩
              refine ⟨drv, ?_, ?_, ?_⟩
              · simpa [__derivative] using hDrvEval
              · simpa [__derivative] using hDrvTy
              · exact RuleProofs.smt_value_rel_trans
                  (SmtValue.RegLan drv)
                  (SmtValue.RegLan (native_re_union dy dx))
                  (SmtValue.RegLan
                    (native_re_deriv c (native_re_union ry rx)))
                  hMergeRel
                  (smt_value_rel_deriv_union c ry rx dy dx hc
                    hDyRel hDxRel)
          case re_inter =>
            have hArgs :=
              reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
                (typeof_re_inter_eq (__eo_to_smt y) (__eo_to_smt x)) (by
                  unfold term_has_non_none_type
                  change __smtx_typeof
                      (__eo_to_smt
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.re_inter) y) x)) ≠
                    SmtType.None
                  rw [hRTy]
                  exact smt_reglan_ne_none)
            change __smtx_model_eval M
                (SmtTerm.re_inter (__eo_to_smt y) (__eo_to_smt x)) =
              SmtValue.RegLan rv at hREval
            cases hyEval : __smtx_model_eval M (__eo_to_smt y) <;>
              cases hxEval : __smtx_model_eval M (__eo_to_smt x) <;>
                simp [__smtx_model_eval, __smtx_model_eval_re_inter,
                  hyEval, hxEval] at hREval
            case RegLan.RegLan ry rx =>
              cases hREval
              have hDerYNe :
                  __derivative (Term.String [c]) y ≠ Term.Stuck := by
                intro hDerY
                apply hDerNe
                simp [hDerY, __re_ac_merge]
              have hDerXNe :
                  __derivative (Term.String [c]) x ≠ Term.Stuck := by
                intro hDerX
                apply hDerNe
                cases hDerY : __derivative (Term.String [c]) y <;>
                  simp [hDerX, __re_ac_merge]
              rcases
                smtx_model_eval_derivative_single_rel M hM c hc y ry
                  hArgs.1 hyEval hDerYNe with
                ⟨dy, hDyEval, hDyTy, hDyRel⟩
              rcases
                smtx_model_eval_derivative_single_rel M hM c hc x rx
                  hArgs.2 hxEval hDerXNe with
                ⟨dx, hDxEval, hDxTy, hDxRel⟩
              have hMergeNe :
                  __re_ac_merge (Term.UOp UserOp.re_inter)
                      (__derivative (Term.String [c]) y)
                      (__derivative (Term.String [c]) x) ≠
                    Term.Stuck := by
                simpa [__derivative] using hDerNe
              rcases
                re_ac_merge_inter_eval_rel M
                  (__derivative (Term.String [c]) y)
                  (__derivative (Term.String [c]) x) dy dx
                  hDyTy hDxTy hDyEval hDxEval hMergeNe with
                ⟨drv, hDrvEval, hDrvTy, hMergeRel⟩
              refine ⟨drv, ?_, ?_, ?_⟩
              · simpa [__derivative] using hDrvEval
              · simpa [__derivative] using hDrvTy
              · exact RuleProofs.smt_value_rel_trans
                  (SmtValue.RegLan drv)
                  (SmtValue.RegLan (native_re_inter dy dx))
                  (SmtValue.RegLan
                    (native_re_deriv c (native_re_inter ry rx)))
                  hMergeRel
                  (smt_value_rel_deriv_inter c ry rx dy dx hc
                    hDyRel hDxRel)
          case re_concat =>
            have hArgs :=
              reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
                (typeof_re_concat_eq (__eo_to_smt y) (__eo_to_smt x)) (by
                  unfold term_has_non_none_type
                  change __smtx_typeof
                      (__eo_to_smt
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.re_concat) y) x)) ≠
                    SmtType.None
                  rw [hRTy]
                  exact smt_reglan_ne_none)
            change __smtx_model_eval M
                (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt x)) =
              SmtValue.RegLan rv at hREval
            cases hyEval : __smtx_model_eval M (__eo_to_smt y) <;>
              cases hxEval : __smtx_model_eval M (__eo_to_smt x) <;>
                simp [__smtx_model_eval, __smtx_model_eval_re_concat,
                  hyEval, hxEval] at hREval
            case RegLan.RegLan ry rx =>
              cases hREval
              have hNullNe : __re_nullable y ≠ Term.Stuck := by
                intro hNull
                apply hDerNe
                simp [hNull, __eo_ite, native_ite,
                  native_teq]
              have hNullEq := re_nullable_term_eq M y ry hyEval hNullNe
              have hDerYNe :
                  __derivative (Term.String [c]) y ≠ Term.Stuck := by
                intro hDerY
                apply hDerNe
                cases hNull : native_re_nullable ry
                · simp [hNullEq, hNull, hDerY,
                    __re_concat_merge, __eo_ite, native_ite, native_teq]
                · cases hDerX : __derivative (Term.String [c]) x <;>
                    simp [hNullEq, hNull, hDerY, __re_concat_merge, __re_ac_merge, __eo_ite,
                      native_ite, native_teq]
              rcases
                smtx_model_eval_derivative_single_rel M hM c hc y ry
                  hArgs.1 hyEval hDerYNe with
                ⟨dy, hDyEval, hDyTy, hDyRel⟩
              have hMergeNe :
                  __re_concat_merge (__derivative (Term.String [c]) y) x ≠
                    Term.Stuck := by
                intro hMerge
                apply hDerNe
                cases hNull : native_re_nullable ry
                · simp [hNullEq, hNull, hMerge, __eo_ite,
                    native_ite, native_teq]
                · cases hDerX : __derivative (Term.String [c]) x <;>
                    simp [hNullEq, hNull, hMerge, __re_ac_merge, __eo_ite, native_ite, native_teq]
              rcases
                re_concat_merge_eval_rel M
                  (__derivative (Term.String [c]) y) x dy rx
                  hDyTy hArgs.2 hDyEval hxEval hMergeNe with
                ⟨dm, hMergeEval, hMergeTy, hMergeRel⟩
              cases hNull : native_re_nullable ry
              · refine ⟨dm, ?_, ?_, ?_⟩
                · simpa [__derivative, hNullEq, hNull, __eo_ite,
                    native_ite, native_teq] using hMergeEval
                · simpa [__derivative, hNullEq, hNull, __eo_ite,
                    native_ite, native_teq] using hMergeTy
                · exact RuleProofs.smt_value_rel_trans
                    (SmtValue.RegLan dm)
                    (SmtValue.RegLan (native_re_concat dy rx))
                    (SmtValue.RegLan
                      (native_re_deriv c (native_re_concat ry rx)))
                    hMergeRel
                    (smt_value_rel_deriv_concat_not_nullable c ry rx dy
                      hNull hDyRel)
              · have hDerXNe :
                  __derivative (Term.String [c]) x ≠ Term.Stuck := by
                  intro hDerX
                  apply hDerNe
                  simp [hNullEq, hNull, hDerX,
                    __re_ac_merge, __eo_ite, native_ite, native_teq]
                rcases
                  smtx_model_eval_derivative_single_rel M hM c hc x rx
                    hArgs.2 hxEval hDerXNe with
                  ⟨dx, hDxEval, hDxTy, hDxRel⟩
                have hUnionNe :
                    __re_ac_merge (Term.UOp UserOp.re_union)
                        (__derivative (Term.String [c]) x)
                        (__re_concat_merge
                          (__derivative (Term.String [c]) y) x) ≠
                      Term.Stuck := by
                  simpa [__derivative, hNullEq, hNull, __eo_ite,
                    native_ite, native_teq] using hDerNe
                rcases
                  re_ac_merge_union_eval_rel M
                    (__derivative (Term.String [c]) x)
                    (__re_concat_merge (__derivative (Term.String [c]) y) x)
                    dx dm hDxTy hMergeTy hDxEval hMergeEval hUnionNe with
                  ⟨drv, hDrvEval, hDrvTy, hUnionRel⟩
                have hUnionMergeRel :
                    RuleProofs.smt_value_rel
                      (SmtValue.RegLan (native_re_union dx dm))
                      (SmtValue.RegLan
                        (native_re_union dx (native_re_concat dy rx))) :=
                  smt_value_rel_re_union
                    (RuleProofs.smt_value_rel_refl (SmtValue.RegLan dx))
                    hMergeRel
                refine ⟨drv, ?_, ?_, ?_⟩
                · simpa [__derivative, hNullEq, hNull, __eo_ite,
                    native_ite, native_teq] using hDrvEval
                · simpa [__derivative, hNullEq, hNull, __eo_ite,
                    native_ite, native_teq] using hDrvTy
                · exact RuleProofs.smt_value_rel_trans
                    (SmtValue.RegLan drv)
                    (SmtValue.RegLan (native_re_union dx dm))
                    (SmtValue.RegLan
                      (native_re_deriv c (native_re_concat ry rx)))
                    hUnionRel
                    (RuleProofs.smt_value_rel_trans
                      (SmtValue.RegLan (native_re_union dx dm))
                      (SmtValue.RegLan
                        (native_re_union dx (native_re_concat dy rx)))
                      (SmtValue.RegLan
                        (native_re_deriv c (native_re_concat ry rx)))
                      hUnionMergeRel
                      (smt_value_rel_deriv_concat_nullable c ry rx dy dx
                        hNull hDyRel hDxRel))
          case re_range =>
            -- Range uses the type invariant to rule out invalid singleton
            -- endpoints; the arithmetic proof is local to this case.
            rcases re_range_derivative_arg_singletons c y x hc hRTy hDerNe with
              ⟨lo, hi, rfl, rfl⟩
            change __smtx_typeof
                (SmtTerm.re_range (SmtTerm.String [lo])
                  (SmtTerm.String [hi])) =
              SmtType.RegLan at hRTy
            have hArgs :=
              seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
                (typeof_re_range_eq (SmtTerm.String [lo])
                  (SmtTerm.String [hi])) (by
                    unfold term_has_non_none_type
                    rw [hRTy]
                    simp)
            have hloStringValid : native_string_valid [lo] = true :=
              native_string_valid_of_smtx_typeof_eo_string [lo]
                (by exact hArgs.1)
            have hhiStringValid : native_string_valid [hi] = true :=
              native_string_valid_of_smtx_typeof_eo_string [hi]
                (by exact hArgs.2)
            have hloValid : native_char_valid lo = true :=
              (native_string_valid_cons_parts hloStringValid).1
            have hhiValid : native_char_valid hi = true :=
              (native_string_valid_cons_parts hhiStringValid).1
            change __smtx_model_eval M
                (SmtTerm.re_range (SmtTerm.String [lo])
                  (SmtTerm.String [hi])) =
              SmtValue.RegLan rv at hREval
            simp [__smtx_model_eval, __smtx_model_eval_re_range,
              ] at hREval
            cases hREval
            by_cases hLo : lo ≤ c
            · by_cases hHi : c ≤ hi
              · refine ⟨native_str_to_re [], ?_, ?_, ?_⟩
                · have hLower := re_range_lower_cond_true c lo hLo
                  have hUpper := re_range_upper_cond_true c hi hHi
                  have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])) =
                        Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String []) := by
                    exact (re_range_derivative_singletons_eq c lo hi hc hloValid hhiValid true true hLower hUpper)
                  have hEval :
                      __smtx_model_eval M
                          (__eo_to_smt
                            (Term.Apply (Term.UOp UserOp.str_to_re)
                              (Term.String []))) =
                        SmtValue.RegLan (native_str_to_re []) := by
                    change __smtx_model_eval M
                        (SmtTerm.str_to_re (SmtTerm.String [])) =
                      SmtValue.RegLan (native_str_to_re [])
                    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
                      ]
                  change __smtx_model_eval M
                      (__eo_to_smt
                        (__derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])))) =
                    SmtValue.RegLan (native_str_to_re [])
                  rw [hDerEq]
                  exact hEval
                · have hLower := re_range_lower_cond_true c lo hLo
                  have hUpper := re_range_upper_cond_true c hi hHi
                  have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])) =
                        Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String []) := by
                    exact (re_range_derivative_singletons_eq c lo hi hc hloValid hhiValid true true hLower hUpper)
                  have hTy :
                      __smtx_typeof
                          (__eo_to_smt
                            (Term.Apply (Term.UOp UserOp.str_to_re)
                              (Term.String []))) =
                        SmtType.RegLan := by
                    change __smtx_typeof
                        (SmtTerm.str_to_re (SmtTerm.String [])) =
                      SmtType.RegLan
                    native_decide
                  change __smtx_typeof
                      (__eo_to_smt
                        (__derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])))) =
                    SmtType.RegLan
                  rw [hDerEq]
                  exact hTy
                · exact smt_value_rel_reglan_of_eq (by
                    simp [native_re_range, native_re_deriv, native_str_to_re,
                      impl_native_re_of_list, native_re_elem_valid,
                      impl_native_re_elem_le, hc, hloValid, hhiValid, hLo, hHi])
              · refine ⟨native_re_none, ?_, ?_, ?_⟩
                · have hLower := re_range_lower_cond_true c lo hLo
                  have hUpper := re_range_upper_cond_false c hi hHi
                  have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])) =
                        Term.UOp UserOp.re_none := by
                    exact (re_range_derivative_singletons_eq c lo hi hc hloValid hhiValid true false hLower hUpper)
                  have hEval :
                      __smtx_model_eval M
                          (__eo_to_smt (Term.UOp UserOp.re_none)) =
                        SmtValue.RegLan native_re_none := by
                    change __smtx_model_eval M SmtTerm.re_none =
                      SmtValue.RegLan native_re_none
                    simp [__smtx_model_eval]
                  change __smtx_model_eval M
                      (__eo_to_smt
                        (__derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])))) =
                    SmtValue.RegLan native_re_none
                  rw [hDerEq]
                  exact hEval
                · have hLower := re_range_lower_cond_true c lo hLo
                  have hUpper := re_range_upper_cond_false c hi hHi
                  have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])) =
                        Term.UOp UserOp.re_none := by
                    exact (re_range_derivative_singletons_eq c lo hi hc hloValid hhiValid true false hLower hUpper)
                  change __smtx_typeof
                      (__eo_to_smt
                        (__derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])))) =
                    SmtType.RegLan
                  rw [hDerEq]
                  native_decide
                · exact smt_value_rel_reglan_of_eq (by
                    simp [native_re_range, native_re_deriv, native_re_none,
                      native_re_elem_valid, impl_native_re_elem_le,
                      hc, hloValid, hhiValid, hLo, hHi])
            · by_cases hHi : c ≤ hi
              · refine ⟨native_re_none, ?_, ?_, ?_⟩
                · have hLower := re_range_lower_cond_false c lo hLo
                  have hUpper := re_range_upper_cond_true c hi hHi
                  have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])) =
                        Term.UOp UserOp.re_none := by
                    exact (re_range_derivative_singletons_eq c lo hi hc hloValid hhiValid false true hLower hUpper)
                  have hEval :
                      __smtx_model_eval M
                          (__eo_to_smt (Term.UOp UserOp.re_none)) =
                        SmtValue.RegLan native_re_none := by
                    change __smtx_model_eval M SmtTerm.re_none =
                      SmtValue.RegLan native_re_none
                    simp [__smtx_model_eval]
                  change __smtx_model_eval M
                      (__eo_to_smt
                        (__derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])))) =
                    SmtValue.RegLan native_re_none
                  rw [hDerEq]
                  exact hEval
                · have hLower := re_range_lower_cond_false c lo hLo
                  have hUpper := re_range_upper_cond_true c hi hHi
                  have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])) =
                        Term.UOp UserOp.re_none := by
                    exact (re_range_derivative_singletons_eq c lo hi hc hloValid hhiValid false true hLower hUpper)
                  change __smtx_typeof
                      (__eo_to_smt
                        (__derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])))) =
                    SmtType.RegLan
                  rw [hDerEq]
                  native_decide
                · exact smt_value_rel_reglan_of_eq (by
                    simp [native_re_range, native_re_deriv, native_re_none,
                      native_re_elem_valid, impl_native_re_elem_le,
                      hc, hloValid, hhiValid, hLo, hHi])
              · refine ⟨native_re_none, ?_, ?_, ?_⟩
                · have hLower := re_range_lower_cond_false c lo hLo
                  have hUpper := re_range_upper_cond_false c hi hHi
                  have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])) =
                        Term.UOp UserOp.re_none := by
                    exact (re_range_derivative_singletons_eq c lo hi hc hloValid hhiValid false false hLower hUpper)
                  have hEval :
                      __smtx_model_eval M
                          (__eo_to_smt (Term.UOp UserOp.re_none)) =
                        SmtValue.RegLan native_re_none := by
                    change __smtx_model_eval M SmtTerm.re_none =
                      SmtValue.RegLan native_re_none
                    simp [__smtx_model_eval]
                  change __smtx_model_eval M
                      (__eo_to_smt
                        (__derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])))) =
                    SmtValue.RegLan native_re_none
                  rw [hDerEq]
                  exact hEval
                · have hLower := re_range_lower_cond_false c lo hLo
                  have hUpper := re_range_upper_cond_false c hi hHi
                  have hDerEq :
                      __derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])) =
                        Term.UOp UserOp.re_none := by
                    exact (re_range_derivative_singletons_eq c lo hi hc hloValid hhiValid false false hLower hUpper)
                  change __smtx_typeof
                      (__eo_to_smt
                        (__derivative (Term.String [c])
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.re_range)
                              (Term.String [lo]))
                            (Term.String [hi])))) =
                    SmtType.RegLan
                  rw [hDerEq]
                  native_decide
                · exact smt_value_rel_reglan_of_eq (by
                    simp [native_re_range, native_re_deriv, native_re_none,
                      native_re_elem_valid, impl_native_re_elem_le,
                      hc, hloValid, hhiValid, hLo, hHi])
  | Term.Stuck, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.UOp1 _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.UOp2 _ _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.UOp3 _ _ _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.__eo_List, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.__eo_List_nil, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.__eo_List_cons, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.Bool, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.Boolean _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.Numeral _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.Rational _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.String _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.Binary _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.Type, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.FunType, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.Var _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.DatatypeType _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.DatatypeTypeRef _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.DtcAppType _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.DtCons _ _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.DtSel _ _ _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.USort _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe
  | Term.UConst _ _, rv, hRTy, hREval, hDerNe => by
      simp [__derivative] at hDerNe

private theorem smtx_model_eval_str_in_re_eval_substrWord
    (M : SmtModel) (hM : model_wf M)
    (str : native_String) (r : Term) (rv : SmtRegLan)
    (hValid : native_string_valid str = true)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hNe : __str_eval_str_in_re_rec (substrWord str 0 str.length) r ≠
      Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (__str_eval_str_in_re_rec (substrWord str 0 str.length) r)) =
      SmtValue.Boolean (native_str_in_re str rv) := by
  induction str generalizing r rv with
  | nil =>
      simp [substrWord] at hNe ⊢
      rw [str_eval_empty_eq_nullable] at hNe ⊢
      simp [native_str_in_re]
      change __smtx_model_eval M (__eo_to_smt (__re_nullable r)) =
        SmtValue.Boolean (native_re_nullable rv)
      exact smtx_model_eval_re_nullable M r rv hREval hNe
  | cons c cs ih =>
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      simp [substrWord, extractString_zero_cons] at hNe ⊢
      rw [substrWord_cons_tail c cs] at hNe ⊢
      by_cases hRNone : r = Term.UOp UserOp.re_none
      · subst r
        change __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean (native_str_in_re (c :: cs) rv)
        change __smtx_model_eval M SmtTerm.re_none = SmtValue.RegLan rv at hREval
        rw [__smtx_model_eval.eq_105] at hREval
        cases hREval
        simp [__smtx_model_eval, native_str_in_re, native_re_none,
          native_re_deriv, native_re_nullable_fold_empty]
      have hRStuck : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hStep :=
        str_eval_concat_step_of_ne_re_none (Term.String [c])
          (substrWord cs 0 cs.length) r hRStuck hRNone
      rw [hStep] at hNe ⊢
      have hDerNe : __derivative (Term.String [c]) r ≠ Term.Stuck := by
        intro hDer
        rw [hDer] at hNe
        cases hTail : substrWord cs 0 cs.length <;>
          simp [__str_eval_str_in_re_rec, hTail] at hNe
      rcases
        smtx_model_eval_derivative_single_rel M hM c hc r rv hRTy hREval
          hDerNe with
        ⟨drv, hDerEval, hDerTy, hDerRel⟩
      have hTailEval :=
        ih (__derivative (Term.String [c]) r) drv hcs hDerTy hDerEval hNe
      rw [hTailEval]
      rw [native_str_in_re_cons hValid]
      have hInEq :
          native_str_in_re cs drv =
            native_str_in_re cs (native_re_deriv c rv) :=
        smt_value_rel_reglan_valid_eq hDerRel hcs
      rw [hInEq]

theorem str_eval_str_in_re_rec_substrWord_eq
    (M : SmtModel) (hM : model_wf M)
    (str : native_String) (r : Term) (rv : SmtRegLan)
    (hValid : native_string_valid str = true)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hNe : __str_eval_str_in_re_rec (substrWord str 0 str.length) r ≠
      Term.Stuck) :
    __str_eval_str_in_re_rec (substrWord str 0 str.length) r =
      Term.Boolean (native_str_in_re str rv) := by
  induction str generalizing r rv with
  | nil =>
      simp [substrWord] at hNe ⊢
      rw [str_eval_empty_eq_nullable] at hNe ⊢
      simp [native_str_in_re]
      exact re_nullable_term_eq M r rv hREval hNe
  | cons c cs ih =>
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      simp [substrWord, extractString_zero_cons] at hNe ⊢
      rw [substrWord_cons_tail c cs] at hNe ⊢
      by_cases hRNone : r = Term.UOp UserOp.re_none
      · subst r
        change Term.Boolean false =
          Term.Boolean (native_str_in_re (c :: cs) rv)
        change __smtx_model_eval M SmtTerm.re_none = SmtValue.RegLan rv at hREval
        rw [__smtx_model_eval.eq_105] at hREval
        cases hREval
        simp [native_str_in_re, native_re_none, native_re_deriv,
          native_re_nullable_fold_empty]
      have hRStuck : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hStep :=
        str_eval_concat_step_of_ne_re_none (Term.String [c])
          (substrWord cs 0 cs.length) r hRStuck hRNone
      rw [hStep] at hNe ⊢
      have hDerNe : __derivative (Term.String [c]) r ≠ Term.Stuck := by
        intro hDer
        rw [hDer] at hNe
        cases hTail : substrWord cs 0 cs.length <;>
          simp [__str_eval_str_in_re_rec, hTail] at hNe
      rcases
        smtx_model_eval_derivative_single_rel M hM c hc r rv hRTy hREval
          hDerNe with
        ⟨drv, hDerEval, hDerTy, hDerRel⟩
      have hTailEq :=
        ih (__derivative (Term.String [c]) r) drv hcs hDerTy hDerEval hNe
      rw [hTailEq]
      rw [native_str_in_re_cons hValid]
      have hInEq :
          native_str_in_re cs drv =
            native_str_in_re cs (native_re_deriv c rv) :=
        smt_value_rel_reglan_valid_eq hDerRel hcs
      rw [hInEq]

theorem smtx_model_eval_str_in_re_eval_side
    (M : SmtModel) (hM : model_wf M)
    (str : native_String) (r side : Term) (rv : SmtRegLan)
    (hSTy : __smtx_typeof (__eo_to_smt (Term.String str)) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSide :
      side =
        __str_eval_str_in_re_rec
          (__str_flatten (__str_nary_intro (Term.String str))) r)
    (hSideNe : side ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt side) =
      SmtValue.Boolean (native_str_in_re str rv) := by
  subst side
  cases str with
  | nil =>
      rw [str_flatten_nary_intro_empty] at hSideNe ⊢
      rw [str_eval_empty_eq_nullable] at hSideNe ⊢
      change __smtx_model_eval M (__eo_to_smt (__re_nullable r)) =
        SmtValue.Boolean (native_re_nullable rv)
      exact
        smtx_model_eval_re_nullable M r rv hREval hSideNe
  | cons c cs =>
      have hValid : native_string_valid (c :: cs) = true :=
        native_string_valid_of_smtx_typeof_eo_string (c :: cs) hSTy
      rw [str_flatten_nary_intro_cons] at hSideNe ⊢
      exact
        smtx_model_eval_str_in_re_eval_substrWord M hM (c :: cs) r rv
          hValid hRTy hREval hSideNe


end RuleProofs
