module

public import Cpc.Proofs.Canonical.Ops
public import Cpc.Proofs.TypePreservation.BitVec
public import Cpc.Proofs.TypePreservation.CoreArith
public import Cpc.Proofs.TypePreservation.Datatypes
public import Cpc.Proofs.TypePreservation.Sets
public import Cpc.Proofs.TypePreservation.SeqStringRegex
import all Cpc.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

attribute [local simp] __smtx_type_wf_component

private theorem term_has_non_none_of_type_eq
    {t : SmtTerm}
    {T : SmtType}
    (h : __smtx_typeof t = T)
    (hT : T ≠ SmtType.None) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type
  rw [h]
  exact hT

private def tp_result_seq_components_wf : SmtType -> Prop
  | SmtType.Seq A => __smtx_type_wf (SmtType.Seq A) = true
  | SmtType.Set A => __smtx_type_wf (SmtType.Set A) = true
  | SmtType.Datatype s d => __smtx_type_wf (SmtType.Datatype s d) = true
  | SmtType.Map A B => __smtx_type_wf (SmtType.Map A B) = true
  | SmtType.FunType A B => __smtx_type_wf (SmtType.FunType A B) = true
  | SmtType.DtcAppType A B =>
      A ≠ SmtType.RegLan ∧ tp_result_seq_components_wf B
  | _ => True

@[simp] private theorem tp_result_seq_components_wf_if
    {c : Prop} [Decidable c] {A B : SmtType} :
    tp_result_seq_components_wf (if c then A else B) ↔
      (if c then tp_result_seq_components_wf A
       else tp_result_seq_components_wf B) := by
  by_cases hc : c <;> simp [hc]

@[simp] private theorem tp_result_seq_components_wf_native_ite
    (c : native_Bool) {A B : SmtType} :
    tp_result_seq_components_wf (native_ite c A B) ↔
      (if c = true then tp_result_seq_components_wf A
       else tp_result_seq_components_wf B) := by
  cases c <;> simp [native_ite]

private theorem tp_result_seq_components_wf_typeof_eq
    (T U : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_eq T U) := by
  cases T <;> cases U <;>
    simp [__smtx_typeof_eq, __smtx_typeof_guard,
      tp_result_seq_components_wf, native_ite, native_Teq]

private theorem tp_result_seq_components_wf_arith_overload_op_1
    (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_arith_overload_op_1 T) := by
  cases T <;> simp [__smtx_typeof_arith_overload_op_1,
    tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_arith_overload_op_2
    (T U : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_arith_overload_op_2 T U) := by
  cases T <;> cases U <;> simp [__smtx_typeof_arith_overload_op_2,
    tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_arith_overload_op_2_ret
    (T U R : SmtType)
    (hR : tp_result_seq_components_wf R) :
    tp_result_seq_components_wf
      (__smtx_typeof_arith_overload_op_2_ret T U R) := by
  cases T <;> cases U <;> simp [__smtx_typeof_arith_overload_op_2_ret,
    tp_result_seq_components_wf, hR]

private theorem tp_result_seq_components_wf_bv_op_1
    (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_bv_op_1 T) := by
  cases T <;> simp [__smtx_typeof_bv_op_1, tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_bv_op_1_ret
    (T R : SmtType)
    (hR : tp_result_seq_components_wf R) :
    tp_result_seq_components_wf (__smtx_typeof_bv_op_1_ret T R) := by
  cases T <;> simp [__smtx_typeof_bv_op_1_ret, tp_result_seq_components_wf,
    hR]

private theorem tp_result_seq_components_wf_bv_op_2
    (T U : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_bv_op_2 T U) := by
  cases T <;> cases U <;>
    simp [__smtx_typeof_bv_op_2, tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_bv_op_2_ret
    (T U R : SmtType)
    (hR : tp_result_seq_components_wf R) :
    tp_result_seq_components_wf (__smtx_typeof_bv_op_2_ret T U R) := by
  cases T <;> cases U <;> simp [__smtx_typeof_bv_op_2_ret,
    tp_result_seq_components_wf, hR]

private theorem tp_result_seq_components_wf_seq_op_1_ret
    (T R : SmtType)
    (hR : tp_result_seq_components_wf R) :
    tp_result_seq_components_wf (__smtx_typeof_seq_op_1_ret T R) := by
  cases T <;> simp [__smtx_typeof_seq_op_1_ret,
    tp_result_seq_components_wf, hR]

private theorem tp_result_seq_components_wf_seq_op_2_ret
    (T U R : SmtType)
    (hR : tp_result_seq_components_wf R) :
    tp_result_seq_components_wf (__smtx_typeof_seq_op_2_ret T U R) := by
  cases T <;> cases U <;> simp [__smtx_typeof_seq_op_2_ret,
    tp_result_seq_components_wf, hR, native_ite, native_Teq]

private theorem tp_result_seq_components_wf_seq_diff
    (T U : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_seq_diff T U) := by
  cases T <;> cases U <;> simp [__smtx_typeof_seq_diff,
    tp_result_seq_components_wf, native_ite, native_Teq]

private theorem tp_result_seq_components_wf_str_indexof
    (T U V : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_str_indexof T U V) := by
  cases T <;> cases U <;> cases V <;> simp [__smtx_typeof_str_indexof,
    tp_result_seq_components_wf, native_ite, native_Teq]

private theorem tp_result_seq_components_wf_str_indexof_re
    (T U V : SmtType) :
    tp_result_seq_components_wf
      (if T = SmtType.Seq SmtType.Char then
        if U = SmtType.RegLan then
          if V = SmtType.Int then SmtType.Int else SmtType.None
        else SmtType.None
      else SmtType.None) := by
  by_cases hT : T = SmtType.Seq SmtType.Char <;>
    by_cases hU : U = SmtType.RegLan <;>
    by_cases hV : V = SmtType.Int <;>
    simp [hT, hU, hV, tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_str_indexof_re_split
    (T U V : SmtType) :
    tp_result_seq_components_wf
      (if T = SmtType.Seq SmtType.Char then
        if U = SmtType.RegLan then
          if V = SmtType.RegLan then SmtType.Int else SmtType.None
        else SmtType.None
      else SmtType.None) := by
  by_cases hT : T = SmtType.Seq SmtType.Char <;>
    by_cases hU : U = SmtType.RegLan <;>
    by_cases hV : V = SmtType.RegLan <;>
    simp [hT, hU, hV, tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_re_exp
    (n : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_re_exp n T) := by
  cases n <;> try simp [__smtx_typeof_re_exp, tp_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_re_loop
    (m n : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_re_loop m n T) := by
  cases m <;> try simp [__smtx_typeof_re_loop, tp_result_seq_components_wf]
  case Numeral i =>
    cases n <;> try simp [tp_result_seq_components_wf]
    case Numeral j =>
      cases T <;> simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_set_member
    (T U : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_set_member T U) := by
  cases T <;> cases U <;> simp [__smtx_typeof_set_member,
    tp_result_seq_components_wf, native_ite, native_Teq]

private theorem tp_result_seq_components_wf_sets_op_2_ret
    (T U R : SmtType)
    (hR : tp_result_seq_components_wf R) :
    tp_result_seq_components_wf (__smtx_typeof_sets_op_2_ret T U R) := by
  cases T <;> cases U <;> simp [__smtx_typeof_sets_op_2_ret,
    tp_result_seq_components_wf, hR, native_ite, native_Teq]

private theorem tp_result_seq_components_wf_int_to_bv
    (n : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_int_to_bv n T) := by
  cases n <;> try simp [__smtx_typeof_int_to_bv, tp_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_concat
    (T U : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_concat T U) := by
  cases T <;> cases U <;> simp [__smtx_typeof_concat,
    tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_extract
    (i j : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_extract i j T) := by
  cases i <;> try simp [__smtx_typeof_extract, tp_result_seq_components_wf]
  case Numeral hi =>
    cases j <;> try simp [tp_result_seq_components_wf]
    case Numeral lo =>
      cases T <;> try simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_repeat
    (n : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_repeat n T) := by
  cases n <;> try simp [__smtx_typeof_repeat, tp_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_zero_extend
    (n : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_zero_extend n T) := by
  cases n <;> try simp [__smtx_typeof_zero_extend, tp_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_sign_extend
    (n : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_sign_extend n T) := by
  cases n <;> try simp [__smtx_typeof_sign_extend, tp_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_rotate_left
    (n : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_rotate_left n T) := by
  cases n <;> try simp [__smtx_typeof_rotate_left, tp_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_rotate_right
    (n : SmtTerm) (T : SmtType) :
    tp_result_seq_components_wf (__smtx_typeof_rotate_right n T) := by
  cases n <;> try simp [__smtx_typeof_rotate_right, tp_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [tp_result_seq_components_wf]

private theorem tp_result_seq_components_wf_of_type_wf
    {T : SmtType} (h : __smtx_type_wf T = true) :
    tp_result_seq_components_wf T := by
  let rec go (T : SmtType) (h : __smtx_type_wf T = true) :
      tp_result_seq_components_wf T := by
    cases T
    case Seq A =>
      exact h
    case Datatype s d =>
      exact h
    case Set A =>
      exact h
    case Map A B =>
      exact h
    case FunType A B =>
      exact h
    case DtcAppType A B =>
      simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h
    all_goals
      simp [tp_result_seq_components_wf]
  exact go T h

private theorem tp_dt_cons_wf_rec_tail
    {T : SmtType} {c : SmtDatatypeCons} {dd : SmtDatatypeDecl}
    (h : __smtx_dt_cons_wf_rec dd (SmtDatatypeCons.cons T c) = true) :
    __smtx_dt_cons_wf_rec dd c = true := by
  cases T <;>
    simp [__smtx_dt_cons_wf_rec, native_and] at h <;>
    exact h.2

private def tp_dtc_resolve_field
    (T : SmtType) (dd : SmtDatatypeDecl) : SmtType :=
  match T with
  | SmtType.TypeRef s => SmtType.Datatype s dd
  | T => T

private theorem tp_dtc_resolve_head_ne_reglan
    {T : SmtType} {c : SmtDatatypeCons} {dd : SmtDatatypeDecl}
    (h : __smtx_dt_cons_wf_rec dd (SmtDatatypeCons.cons T c) = true) :
    tp_dtc_resolve_field T dd ≠ SmtType.RegLan := by
  cases T
  case TypeRef s =>
    simp [tp_dtc_resolve_field]
  all_goals
    apply type_wf_rec_ne_reglan
    simp only [__smtx_dt_cons_wf_rec, native_and,
      Bool.and_eq_true] at h
    exact h.1.2

private theorem tp_result_seq_components_wf_dt_cons_rec
    (T : SmtType) (hT : tp_result_seq_components_wf T)
    (dd : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (i : native_Nat),
      __smtx_dt_wf_rec dd d = true →
      tp_result_seq_components_wf
        (__smtx_typeof_dt_cons_rec T (__smtx_dt_resolve d dd) i)
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, _hWf => by
      simpa [__smtx_dt_resolve, __smtx_dtc_resolve,
        __smtx_typeof_dt_cons_rec] using hT
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero, hWf => by
      have hParts :
          __smtx_dt_cons_wf_rec dd (SmtDatatypeCons.cons U c) = true ∧
            __smtx_dt_wf_rec dd d = true := by
        simpa [__smtx_dt_wf_rec, native_and] using hWf
      have hTailCons : __smtx_dt_cons_wf_rec dd c = true :=
        tp_dt_cons_wf_rec_tail hParts.1
      have hTailWf :
          __smtx_dt_wf_rec dd (SmtDatatype.sum c d) = true := by
        simp [__smtx_dt_wf_rec, native_and, hTailCons, hParts.2]
      have hTail :=
        tp_result_seq_components_wf_dt_cons_rec T hT dd
          (SmtDatatype.sum c d) native_nat_zero hTailWf
      have hUNeReg :
          tp_dtc_resolve_field U dd ≠ SmtType.RegLan :=
        tp_dtc_resolve_head_ne_reglan hParts.1
      have hResolve :
          __smtx_dtc_resolve (SmtDatatypeCons.cons U c) dd =
            SmtDatatypeCons.cons
              (tp_dtc_resolve_field U dd)
              (__smtx_dtc_resolve c dd) := by
        cases U <;> rfl
      rw [__smtx_dt_resolve, hResolve, __smtx_typeof_dt_cons_rec]
      exact ⟨hUNeReg, hTail⟩
  | SmtDatatype.sum c d, native_nat_succ i, hWf => by
      have hParts :
          __smtx_dt_cons_wf_rec dd c = true ∧
            __smtx_dt_wf_rec dd d = true := by
        simpa [__smtx_dt_wf_rec, native_and] using hWf
      simpa [__smtx_dt_resolve, __smtx_typeof_dt_cons_rec] using
        tp_result_seq_components_wf_dt_cons_rec T hT dd d i hParts.2
  | SmtDatatype.null, i, _hWf => by
      cases i <;>
        simp [__smtx_dt_resolve, __smtx_typeof_dt_cons_rec,
          tp_result_seq_components_wf]

private theorem tp_seq_char_wf :
    __smtx_type_wf (SmtType.Seq SmtType.Char) = true := by
  have hSeqInh :
      native_inhabited_type (SmtType.Seq SmtType.Char) = true :=
    native_inhabited_type_seq SmtType.Char
  have hCharInh : native_inhabited_type SmtType.Char = true :=
    native_inhabited_type_char
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, hSeqInh, hCharInh]

private theorem tp_smt_term_result_seq_components_wf_of_non_none
    (x : SmtTerm) (hxNN : term_has_non_none_type x) :
    tp_result_seq_components_wf (__smtx_typeof x) := by
  let rec go (x : SmtTerm) (hxNN : term_has_non_none_type x) :
      tp_result_seq_components_wf (__smtx_typeof x) := by
    cases x
    case _at_purify t =>
      have htNN : term_has_non_none_type t := by
        unfold term_has_non_none_type at hxNN ⊢
        simpa [__smtx_typeof] using hxNN
      simpa [__smtx_typeof] using go t htNN
    case String s =>
      cases hValid : native_string_valid s <;>
        simp [__smtx_typeof, native_ite, hValid, tp_result_seq_components_wf, tp_seq_char_wf]
    case Var s T =>
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      simpa [__smtx_typeof, tp_result_seq_components_wf,
        smtx_typeof_guard_wf_of_non_none T T hGuardNN] using
        tp_result_seq_components_wf_of_type_wf hWf
    case UConst s T =>
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      simpa [__smtx_typeof, tp_result_seq_components_wf,
        smtx_typeof_guard_wf_of_non_none T T hGuardNN] using
        tp_result_seq_components_wf_of_type_wf hWf
    case seq_empty T =>
      have hGuardNN : __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) ≠
          SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf (SmtType.Seq T) = true :=
        smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuardNN
      simpa [__smtx_typeof, tp_result_seq_components_wf,
        smtx_typeof_guard_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuardNN] using
        hWf
    case set_empty T =>
      have hGuardNN : __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) ≠
          SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf (SmtType.Set T) = true :=
        smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuardNN
      simpa [__smtx_typeof, tp_result_seq_components_wf,
        smtx_typeof_guard_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuardNN] using
        hWf
    case seq_unit t =>
      have hGuardNN :
          __smtx_typeof_guard_wf
              (SmtType.Seq (__smtx_typeof t))
              (SmtType.Seq (__smtx_typeof t)) ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf (SmtType.Seq (__smtx_typeof t)) = true :=
        smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq (__smtx_typeof t))
          (SmtType.Seq (__smtx_typeof t)) hGuardNN
      simpa [__smtx_typeof, tp_result_seq_components_wf,
        smtx_typeof_guard_wf_of_non_none (SmtType.Seq (__smtx_typeof t))
          (SmtType.Seq (__smtx_typeof t)) hGuardNN] using
        hWf
    case set_singleton t =>
      have hGuardNN :
          __smtx_typeof_guard_wf
              (SmtType.Set (__smtx_typeof t))
              (SmtType.Set (__smtx_typeof t)) ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf (SmtType.Set (__smtx_typeof t)) = true :=
        smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set (__smtx_typeof t))
          (SmtType.Set (__smtx_typeof t)) hGuardNN
      simpa [__smtx_typeof, tp_result_seq_components_wf,
        smtx_typeof_guard_wf_of_non_none (SmtType.Set (__smtx_typeof t))
          (SmtType.Set (__smtx_typeof t)) hGuardNN] using
        hWf
    case «exists» s T body =>
      have hBody : __smtx_typeof body = SmtType.Bool :=
        exists_body_bool_of_non_none hxNN
      have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
        simpa [native_Teq] using hBody
      have hGuardNN : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        intro hNone
        apply hxNN
        rw [__smtx_typeof.eq_def] <;> simp only
        simp [hEq, native_ite, hNone]
      have hGuard : __smtx_typeof_guard_wf T SmtType.Bool = SmtType.Bool :=
        smtx_typeof_guard_wf_of_non_none T SmtType.Bool hGuardNN
      rw [__smtx_typeof.eq_def] <;> simp only
      simp [hEq, native_ite, hGuard, tp_result_seq_components_wf]
    case «forall» s T body =>
      have hBody : __smtx_typeof body = SmtType.Bool :=
        forall_body_bool_of_non_none hxNN
      have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
        simpa [native_Teq] using hBody
      have hGuardNN : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        intro hNone
        apply hxNN
        rw [__smtx_typeof.eq_def] <;> simp only
        simp [hEq, native_ite, hNone]
      have hGuard : __smtx_typeof_guard_wf T SmtType.Bool = SmtType.Bool :=
        smtx_typeof_guard_wf_of_non_none T SmtType.Bool hGuardNN
      rw [__smtx_typeof.eq_def] <;> simp only
      simp [hEq, native_ite, hGuard, tp_result_seq_components_wf]
    case str_concat x y =>
      rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat)
          (typeof_str_concat_eq x y) hxNN with ⟨T, hxT, hyT⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_concat_eq x y, hxT, hyT]
      simpa [__smtx_typeof_seq_op_2, native_ite, native_Teq, hxT,
        tp_result_seq_components_wf] using hxGood
    case str_rev t =>
      rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
          (typeof_str_rev_eq t) hxNN with ⟨T, htT⟩
      have htNN : term_has_non_none_type t :=
        term_has_non_none_of_type_eq htT (by simp)
      have htGood := go t htNN
      rw [typeof_str_rev_eq t, htT]
      simpa [__smtx_typeof_seq_op_1, htT,
        tp_result_seq_components_wf] using htGood
    case str_substr x y z =>
      rcases str_substr_args_of_non_none hxNN with ⟨T, hxT, hy, hz⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_substr_eq x y z]
      simp [__smtx_typeof_str_substr, hxT, hy, hz]
      simpa [hxT, tp_result_seq_components_wf] using hxGood
    case str_replace x y z =>
      rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
          (typeof_str_replace_eq x y z) hxNN with ⟨T, hxT, hyT, hzT⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_replace_eq x y z, hxT, hyT, hzT]
      simpa [__smtx_typeof_seq_op_3, native_ite, native_Teq, hxT,
        tp_result_seq_components_wf] using hxGood
    case str_replace_all x y z =>
      rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
          (typeof_str_replace_all_eq x y z) hxNN with ⟨T, hxT, hyT, hzT⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_replace_all_eq x y z, hxT, hyT, hzT]
      simpa [__smtx_typeof_seq_op_3, native_ite, native_Teq, hxT,
        tp_result_seq_components_wf] using hxGood
    case str_at x y =>
      rcases str_at_args_of_non_none hxNN with ⟨T, hxT, hy⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_at_eq x y]
      simp [__smtx_typeof_str_at, hxT, hy]
      simpa [hxT, tp_result_seq_components_wf] using hxGood
    case str_update x y z =>
      rcases str_update_args_of_non_none hxNN with ⟨T, hxT, hy, hzT⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_update_eq x y z]
      simpa [__smtx_typeof_str_update, native_ite, native_Teq, hxT, hy,
        hzT, tp_result_seq_components_wf] using hxGood
    case str_to_lower t =>
      have ht : __smtx_typeof t = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
          (typeof_str_to_lower_eq t) hxNN
      rw [typeof_str_to_lower_eq, ht]
      simpa [tp_result_seq_components_wf, native_ite] using tp_seq_char_wf
    case str_to_upper t =>
      have ht : __smtx_typeof t = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
          (typeof_str_to_upper_eq t) hxNN
      rw [typeof_str_to_upper_eq, ht]
      simpa [tp_result_seq_components_wf, native_ite] using tp_seq_char_wf
    case str_from_code t =>
      rw [typeof_str_from_code_eq]
      cases h : __smtx_typeof t <;>
        simp [tp_result_seq_components_wf, native_ite, native_Teq]
      exact tp_seq_char_wf
    case str_from_int t =>
      rw [typeof_str_from_int_eq]
      cases h : __smtx_typeof t <;>
        simp [tp_result_seq_components_wf, native_ite, native_Teq]
      exact tp_seq_char_wf
    case str_replace_re x y z =>
      rw [typeof_str_replace_re_eq x y z]
      rcases str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re)
          (typeof_str_replace_re_eq x y z) hxNN with ⟨hx, hy, hz⟩
      simpa [hx, hy, hz, tp_result_seq_components_wf, native_ite] using tp_seq_char_wf
    case str_replace_re_all x y z =>
      rw [typeof_str_replace_re_all_eq x y z]
      rcases str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all)
          (typeof_str_replace_re_all_eq x y z) hxNN with ⟨hx, hy, hz⟩
      simpa [hx, hy, hz, tp_result_seq_components_wf, native_ite] using tp_seq_char_wf
    case seq_nth x y =>
      rcases seq_nth_args_of_non_none hxNN with ⟨T, hxT, hy⟩
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        rw [typeof_seq_nth_eq x y, hxT, hy] at hxNN
        simpa [__smtx_typeof_seq_nth] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      rw [typeof_seq_nth_eq x y, hxT, hy]
      simpa [__smtx_typeof_seq_nth,
        smtx_typeof_guard_wf_of_non_none T T hGuardNN] using
        tp_result_seq_components_wf_of_type_wf hWf
    case select x y =>
      rcases select_args_of_non_none hxNN with ⟨A, B, hxMap, hyA⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxMap (by simp)
      have hxGood := go x hxNN'
      have hBGood : tp_result_seq_components_wf B := by
        rw [hxMap] at hxGood
        exact tp_result_seq_components_wf_of_type_wf
          (map_type_wf_components_of_wf hxGood).2
      rw [typeof_select_eq x y]
      simpa [__smtx_typeof_select, native_ite, native_Teq, hxMap, hyA] using hBGood
    case store x y z =>
      rcases store_args_of_non_none hxNN with ⟨A, B, hxMap, hyA, hzB⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxMap (by simp)
      have hxGood := go x hxNN'
      rw [typeof_store_eq x y z]
      simpa [__smtx_typeof_store, native_ite, native_Teq, hxMap, hyA, hzB,
        tp_result_seq_components_wf] using hxGood
    case map_diff x y =>
      rcases map_diff_args_of_non_none hxNN with hMap | hSet
      · rcases hMap with ⟨A, B, hxMap, hyMap, hTy⟩
        have hxNN' : term_has_non_none_type x :=
          term_has_non_none_of_type_eq hxMap (by simp)
        have hxGood := go x hxNN'
        have hMapWf : __smtx_type_wf (SmtType.Map A B) = true := by
          simpa [hxMap, tp_result_seq_components_wf] using hxGood
        rw [hTy]
        exact tp_result_seq_components_wf_of_type_wf
          (map_type_wf_components_of_wf hMapWf).1
      · rcases hSet with ⟨A, hxSet, hySet, hTy⟩
        have hxNN' : term_has_non_none_type x :=
          term_has_non_none_of_type_eq hxSet (by simp)
        have hxGood := go x hxNN'
        have hSetWf : __smtx_type_wf (SmtType.Set A) = true := by
          simpa [hxSet, tp_result_seq_components_wf] using hxGood
        rw [hTy]
        exact tp_result_seq_components_wf_of_type_wf
          (set_type_wf_component_of_wf hSetWf)
    case ite c x y =>
      rcases ite_args_of_non_none hxNN with ⟨T, hc, hxT, hyT, hTNN⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxT hTNN
      have hxGood := go x hxNN'
      rw [typeof_ite_eq]
      simp [__smtx_typeof_ite, native_ite, native_Teq, hc, hxT, hyT]
      simpa [hxT] using hxGood
    case choice s T body =>
      have hGuardTy :
          __smtx_typeof (SmtTerm.choice s T body) =
            __smtx_typeof_guard_wf T T :=
        choice_term_guard_type_of_non_none hxNN
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        intro hNone
        unfold term_has_non_none_type at hxNN
        rw [hGuardTy, hNone] at hxNN
        exact hxNN rfl
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      rw [choice_term_typeof_of_non_none hxNN]
      exact tp_result_seq_components_wf_of_type_wf hWf
    case bind s T x1 x2 =>
      have hTyEq : __smtx_typeof (SmtTerm.bind s T x1 x2) = __smtx_typeof x2 :=
        bind_term_typeof_of_non_none hxNN
      have hx2NN : term_has_non_none_type x2 := by
        unfold term_has_non_none_type at hxNN ⊢
        rw [hTyEq] at hxNN
        exact hxNN
      rw [hTyEq]
      exact go x2 hx2NN
    case DtCons s d i =>
      let raw :=
        __smtx_typeof_dt_cons_rec (SmtType.Datatype s d)
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      have hGuardNN : __smtx_typeof_guard_wf (SmtType.Datatype s d) raw ≠
          SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [Smtm.typeof_dt_cons_eq, raw] using hxNN
      rw [Smtm.typeof_dt_cons_eq,
        smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s d) raw
          hGuardNN]
      have hBaseWf : __smtx_type_wf (SmtType.Datatype s d) = true :=
        smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
      have hDatatypeWf :
          __smtx_dt_wf_rec d (__smtx_dd_lookup s d) = true :=
        datatype_wf_rec_of_type_wf hBaseWf
      exact tp_result_seq_components_wf_dt_cons_rec (SmtType.Datatype s d)
        (by simpa [tp_result_seq_components_wf] using hBaseWf)
        d (__smtx_dd_lookup s d) i hDatatypeWf
    case Apply f x =>
      by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
      · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
        let R := __smtx_ret_typeof_sel s d i j
        let inner :=
          __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R)
            (__smtx_typeof x)
        have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
          unfold term_has_non_none_type at hxNN
          rw [typeof_dt_sel_apply_eq] at hxNN
          simpa [R, inner] using hxNN
        have hWf : __smtx_type_wf R = true :=
          smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
        rw [dt_sel_term_typeof_of_non_none hxNN]
        exact tp_result_seq_components_wf_of_type_wf hWf
      · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
        · rcases hTesterWitness with ⟨s, d, i, rfl⟩
          rw [dt_tester_term_typeof_of_non_none hxNN]
          simp [tp_result_seq_components_wf]
        · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
            intro s d i j hEq
            exact hSelWitness ⟨s, d, i, j, hEq⟩
          have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
            intro s d i hEq
            exact hTesterWitness ⟨s, d, i, hEq⟩
          have hTy : generic_apply_type f x :=
            generic_apply_type_of_non_datatype_head hSel hTester
          have hTyEq :
              __smtx_typeof (SmtTerm.Apply f x) =
                __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := hTy
          have hApplyNN :
              __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
                SmtType.None := by
            intro hNone
            unfold term_has_non_none_type at hxNN
            rw [hTyEq, hNone] at hxNN
            exact hxNN rfl
          rcases typeof_apply_non_none_cases hApplyNN with
            ⟨A, B, hHead, hX, _hA, _hB⟩
          have hfNN : term_has_non_none_type f := by
            unfold term_has_non_none_type
            rcases hHead with hF | hF <;> rw [hF] <;> simp
          have hfGood := go f hfNN
          have hApplyTy : __smtx_typeof_apply (__smtx_typeof f)
                (__smtx_typeof x) = B := by
            rcases hHead with hF | hF
            · rw [hF, hX]
              simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
                native_Teq, _hA]
            · rw [hF, hX]
              simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
                native_Teq, _hA]
          rw [hTyEq, hApplyTy]
          rcases hHead with hF | hF
          · have hHeadGood : __smtx_type_wf (SmtType.FunType A B) = true := by
              simpa [hF, tp_result_seq_components_wf] using hfGood
            exact tp_result_seq_components_wf_of_type_wf
              (fun_type_wf_components_of_wf hHeadGood).2
          · have hHeadGood :
                A ≠ SmtType.RegLan ∧ tp_result_seq_components_wf B := by
              simpa [hF, tp_result_seq_components_wf] using hfGood
            exact hHeadGood.2
    case set_union x y =>
      rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
          (typeof_set_union_eq x y) hxNN with ⟨A, hxSet, hySet⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxSet (by simp)
      have hxGood := go x hxNN'
      rw [typeof_set_union_eq x y, hxSet, hySet]
      simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
      simpa [hxSet, tp_result_seq_components_wf] using hxGood
    case set_inter x y =>
      rcases set_binop_args_of_non_none (op := SmtTerm.set_inter)
          (typeof_set_inter_eq x y) hxNN with ⟨A, hxSet, hySet⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxSet (by simp)
      have hxGood := go x hxNN'
      rw [typeof_set_inter_eq x y, hxSet, hySet]
      simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
      simpa [hxSet, tp_result_seq_components_wf] using hxGood
    case set_minus x y =>
      rcases set_binop_args_of_non_none (op := SmtTerm.set_minus)
          (typeof_set_minus_eq x y) hxNN with ⟨A, hxSet, hySet⟩
      have hxNN' : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hxSet (by simp)
      have hxGood := go x hxNN'
      rw [typeof_set_minus_eq x y, hxSet, hySet]
      simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
      simpa [hxSet, tp_result_seq_components_wf] using hxGood
    all_goals
      repeat split
      all_goals
      simp [tp_result_seq_components_wf, __smtx_typeof, native_ite,
        native_Teq, tp_result_seq_components_wf_typeof_eq,
        tp_result_seq_components_wf_arith_overload_op_1,
        tp_result_seq_components_wf_arith_overload_op_2,
        tp_result_seq_components_wf_bv_op_1,
        tp_result_seq_components_wf_bv_op_2,
        tp_result_seq_components_wf_seq_diff,
        tp_result_seq_components_wf_str_indexof,
        tp_result_seq_components_wf_re_exp,
        tp_result_seq_components_wf_re_loop,
        tp_result_seq_components_wf_set_member,
        tp_result_seq_components_wf_int_to_bv,
        tp_result_seq_components_wf_concat,
        tp_result_seq_components_wf_extract,
        tp_result_seq_components_wf_repeat,
        tp_result_seq_components_wf_zero_extend,
        tp_result_seq_components_wf_sign_extend,
        tp_result_seq_components_wf_rotate_left,
        tp_result_seq_components_wf_rotate_right]
    all_goals
      first
      | (apply tp_result_seq_components_wf_arith_overload_op_2_ret <;>
          simp [tp_result_seq_components_wf])
      | (apply tp_result_seq_components_wf_bv_op_1_ret <;>
          simp [tp_result_seq_components_wf])
      | (apply tp_result_seq_components_wf_bv_op_2_ret <;>
          simp [tp_result_seq_components_wf])
      | (apply tp_result_seq_components_wf_seq_op_1_ret <;>
          simp [tp_result_seq_components_wf])
      | (apply tp_result_seq_components_wf_seq_op_2_ret <;>
          simp [tp_result_seq_components_wf])
      | (apply tp_result_seq_components_wf_sets_op_2_ret <;>
          simp [tp_result_seq_components_wf])
  exact go x hxNN

theorem smt_term_fun_type_wf_of_non_none
    (x : SmtTerm)
    (hxNN : term_has_non_none_type x)
    {A B : SmtType}
    (hxTy : __smtx_typeof x = SmtType.FunType A B) :
    __smtx_type_wf (SmtType.FunType A B) = true := by
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  simpa [tp_result_seq_components_wf, hxTy] using hGood

theorem smt_term_fun_like_arg_ne_reglan_of_non_none
    (x : SmtTerm)
    (hxNN : term_has_non_none_type x)
    {A B : SmtType}
    (hxTy :
      __smtx_typeof x = SmtType.FunType A B ∨
        __smtx_typeof x = SmtType.DtcAppType A B) :
    A ≠ SmtType.RegLan := by
  rcases hxTy with hFun | hDtc
  · exact fun_type_domain_ne_reglan_of_wf
      (smt_term_fun_type_wf_of_non_none x hxNN hFun)
  · have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
    rw [hDtc] at hGood
    exact hGood.1

theorem smt_term_seq_type_wf_of_non_none
    (x : SmtTerm)
    (hxNN : term_has_non_none_type x)
    {A : SmtType}
    (hxTy : __smtx_typeof x = SmtType.Seq A) :
    __smtx_type_wf (SmtType.Seq A) = true := by
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  simpa [tp_result_seq_components_wf, hxTy] using hGood

theorem smt_term_set_type_wf_of_non_none
    (x : SmtTerm)
    (hxNN : term_has_non_none_type x)
    {A : SmtType}
    (hxTy : __smtx_typeof x = SmtType.Set A) :
    __smtx_type_wf (SmtType.Set A) = true := by
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  simpa [tp_result_seq_components_wf, hxTy] using hGood

theorem smt_term_map_type_wf_of_non_none
    (x : SmtTerm)
    (hxNN : term_has_non_none_type x)
    {A B : SmtType}
    (hxTy : __smtx_typeof x = SmtType.Map A B) :
    __smtx_type_wf (SmtType.Map A B) = true := by
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  simpa [tp_result_seq_components_wf, hxTy] using hGood

private theorem tp_smt_seq_component_wf_rec_of_non_none_type
    (x : SmtTerm) (T : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Seq T) :
    __smtx_type_wf_rec T = true := by
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    simp
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  rw [hxTy] at hGood
  have hSeqParts :
      native_inhabited_type (SmtType.Seq T) = true ∧
        (native_inhabited_type T = true ∧
          __smtx_type_wf_rec T = true) := by
    simpa [tp_result_seq_components_wf, __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and] using hGood
  exact hSeqParts.2.2

theorem smt_seq_component_wf_rec_of_non_none_type
    (x : SmtTerm) (T : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Seq T) :
    __smtx_type_wf_rec T = true :=
  tp_smt_seq_component_wf_rec_of_non_none_type x T hxTy

private theorem tp_smt_set_component_wf_rec_of_non_none_type
    (x : SmtTerm) (T : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Set T) :
    __smtx_type_wf_rec T = true := by
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    simp
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  rw [hxTy] at hGood
  have hSetParts :
      native_inhabited_type (SmtType.Set T) = true ∧
        (native_inhabited_type T = true ∧
          __smtx_type_wf_rec T = true) := by
    simpa [tp_result_seq_components_wf, __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and] using hGood
  exact hSetParts.2.2

theorem smt_set_component_wf_rec_of_non_none_type
    (x : SmtTerm) (T : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Set T) :
    __smtx_type_wf_rec T = true :=
  tp_smt_set_component_wf_rec_of_non_none_type x T hxTy

private theorem tp_smt_map_components_wf_rec_of_non_none_type
    (x : SmtTerm) (A B : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Map A B) :
    __smtx_type_wf_rec A = true ∧
      __smtx_type_wf_rec B = true := by
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    simp
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  rw [hxTy] at hGood
  have hMapParts :
      native_inhabited_type (SmtType.Map A B) = true ∧
        ((native_inhabited_type A = true ∧ __smtx_type_wf_rec A = true) ∧
          (native_inhabited_type B = true ∧ __smtx_type_wf_rec B = true)) := by
    simpa [tp_result_seq_components_wf, __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and] using hGood
  exact ⟨hMapParts.2.1.2, hMapParts.2.2.2⟩

theorem smt_map_components_wf_rec_of_non_none_type
    (x : SmtTerm) (A B : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Map A B) :
    __smtx_type_wf_rec A = true ∧
      __smtx_type_wf_rec B = true :=
  tp_smt_map_components_wf_rec_of_non_none_type x A B hxTy

private theorem tp_smt_fun_components_wf_rec_of_non_none_type
    (x : SmtTerm) (A B : SmtType)
    (hxTy : __smtx_typeof x = SmtType.FunType A B) :
    __smtx_type_wf_rec A = true ∧
      __smtx_type_wf B = true := by
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    simp
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  rw [hxTy] at hGood
  have hFunParts :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A = true ∧
          __smtx_type_wf B = true := by
    exact fun_type_wf_parts (by simpa [tp_result_seq_components_wf] using hGood)
  exact ⟨hFunParts.2.1, hFunParts.2.2⟩

theorem smt_fun_components_wf_rec_of_non_none_type
    (x : SmtTerm) (A B : SmtType)
    (hxTy : __smtx_typeof x = SmtType.FunType A B) :
    __smtx_type_wf_rec A = true ∧
      __smtx_type_wf B = true :=
  tp_smt_fun_components_wf_rec_of_non_none_type x A B hxTy

private theorem tp_smt_datatype_wf_of_non_none_type
    (x : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (hxTy : __smtx_typeof x = SmtType.Datatype s d) :
    __smtx_type_wf (SmtType.Datatype s d) = true := by
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    simp
  have hGood := tp_smt_term_result_seq_components_wf_of_non_none x hxNN
  rw [hxTy] at hGood
  simpa [tp_result_seq_components_wf] using hGood

theorem smt_datatype_wf_of_non_none_type
    (x : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (hxTy : __smtx_typeof x = SmtType.Datatype s d) :
    __smtx_type_wf (SmtType.Datatype s d) = true :=
  tp_smt_datatype_wf_of_non_none_type x s d hxTy

/-- Evaluating a choice term yields a canonical value: it selects either a
witness or the canonical `NotValue`. -/
private theorem tp_native_eval_tchoice_canonical
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
    · simpa [hSat, hTy] using value_canonical_notValue

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
  | purify ht1 hs1 =>
      simpa [__smtx_typeof, __smtx_model_eval, __smtx_model_eval__at_purify] using
        supported_type_preservation M hM _ ht1 hs1
  | var s T hT =>
      exact typeof_value_model_eval_var M hM s T hT ht
  | uconst s T hT =>
      exact typeof_value_model_eval_uconst M hM s T hT ht
  | re_allchar =>
      exact typeof_value_model_eval_re_allchar M
  | re_none =>
      exact typeof_value_model_eval_re_none M
  | re_all =>
      exact typeof_value_model_eval_re_all M
  | seq_empty T hT =>
      exact typeof_value_model_eval_seq_empty M T hT ht
  | set_empty T hT =>
      exact typeof_value_model_eval_set_empty M T hT ht
  | seq_unit ht1 hs1 =>
      exact typeof_value_model_eval_seq_unit M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | set_singleton ht1 hs1 =>
      exact typeof_value_model_eval_set_singleton M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | seq_nth ht1 hs1 ht2 hs2 hT hElemRec =>
      exact typeof_value_model_eval_seq_nth M hM _ _ ht hElemRec
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_union ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_union M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_inter ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_inter M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_minus ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_minus M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_member ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_member M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_subset ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_subset M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | select ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_select M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | store ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_store M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | map_diff ht1 hs1 ht2 hs2 hDefault =>
      exact typeof_value_model_eval_map_diff M _ _ ht
        (fun {A} hA => (hDefault (A := A) hA).1)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | seq_diff ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_seq_diff M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
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
  | xor t1 t2 =>
      exact typeof_value_model_eval_xor M t1 t2 ht
  | plus ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_plus M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | arith_neg ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_neg M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | mult ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_mult M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | lt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_lt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | leq ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_leq M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | gt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_gt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | geq ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_geq M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | to_real ht1 hs1 =>
      exact typeof_value_model_eval_to_real M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | to_int ht1 hs1 =>
      exact typeof_value_model_eval_to_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | is_int ht1 hs1 =>
      exact typeof_value_model_eval_is_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | abs ht1 hs1 =>
      exact typeof_value_model_eval_abs M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | uneg ht1 hs1 =>
      exact typeof_value_model_eval_uneg M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | div ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_div M hM _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | mod ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_mod M hM _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | divisible ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_divisible M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | int_pow2 ht1 hs1 =>
      exact typeof_value_model_eval_int_pow2 M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | int_log2 ht1 hs1 =>
      exact typeof_value_model_eval_int_log2 M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | div_total ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_div_total M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | mod_total ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_mod_total M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | qdiv ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_qdiv M hM _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | qdiv_total ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_qdiv_total M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_len ht1 hs1 =>
      exact typeof_value_model_eval_str_len M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_to_lower ht1 hs1 =>
      exact typeof_value_model_eval_str_to_lower M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_to_upper ht1 hs1 =>
      exact typeof_value_model_eval_str_to_upper M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_concat ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_concat M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_substr ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_substr M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_contains ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_contains M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_indexof ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_indexof M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_at ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_at M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_replace ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_replace M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_rev ht1 hs1 =>
      exact typeof_value_model_eval_str_rev M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_update ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_update M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_replace_all ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_replace_all M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_replace_re ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_replace_re M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_replace_re_all ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_replace_re_all M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_indexof_re ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_indexof_re M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | _at_strings_occur_index ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_at_strings_occur_index M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | _at_strings_occur_index_re ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_at_strings_occur_index_re M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_indexof_re_split ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_indexof_re_split M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_to_code ht1 hs1 =>
      exact typeof_value_model_eval_str_to_code M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_to_int ht1 hs1 =>
      exact typeof_value_model_eval_str_to_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_from_code ht1 hs1 =>
      exact typeof_value_model_eval_str_from_code M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_from_int ht1 hs1 =>
      exact typeof_value_model_eval_str_from_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_to_re ht1 hs1 =>
      exact typeof_value_model_eval_str_to_re M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_mult ht1 hs1 =>
      exact typeof_value_model_eval_re_mult M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_plus ht1 hs1 =>
      exact typeof_value_model_eval_re_plus M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_exp n ht1 hs1 =>
      exact typeof_value_model_eval_re_exp M n _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_opt ht1 hs1 =>
      exact typeof_value_model_eval_re_opt M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_comp ht1 hs1 =>
      exact typeof_value_model_eval_re_comp M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_range ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_range M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_concat ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_concat M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_inter ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_inter M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_union ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_union M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_diff ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_diff M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_loop n1 n2 ht1 hs1 =>
      exact typeof_value_model_eval_re_loop M n1 n2 _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_in_re ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_in_re M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_lt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_lt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_leq ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_leq M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_prefixof ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_prefixof M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_suffixof ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_suffixof M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_is_digit ht1 hs1 =>
      exact typeof_value_model_eval_str_is_digit M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | bv_concat ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_concat M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | extract ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_extract M _ _ _ ht
        (supported_type_preservation M hM _ ht3 hs3)
  | bvnot ht1 hs1 =>
      exact typeof_value_model_eval_bvnot M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | bvand ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvand M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvor ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvor M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvnand ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvnand M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvnor ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvnor M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvxor ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvxor M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvxnor ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvxnor M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvcomp ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvcomp M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvneg ht1 hs1 =>
      exact typeof_value_model_eval_bvneg M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | bvadd ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvadd M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvmul ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvmul M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvudiv ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvudiv M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvurem ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvurem M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsub ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsub M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvult ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvult M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvule ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvule M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvugt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvugt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvuge ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvuge M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvslt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvslt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsle ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsle M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsgt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsgt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsge ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsge M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvshl ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvshl M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvlshr ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvlshr M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «repeat» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_repeat M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsdiv ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsdiv M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsrem ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsrem M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsmod ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsmod M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvashr ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvashr M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | rotate_left ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_rotate_left M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | rotate_right ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_rotate_right M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | bvuaddo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvuaddo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvnego ht1 hs1 =>
      exact typeof_value_model_eval_bvnego M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | bvsaddo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsaddo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvumulo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvumulo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsmulo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsmulo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvusubo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvusubo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvssubo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvssubo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsdivo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsdivo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | zero_extend ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_zero_extend M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | sign_extend ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_sign_extend M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | int_to_bv ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_int_to_bv M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | ubv_to_int ht1 hs1 =>
      exact typeof_value_model_eval_ubv_to_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | sbv_to_int ht1 hs1 =>
      exact typeof_value_model_eval_sbv_to_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | dt_cons s d i =>
      exact typeof_value_model_eval_dt_cons M s d i ht
  | dt_sel htSel hT hWrongMapWF htx hsx =>
      exact typeof_value_model_eval_dt_sel M hM _ _ _ _ _ htSel hWrongMapWF hT
        (supported_type_preservation M hM _ htx hsx)
  | dt_tester s d i x =>
      exact typeof_value_model_eval_dt_tester M s d i x ht
  | apply hTy hEval htf hsf htx hsx =>
      rename_i f x
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
        have hGood := tp_smt_term_result_seq_components_wf_of_non_none f htf
        rw [hFunTy] at hGood
        simpa [tp_result_seq_components_wf] using hGood
      exact typeof_value_model_eval_apply_generic M hM f x hFunWF hNN
        (supported_type_preservation M hM f htf hsf)
        (supported_type_preservation M hM x htx hsx)

/-- Canonicity preservation: evaluating a supported, well-typed SMT term in a
total typed model yields a canonical value.  Mutually recursive with
`supported_type_preservation` (the `bind` case of each needs the other for the
bound value). -/
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
      simpa [__smtx_model_eval] using value_canonical_boolean b
  case numeral n =>
      simpa [__smtx_model_eval] using value_canonical_numeral n
  case rational q =>
      simpa [__smtx_model_eval] using value_canonical_rational q
  case string s =>
      have hsValid : native_string_valid s = true := by
        rw [term_has_non_none_type, __smtx_typeof.eq_4] at ht
        cases hValid : native_string_valid s <;>
          simp [native_ite, hValid] at ht ⊢
      simpa [__smtx_model_eval] using model_eval_string_value_canonical s hsValid
  case binary w n =>
      cases hw : native_zleq 0 w <;>
        cases hn : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_model_eval, __smtx_typeof, value_canonical,
            __smtx_value_canonical, term_has_non_none_type,
            native_and, SmtEval.native_and,
            native_ite, hw, hn] at ht ⊢
  case purify ht1 hs1 =>
      simpa [__smtx_model_eval, __smtx_model_eval__at_purify] using
        canonical_of_supported M hM _ ht1 hs1
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
  case re_allchar =>
      simpa [__smtx_model_eval] using value_canonical_reglan_allchar
  case re_none =>
      simpa [__smtx_model_eval] using value_canonical_reglan_none
  case re_all =>
      simpa [__smtx_model_eval] using value_canonical_reglan_all
  case seq_empty T hT =>
      simpa [__smtx_model_eval] using model_eval_seq_empty_value_canonical T
  case set_empty T hT =>
      simpa [__smtx_model_eval] using model_eval_set_empty_value_canonical T
  case seq_unit ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_seq_unit_value_canonical (v := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
  case set_singleton ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_set_singleton_value_canonical (v := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
  case seq_nth ht1 hs1 ht2 hs2 hT hElemRec =>
      rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at ht
        rw [typeof_seq_nth_eq] at ht
        simpa [__smtx_typeof_seq_nth, h1, h2] using ht
      have hTWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      have hRec : __smtx_type_wf_rec T = true := hElemRec h1
      have hTInh : native_inhabited_type T = true := by
        cases T <;>
          simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
            native_and] at hTWf hRec ⊢
        all_goals first | exact hTWf | exact hTWf.1 | exact hTWf.1.1 | contradiction
      have hMapWF := seq_nth_wrong_map_type_wf hTInh hRec
      have hvTy := (supported_type_preservation M hM _ ht1 hs1).trans h1
      simpa [__smtx_model_eval] using
        model_eval_seq_nth_canonical (M := M) (hM := hM)
          (v := __smtx_model_eval M _) (i := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1) T hvTy hMapWF
  case set_union ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_set_union_canonical
          (v1 := __smtx_model_eval M _) (v2 := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case set_inter ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_set_inter_canonical
          (v1 := __smtx_model_eval M _) (v2 := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case set_minus ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_set_minus_canonical
          (v1 := __smtx_model_eval M _) (v2 := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case set_member ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval, __smtx_model_eval_set_member,
        __smtx_model_eval_select] using
        model_eval_select_canonical
          (v := __smtx_model_eval M _)
          (i := __smtx_model_eval M _) (canonical_of_supported M hM _ ht2 hs2)
  case set_subset ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval, __smtx_model_eval_set_subset] using
        model_eval_eq_canonical
          (__smtx_model_eval_set_inter (__smtx_model_eval M _) (__smtx_model_eval M _))
          (__smtx_model_eval M _)
  case select ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_select_canonical
          (v := __smtx_model_eval M _)
          (i := __smtx_model_eval M _) (canonical_of_supported M hM _ ht1 hs1)
  case store ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_store_canonical
          (v := __smtx_model_eval M _) (i := __smtx_model_eval M _)
          (e := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
          (canonical_of_supported M hM _ ht3 hs3)
  case map_diff ht1 hs1 ht2 hs2 hDefault =>
      exact model_eval_map_diff_canonical M _ _ ht
        (fun {A} hA => (hDefault (A := A) hA).2)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  case seq_diff ht1 hs1 ht2 hs2 =>
      have hpres := typeof_value_model_eval_seq_diff M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
      refine value_canonical_of_int_type (hpres.trans ?_)
      rcases seq_binop_args_of_non_none_ret (op := SmtTerm.seq_diff)
          (typeof_seq_diff_eq _ _) ht with ⟨T, h1, h2⟩
      rw [typeof_seq_diff_eq]
      simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, h1, h2]
  case ite htc hsc ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_ite_canonical
          (c := __smtx_model_eval M _) (t := __smtx_model_eval M _)
          (e := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case «exists» s T body =>
      exact value_canonical_of_bool_type
        ((typeof_value_model_eval_exists M s T body ht).trans
          (exists_term_typeof_of_non_none ht))
  case «forall» s T body =>
      exact value_canonical_of_bool_type
        ((typeof_value_model_eval_forall M s T body ht).trans
          (forall_term_typeof_of_non_none ht))
  case choice s T body htc =>
      simpa [__smtx_model_eval] using tp_native_eval_tchoice_canonical M s T body
  case «not» ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_not_canonical (__smtx_model_eval M _)
  case «or» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_or_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «and» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_and_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «imp» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_imp_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case eq t1 t2 =>
      simpa [__smtx_model_eval] using
        model_eval_eq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)
  case xor t1 t2 =>
      simpa [__smtx_model_eval] using
        model_eval_xor_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)
  case plus ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_plus_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case arith_neg ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_sub_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case mult ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_mult_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case lt ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_lt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case leq ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_leq_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case gt ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_gt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case geq ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_geq_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case to_real ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_to_real_canonical (__smtx_model_eval M _)
  case to_int ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_to_int_canonical (__smtx_model_eval M _)
  case is_int ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_is_int_canonical (__smtx_model_eval M _)
  case abs ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_abs_canonical (__smtx_model_eval M _)
  case uneg ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_uneg_canonical (__smtx_model_eval M _)
  case div ht1 hs1 ht2 hs2 =>
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.div) (typeof_div_eq _ _) ht
      have hxTy := (supported_type_preservation M hM _ ht1 hs1).trans hArgs.1
      simpa [__smtx_model_eval] using
        model_eval_ite_canonical
          (model_eval_apply_lookup_fun_canonical M hM native_div_by_zero_id
            SmtType.Int SmtType.Int _ fun_type_wf_int_int hxTy)
          (model_eval_div_total_canonical _ _)
  case mod ht1 hs1 ht2 hs2 =>
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod) (typeof_mod_eq _ _) ht
      have hxTy := (supported_type_preservation M hM _ ht1 hs1).trans hArgs.1
      simpa [__smtx_model_eval] using
        model_eval_ite_canonical
          (model_eval_apply_lookup_fun_canonical M hM native_mod_by_zero_id
            SmtType.Int SmtType.Int _ fun_type_wf_int_int hxTy)
          (model_eval_mod_total_canonical _ _)
  case divisible ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_divisible_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case int_pow2 ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_int_pow2_canonical (__smtx_model_eval M _)
  case int_log2 ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_int_log2_canonical (__smtx_model_eval M _)
  case div_total ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_div_total_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case mod_total ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_mod_total_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case qdiv ht1 hs1 ht2 hs2 =>
      rename_i t1 t2
      rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv)
          (typeof_qdiv_eq t1 t2) ht with hArgs | hArgs
      · have hpres1 := supported_type_preservation M hM t1 ht1 hs1
        rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
        have hxTy :
            __smtx_typeof_value
              (__smtx_to_real_coerce (__smtx_model_eval M t1)) = SmtType.Real := by
          rw [hn1]
          simp [__smtx_to_real_coerce, __smtx_typeof_value]
        simpa [__smtx_model_eval] using
          model_eval_ite_canonical
            (model_eval_apply_lookup_fun_canonical M hM native_qdiv_by_zero_id
              SmtType.Real SmtType.Real
              (__smtx_to_real_coerce (__smtx_model_eval M t1))
              fun_type_wf_real_real hxTy)
            (model_eval_qdiv_total_canonical _ _)
      · have hxTyRaw :
            __smtx_typeof_value (__smtx_model_eval M t1) = SmtType.Real := by
          simpa [hArgs.1] using supported_type_preservation M hM t1 ht1 hs1
        rcases real_value_canonical hxTyRaw with ⟨q1, hq1⟩
        have hxTy :
            __smtx_typeof_value
              (__smtx_to_real_coerce (__smtx_model_eval M t1)) = SmtType.Real := by
          rw [hq1]
          simp [__smtx_to_real_coerce, __smtx_typeof_value]
        simpa [__smtx_model_eval] using
          model_eval_ite_canonical
            (model_eval_apply_lookup_fun_canonical M hM native_qdiv_by_zero_id
              SmtType.Real SmtType.Real
              (__smtx_to_real_coerce (__smtx_model_eval M t1))
              fun_type_wf_real_real hxTy)
            (model_eval_qdiv_total_canonical _ _)
  case qdiv_total ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_qdiv_total_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_concat ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_concat_canonical
          (v1 := __smtx_model_eval M _) (v2 := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case str_substr ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_substr_canonical
          (v := __smtx_model_eval M _) (i := __smtx_model_eval M _)
          (n := __smtx_model_eval M _) (canonical_of_supported M hM _ ht1 hs1)
  case str_contains ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_contains_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_indexof ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_indexof_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_at ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_at_canonical
          (v := __smtx_model_eval M _) (i := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
  case str_replace ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_replace_canonical
          (v := __smtx_model_eval M _) (pat := __smtx_model_eval M _)
          (repl := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
          (canonical_of_supported M hM _ ht3 hs3)
  case str_rev ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_rev_canonical (v := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
  case str_update ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_update_canonical
          (v := __smtx_model_eval M _) (i := __smtx_model_eval M _)
          (repl := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht3 hs3)
  case str_replace_all ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_replace_all_canonical
          (v := __smtx_model_eval M _) (pat := __smtx_model_eval M _)
          (repl := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
          (canonical_of_supported M hM _ ht3 hs3)
  case str_replace_re ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_replace_re_canonical
          (__smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht3 hs3)
  case str_replace_re_all ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_replace_re_all_canonical
          (__smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht3 hs3)
  case str_indexof_re ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_indexof_re_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case _at_strings_occur_index ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_at_strings_occur_index_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case _at_strings_occur_index_re ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_at_strings_occur_index_re_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_indexof_re_split ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_str_indexof_re_split_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_len ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_len_canonical (__smtx_model_eval M _)
  case str_to_lower ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_to_lower_canonical (canonical_of_supported M hM _ ht1 hs1)
  case str_to_upper ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_to_upper_canonical (canonical_of_supported M hM _ ht1 hs1)
  case str_to_code ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_to_code_canonical (__smtx_model_eval M _)
  case str_to_int ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_to_int_canonical (__smtx_model_eval M _)
  case str_from_code ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_from_code_canonical (__smtx_model_eval M _)
  case str_from_int ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_from_int_canonical (__smtx_model_eval M _)
  case str_to_re t ht1 hs1 =>
      have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
          (typeof_str_to_re_eq t) ht
      have hEvalTy :
          __smtx_typeof_value (__smtx_model_eval M t) =
            SmtType.Seq SmtType.Char := by
        simpa [hArg] using supported_type_preservation M hM t ht1 hs1
      simpa [__smtx_model_eval] using
        model_eval_str_to_re_canonical
          (canonical_of_supported M hM t ht1 hs1) hEvalTy
  case re_mult ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_re_mult_canonical (canonical_of_supported M hM _ ht1 hs1)
  case re_plus ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_re_plus_canonical (canonical_of_supported M hM _ ht1 hs1)
  case re_exp n ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_re_exp_canonical (SmtValue.Numeral _)
          (canonical_of_supported M hM _ ht1 hs1)
  case re_opt ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_re_opt_canonical (canonical_of_supported M hM _ ht1 hs1)
  case re_comp ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_re_comp_canonical (canonical_of_supported M hM _ ht1 hs1)
  case re_range t1 t2 ht1 hs1 ht2 hs2 =>
      have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
        (typeof_re_range_eq t1 t2) ht
      have hEvalTy1 :
          __smtx_typeof_value (__smtx_model_eval M t1) =
            SmtType.Seq SmtType.Char := by
        simpa [hArgs.1] using supported_type_preservation M hM t1 ht1 hs1
      have hEvalTy2 :
          __smtx_typeof_value (__smtx_model_eval M t2) =
            SmtType.Seq SmtType.Char := by
        simpa [hArgs.2] using supported_type_preservation M hM t2 ht2 hs2
      simpa [__smtx_model_eval] using
        model_eval_re_range_canonical
          (canonical_of_supported M hM t1 ht1 hs1)
          (canonical_of_supported M hM t2 ht2 hs2)
          hEvalTy1 hEvalTy2
  case re_concat ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_re_concat_canonical
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case re_inter ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_re_inter_canonical
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case re_union ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_re_union_canonical
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case re_diff ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_re_diff_canonical
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case re_loop n1 n2 ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_re_loop_canonical (SmtValue.Numeral _) (SmtValue.Numeral _)
          (canonical_of_supported M hM _ ht1 hs1)
  case str_in_re ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_in_re_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_lt ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_lt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_leq ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_leq_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_prefixof ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_prefixof_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_suffixof ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_str_suffixof_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case str_is_digit ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_str_is_digit_canonical (__smtx_model_eval M _)
  case bv_concat ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_concat_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case extract ht1 hs1 ht2 hs2 ht3 hs3 =>
      simpa [__smtx_model_eval] using
        model_eval_extract_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvnot ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_bvnot_canonical (__smtx_model_eval M _)
  case bvand ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvand_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvor ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvor_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvnand ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvnand_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvnor ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvnor_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvxor ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvxor_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvxnor ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvxnor_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvcomp ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvcomp_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvneg ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_bvneg_canonical (__smtx_model_eval M _)
  case bvadd ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvadd_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvmul ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvmul_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvudiv ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvudiv_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvurem ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvurem_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsub ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsub_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvult ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvult_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvule ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvule_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvugt ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvugt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvuge ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvuge_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvslt ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvslt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsle ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsle_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsgt ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsgt_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsge ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsge_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvshl ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvshl_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvlshr ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvlshr_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «repeat» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_repeat_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsdiv ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsdiv_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsrem ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsrem_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsmod ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsmod_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvashr ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvashr_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case rotate_left ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_rotate_left_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _)
          (canonical_of_supported M hM _ ht2 hs2)
  case rotate_right ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_rotate_right_canonical
          (__smtx_model_eval M _) (__smtx_model_eval M _)
          (canonical_of_supported M hM _ ht2 hs2)
  case bvuaddo ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvuaddo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvnego ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_bvnego_canonical (__smtx_model_eval M _)
  case bvsaddo ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsaddo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvumulo ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvumulo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsmulo ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsmulo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvusubo ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvusubo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvssubo ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvssubo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case bvsdivo ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_bvsdivo_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case zero_extend ht1 hs1 ht2 hs2 =>
      rcases zero_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
      have hpres := typeof_value_model_eval_zero_extend M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
      refine value_canonical_of_bitvec_type
        (w := native_int_to_nat (native_zplus i (native_nat_to_int w))) (hpres.trans ?_)
      rw [typeof_zero_extend_eq]
      simp [__smtx_typeof_zero_extend, h1, h2, hi0, native_ite]
  case sign_extend ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_sign_extend_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case int_to_bv ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        model_eval_int_to_bv_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case ubv_to_int ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_ubv_to_int_canonical (__smtx_model_eval M _)
  case sbv_to_int ht1 hs1 =>
      simpa [__smtx_model_eval] using
        model_eval_sbv_to_int_canonical (__smtx_model_eval M _)
  case dt_cons s d i =>
      simpa [__smtx_model_eval] using value_canonical_dt_cons s d i
  case dt_sel htSel hT hWrongMapWF htx hsx =>
      have hxTy :=
        (supported_type_preservation M hM _ htx hsx).trans
          (dt_sel_arg_datatype_of_non_none htSel)
      simpa [__smtx_model_eval] using
        model_eval_dt_sel_canonical M hM _ _ _ _ hWrongMapWF hxTy
          (canonical_of_supported M hM _ htx hsx)
  case dt_tester s d i x =>
      simpa [__smtx_model_eval, __smtx_model_eval_dt_tester] using
        value_canonical_boolean (native_veq (__smtx_apply_head_value (__smtx_model_eval M x))
          (SmtValue.DtCons s d i))
  case apply hTyApp hEval htf hsf htx hsx =>
      rename_i f x
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
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHeadTerm, hX, _hA, _hB⟩
      have hPresF :
          __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
        supported_type_preservation M hM f htf hsf
      have hPresX :
          __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
        supported_type_preservation M hM x htx hsx
      have hxTy :
          __smtx_typeof_value (__smtx_model_eval M x) = A := by
        simpa [hX] using hPresX
      have hHeadVal :
          __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B ∨
            __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
        cases hHeadTerm with
        | inl hFun =>
            exact Or.inl (by simpa [hFun] using hPresF)
        | inr hDtc =>
            exact Or.inr (by simpa [hDtc] using hPresF)
      have hFunWF :
          __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B ->
            __smtx_type_wf (SmtType.FunType A B) = true := by
        intro hValFun
        cases hHeadTerm with
        | inl hFun =>
            exact smt_term_fun_type_wf_of_non_none f htf hFun
        | inr hDtc =>
            have hValDtc :
                __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
              simpa [hDtc] using hPresF
            rw [hValFun] at hValDtc
            cases hValDtc
      simpa [hEval M] using
        model_eval_apply_canonical M hM
          (f := __smtx_model_eval M f)
          (x := __smtx_model_eval M x)
          (hHead := hHeadVal)
          (hFunWF := hFunWF)
          (hxTy := hxTy)
          hf hx

end

/- Obsolete two-datatype well-formedness helpers retained in history. -/
/-
private theorem tp_dt_cons_wf_rec_tail_of_true
    {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF) (SmtDatatypeCons.cons TU cU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  by_cases hc : __smtx_dt_cons_wf_rec cF cU = true
  · exact hc
  · exfalso
    cases TF <;> cases TU <;>
      simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]

private theorem tp_dt_wf_cons_of_wf
    {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum cF dF) (SmtDatatype.sum cU dU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  cases hc : __smtx_dt_cons_wf_rec cF cU <;>
    simp [__smtx_dt_wf_rec, native_ite, hc] at h ⊢

private theorem tp_dt_wf_tail_of_nonempty_tail_wf
    {cF cU cTailF cTailU : SmtDatatypeCons}
    {dTailF dTailU : SmtDatatype}
    (h : __smtx_dt_wf_rec
        (SmtDatatype.sum cF (SmtDatatype.sum cTailF dTailF))
        (SmtDatatype.sum cU (SmtDatatype.sum cTailU dTailU)) = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum cTailF dTailF)
      (SmtDatatype.sum cTailU dTailU) = true := by
  have hc : __smtx_dt_cons_wf_rec cF cU = true :=
    tp_dt_wf_cons_of_wf h
  simpa [__smtx_dt_wf_rec, native_ite, hc] using h

private theorem tp_ret_typeof_sel_rec_resolve_ne_reglan_of_cons_wf
    (dd : SmtDatatypeDecl) :
    ∀ (c : SmtDatatypeCons) (d : SmtDatatype) (j : native_Nat),
      __smtx_dt_cons_wf_rec (__smtx_dtc_resolve c dd) c = true ->
        __smtx_ret_typeof_sel_rec
            (SmtDatatype.sum (__smtx_dtc_resolve c dd)
              (__smtx_dt_resolve d dd)) native_nat_zero j ≠
          SmtType.RegLan
  | SmtDatatypeCons.unit, d, j, _hWf => by
      cases j <;> simp [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec]
  | SmtDatatypeCons.cons T c, d, native_nat_zero, hWf => by
      cases T
      case TypeRef r =>
        simp [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec]
      all_goals
        simp [__smtx_dtc_resolve, __smtx_dt_cons_wf_rec,
          __smtx_type_wf_rec,
          __smtx_ret_typeof_sel_rec, native_ite,
          native_and] at hWf ⊢
  | SmtDatatypeCons.cons T c, d, native_nat_succ j, hWf => by
      have hTail : __smtx_dt_cons_wf_rec (__smtx_dtc_resolve c dd) c = true := by
        cases T <;>
          exact tp_dt_cons_wf_rec_tail_of_true (by simpa [__smtx_dtc_resolve] using hWf)
      cases T <;>
        simpa [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec] using
          tp_ret_typeof_sel_rec_resolve_ne_reglan_of_cons_wf dd
            c d j hTail

private theorem tp_ret_typeof_sel_rec_resolve_ne_reglan_of_dt_wf
    (dd : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (i j : native_Nat),
      __smtx_dt_wf_rec (__smtx_dt_resolve d dd) d = true ->
        __smtx_ret_typeof_sel_rec (__smtx_dt_resolve d dd) i j ≠
          SmtType.RegLan
  | SmtDatatype.null, i, j, _hWf => by
      cases i <;> cases j <;>
        simp [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec]
  | SmtDatatype.sum c d, native_nat_zero, j, hWf => by
      have hCons : __smtx_dt_cons_wf_rec (__smtx_dtc_resolve c dd) c = true :=
        tp_dt_wf_cons_of_wf (by simpa [__smtx_dt_resolve] using hWf)
      simpa [__smtx_dt_resolve] using
        tp_ret_typeof_sel_rec_resolve_ne_reglan_of_cons_wf dd
          c d j hCons
  | SmtDatatype.sum c d, native_nat_succ i, j, hWf => by
      cases d with
      | null =>
          simp [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec]
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec
                (__smtx_dt_resolve (SmtDatatype.sum cTail dTail) dd)
                (SmtDatatype.sum cTail dTail) = true :=
            tp_dt_wf_tail_of_nonempty_tail_wf (by simpa [__smtx_dt_resolve] using hWf)
          simpa [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec] using
            tp_ret_typeof_sel_rec_resolve_ne_reglan_of_dt_wf dd
              (SmtDatatype.sum cTail dTail) i j hTail

private theorem tp_ret_typeof_sel_ne_reglan_of_datatype_wf
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    (hWf : __smtx_type_wf (SmtType.Datatype s d) = true) :
    __smtx_ret_typeof_sel s d i j ≠ SmtType.RegLan := by
  have hDtWf : __smtx_dt_wf_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d)
      (__smtx_dd_lookup s d) = true :=
    datatype_wf_rec_of_type_wf hWf
  simpa [__smtx_ret_typeof_sel] using
    tp_ret_typeof_sel_rec_resolve_ne_reglan_of_dt_wf d (__smtx_dd_lookup s d) i j hDtWf

private theorem tp_ret_typeof_sel_rec_resolve_ne_funtype_of_cons_wf
    (dd : SmtDatatypeDecl) :
    ∀ (c : SmtDatatypeCons) (d : SmtDatatype) (j : native_Nat),
      __smtx_dt_cons_wf_rec (__smtx_dtc_resolve c dd) c = true ->
        ∀ A B : SmtType,
          __smtx_ret_typeof_sel_rec
              (SmtDatatype.sum (__smtx_dtc_resolve c dd)
                (__smtx_dt_resolve d dd)) native_nat_zero j ≠
            SmtType.FunType A B
  | SmtDatatypeCons.unit, d, j, _hWf => by
      intro A B
      cases j <;> simp [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec]
  | SmtDatatypeCons.cons T c, d, native_nat_zero, hWf => by
      intro A B
      cases T
      case TypeRef r =>
        simp [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec]
      all_goals
        simp [__smtx_dtc_resolve, __smtx_dt_cons_wf_rec,
          __smtx_type_wf_rec,
          __smtx_ret_typeof_sel_rec, native_ite,
          native_and] at hWf ⊢
  | SmtDatatypeCons.cons T c, d, native_nat_succ j, hWf => by
      have hTail : __smtx_dt_cons_wf_rec (__smtx_dtc_resolve c dd) c = true := by
        cases T <;>
          exact tp_dt_cons_wf_rec_tail_of_true (by simpa [__smtx_dtc_resolve] using hWf)
      cases T <;>
        simpa [__smtx_dtc_resolve, __smtx_ret_typeof_sel_rec] using
          tp_ret_typeof_sel_rec_resolve_ne_funtype_of_cons_wf dd
            c d j hTail

private theorem tp_ret_typeof_sel_rec_resolve_ne_funtype_of_dt_wf
    (dd : SmtDatatypeDecl) :
    ∀ (d : SmtDatatype) (i j : native_Nat),
      __smtx_dt_wf_rec (__smtx_dt_resolve d dd) d = true ->
        ∀ A B : SmtType,
          __smtx_ret_typeof_sel_rec (__smtx_dt_resolve d dd) i j ≠
            SmtType.FunType A B
  | SmtDatatype.null, i, j, _hWf => by
      intro A B
      cases i <;> cases j <;>
        simp [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec]
  | SmtDatatype.sum c d, native_nat_zero, j, hWf => by
      have hCons : __smtx_dt_cons_wf_rec (__smtx_dtc_resolve c dd) c = true :=
        tp_dt_wf_cons_of_wf (by simpa [__smtx_dt_resolve] using hWf)
      simpa [__smtx_dt_resolve] using
        tp_ret_typeof_sel_rec_resolve_ne_funtype_of_cons_wf dd
          c d j hCons
  | SmtDatatype.sum c d, native_nat_succ i, j, hWf => by
      cases d with
      | null =>
          intro A B
          simp [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec]
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec
                (__smtx_dt_resolve (SmtDatatype.sum cTail dTail) dd)
                (SmtDatatype.sum cTail dTail) = true :=
            tp_dt_wf_tail_of_nonempty_tail_wf (by simpa [__smtx_dt_resolve] using hWf)
          simpa [__smtx_dt_resolve, __smtx_ret_typeof_sel_rec] using
            tp_ret_typeof_sel_rec_resolve_ne_funtype_of_dt_wf dd
              (SmtDatatype.sum cTail dTail) i j hTail

private theorem tp_ret_typeof_sel_ne_funtype_of_datatype_wf
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    (hWf : __smtx_type_wf (SmtType.Datatype s d) = true) :
    ∀ A B : SmtType, __smtx_ret_typeof_sel s d i j ≠ SmtType.FunType A B := by
  have hDtWf : __smtx_dt_wf_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d)
      (__smtx_dd_lookup s d) = true :=
    datatype_wf_rec_of_type_wf hWf
  simpa [__smtx_ret_typeof_sel] using
    tp_ret_typeof_sel_rec_resolve_ne_funtype_of_dt_wf d (__smtx_dd_lookup s d) i j hDtWf

-/

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

/-- Extracts inhabitation of the `seq_nth` result type from a non-`None` typing judgment. -/
theorem seq_nth_term_inhabited_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2)) :
    type_inhabited (__smtx_typeof (SmtTerm.seq_nth t1 t2)) := by
  rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_seq_nth_eq t1 t2] at ht
    simpa [__smtx_typeof_seq_nth, h1, h2] using ht
  have hTy :
      __smtx_typeof (SmtTerm.seq_nth t1 t2) = T := by
    have hGuard : __smtx_typeof_guard_wf T T = T :=
      smtx_typeof_guard_wf_of_non_none T T hGuardNN
    rw [typeof_seq_nth_eq t1 t2]
    simpa [__smtx_typeof_seq_nth, h1, h2] using hGuard
  rw [hTy]
  exact smtx_typeof_guard_wf_inhabited_of_non_none T T hGuardNN

/-- Extracts recursive well-formedness of the element type used by `seq_nth`. -/
theorem seq_nth_elem_wf_rec_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2)) :
    ∀ {T : SmtType},
      __smtx_typeof t1 = SmtType.Seq T ->
        __smtx_type_wf_rec T = true := by
  intro T h1
  exact tp_smt_seq_component_wf_rec_of_non_none_type t1 T h1

/-- Extracts inhabitation of the `dt_sel` result type from a non-`None` typing judgment. -/
theorem dt_sel_term_inhabited_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner :=
    __smtx_typeof_apply
      (SmtType.FunType (SmtType.Datatype s d) R)
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
    simpa [D] using tp_smt_datatype_wf_of_non_none_type x s d hxTy
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
      native_inhabited_type R = true ∧
        __smtx_type_wf_rec R = true :=
    tp_type_wf_parts_of_wf_ne_reglan hRWf hRNe hRNeFun
  have hDTParts :
      native_inhabited_type D = true ∧
        __smtx_type_wf_rec D = true :=
    tp_type_wf_parts_of_wf_ne_reglan hDTWf (by simp [D]) (by
      intro A B h
      simp [D] at h)
  have hRInh : type_inhabited R :=
    type_inhabited_of_type_wf R hRWf
  have hM3Inh : type_inhabited M3 := by
    exact tp_map_type_inhabited (A := D) (B := R) hRInh
  have hM3InhBool : native_inhabited_type M3 = true :=
    native_inhabited_type_map hRParts.1
  have hM3Rec : __smtx_type_wf_rec M3 = true := by
    simp [M3, __smtx_type_wf_rec, native_and, hDTParts.1,
      hDTParts.2, hRParts.1, hRParts.2]
  have hM2Inh : type_inhabited M2 := by
    exact tp_map_type_inhabited (A := SmtType.Int) (B := M3) hM3Inh
  have hM2InhBool : native_inhabited_type M2 = true :=
    native_inhabited_type_map hM3InhBool
  have hM2Rec : __smtx_type_wf_rec M2 = true := by
    simp [M2, __smtx_type_wf_rec, native_and,
      hM3InhBool, hM3Rec]
  have hM1Inh : type_inhabited M1 := by
    exact tp_map_type_inhabited (A := SmtType.Int) (B := M2) hM2Inh
  have hM1InhBool : native_inhabited_type M1 = true :=
    native_inhabited_type_map hM2InhBool
  have hM1Rec : __smtx_type_wf_rec M1 = true := by
    simp [M1, __smtx_type_wf_rec, native_and,
      hM2InhBool, hM2Rec]
  simpa [M1, M2, M3, D, R] using
    type_wf_of_inhabited_and_wf_rec hM1InhBool hM1Rec

/-- Builds support for `seq_unit` directly from support of its argument and a non-`None` typing judgment. -/
private theorem seq_unit_arg_non_none_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_unit t)) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type at ht ⊢
  by_cases hNone : __smtx_typeof t = SmtType.None
  · exfalso
    apply ht
    simp [__smtx_typeof, hNone, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_rec, native_and, native_ite]
  · exact hNone

private theorem set_singleton_arg_non_none_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.set_singleton t)) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type at ht ⊢
  by_cases hNone : __smtx_typeof t = SmtType.None
  · exfalso
    apply ht
    simp [__smtx_typeof, hNone, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_rec, native_and, native_ite]
  · exact hNone

theorem supported_seq_unit_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_unit t))
    (hs : supported_preservation_term t) :
    supported_preservation_term (SmtTerm.seq_unit t) := by
  have htArg : term_has_non_none_type t :=
    seq_unit_arg_non_none_of_non_none ht
  exact supported_preservation_term.seq_unit htArg hs

/-- Builds support for `set_singleton` directly from support of its argument and a non-`None` typing judgment. -/
theorem supported_set_singleton_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.set_singleton t))
    (hs : supported_preservation_term t) :
    supported_preservation_term (SmtTerm.set_singleton t) := by
  have htArg : term_has_non_none_type t :=
    set_singleton_arg_non_none_of_non_none ht
  exact supported_preservation_term.set_singleton htArg hs

/-- Builds support for `seq_nth` directly from support of its arguments and a non-`None` typing judgment. -/
theorem supported_seq_nth_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2))
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2)
    (hElemRec :
      ∀ {T : SmtType},
        __smtx_typeof t1 = SmtType.Seq T ->
          __smtx_type_wf_rec T = true) :
    supported_preservation_term (SmtTerm.seq_nth t1 t2) := by
  rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
  have ht1 : term_has_non_none_type t1 :=
    term_has_non_none_of_type_eq h1 (by simp)
  have ht2 : term_has_non_none_type t2 :=
    term_has_non_none_of_type_eq h2 (by simp)
  exact supported_preservation_term.seq_nth
    ht1 hs1 ht2 hs2 (seq_nth_term_inhabited_of_non_none ht) hElemRec

/-- Builds support for datatype-selector applications directly from support of the argument. -/
theorem supported_dt_sel_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
    (hWrongMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true)
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) := by
  have htx : term_has_non_none_type x :=
    term_has_non_none_of_type_eq (dt_sel_arg_datatype_of_non_none ht) (by simp)
  exact supported_preservation_term.dt_sel
    ht (dt_sel_term_inhabited_of_non_none ht) hWrongMapWF htx hsx

/-- Builds support for applications directly from support of their subterms and a non-`None` typing judgment. -/
theorem supported_apply_of_non_none
    {f x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hsf : supported_preservation_term f)
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply f x) := by
  by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
  · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
    exact supported_dt_sel_of_non_none ht
      (dt_sel_wrong_map_type_wf_of_non_none ht) hsx
  · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
    · rcases hTesterWitness with ⟨s, d, i, rfl⟩
      exact supported_preservation_term.dt_tester s d i x
    · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
        intro s d i j hEq
        exact hSelWitness ⟨s, d, i, j, hEq⟩
      have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
        intro s d i hEq
        exact hTesterWitness ⟨s, d, i, hEq⟩
      have hTy : generic_apply_type f x :=
        generic_apply_type_of_non_datatype_head hSel hTester
      have hEval : generic_apply_eval f x :=
        generic_apply_eval_of_non_datatype_head hSel hTester
      have hTyEq :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTyEq]
        exact hNone
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have htf : term_has_non_none_type f := by
        rcases hF with hFun | hDtc
        · exact term_has_non_none_of_type_eq hFun (by simp)
        · exact term_has_non_none_of_type_eq hDtc (by simp)
      have htx : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hX hA
      exact supported_preservation_term.apply hTy hEval htf hsf htx hsx

private theorem bool_unop_arg_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, native_ite, native_Teq, h] at ht
  simp

@[expose] def type_has_no_none_components : SmtType -> Prop
  | SmtType.None => False
  | SmtType.TypeRef _ => False
  | SmtType.Seq A => type_has_no_none_components A
  | SmtType.Set A => type_has_no_none_components A
  | SmtType.Map A B => type_has_no_none_components A ∧
      type_has_no_none_components B
  | SmtType.FunType A B => type_has_no_none_components A ∧
      type_has_no_none_components B
  | SmtType.DtcAppType A B => type_has_no_none_components A ∧
      type_has_no_none_components B
  | _ => True

private theorem type_has_no_none_components_of_wf :
    {T : SmtType} ->
    __smtx_type_wf T = true ->
    type_has_no_none_components T
  | SmtType.None, h => by
      simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h
  | SmtType.Bool, _ => by
      simp [type_has_no_none_components]
  | SmtType.Int, _ => by
      simp [type_has_no_none_components]
  | SmtType.Real, _ => by
      simp [type_has_no_none_components]
  | SmtType.RegLan, _ => by
      simp [type_has_no_none_components]
  | SmtType.BitVec _, _ => by
      simp [type_has_no_none_components]
  | SmtType.Map A B, h => by
      rcases map_type_wf_components_of_wf h with ⟨hA, hB⟩
      exact ⟨type_has_no_none_components_of_wf (T := A) hA,
        type_has_no_none_components_of_wf (T := B) hB⟩
  | SmtType.Set A, h => by
      exact type_has_no_none_components_of_wf (T := A) (set_type_wf_component_of_wf h)
  | SmtType.Seq A, h => by
      exact type_has_no_none_components_of_wf (T := A) (seq_type_wf_component_of_wf h)
  | SmtType.Char, _ => by
      simp [type_has_no_none_components]
  | SmtType.Datatype _ _, _ => by
      simp [type_has_no_none_components]
  | SmtType.TypeRef _, h => by
      simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h
  | SmtType.USort _, _ => by
      simp [type_has_no_none_components]
  | SmtType.FunType A B, h => by
      rcases fun_type_wf_components_of_wf h with ⟨hA, hB⟩
      exact ⟨type_has_no_none_components_of_wf (T := A) hA,
        type_has_no_none_components_of_wf (T := B) hB⟩
  | SmtType.DtcAppType _ _, h => by
      simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h
termination_by T => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

private theorem type_has_no_none_components_of_wf_rec :
    {U : SmtType} ->
    __smtx_type_wf_rec U = true ->
    type_has_no_none_components U
  | SmtType.None, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.Bool, _ => by
      simp [type_has_no_none_components]
  | SmtType.Int, _ => by
      simp [type_has_no_none_components]
  | SmtType.Real, _ => by
      simp [type_has_no_none_components]
  | SmtType.RegLan, _ => by
      simp [type_has_no_none_components]
  | SmtType.BitVec _, _ => by
      simp [type_has_no_none_components]
  | SmtType.Map A B, h => by
      have h' :
          (native_inhabited_type A = true ∧
            __smtx_type_wf_rec A = true) ∧
            (native_inhabited_type B = true ∧
              __smtx_type_wf_rec B = true) := by
        simpa [__smtx_type_wf_rec, native_and] using h
      exact ⟨type_has_no_none_components_of_wf_rec (U := A) h'.1.2,
        type_has_no_none_components_of_wf_rec (U := B) h'.2.2⟩
  | SmtType.Set A, h => by
      have hA :
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      exact type_has_no_none_components_of_wf_rec (U := A) hA.2
  | SmtType.Seq A, h => by
      have hA :
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      exact type_has_no_none_components_of_wf_rec (U := A) hA.2
  | SmtType.Char, _ => by
      simp [type_has_no_none_components]
  | SmtType.Datatype _ _, _ => by
      simp [type_has_no_none_components]
  | SmtType.TypeRef _, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.USort _, _ => by
      simp [type_has_no_none_components]
  | SmtType.FunType _ _, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.DtcAppType _ _, h => by
      simp [__smtx_type_wf_rec] at h
termination_by U => sizeOf U
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

theorem type_has_no_none_components_non_none
    {T : SmtType}
    (h : type_has_no_none_components T) :
    T ≠ SmtType.None := by
  cases T <;> simp [type_has_no_none_components] at h ⊢

private theorem type_has_no_none_components_set_component_non_none
    {A : SmtType}
    (h : type_has_no_none_components (SmtType.Set A)) :
    A ≠ SmtType.None :=
  type_has_no_none_components_non_none h

private theorem type_has_no_none_components_map_components_non_none
    {A B : SmtType}
    (h : type_has_no_none_components (SmtType.Map A B)) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  exact ⟨type_has_no_none_components_non_none h.1,
    type_has_no_none_components_non_none h.2⟩

theorem type_has_no_none_components_fun_components_non_none
    {A B : SmtType}
    (h : type_has_no_none_components (SmtType.FunType A B)) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  exact ⟨type_has_no_none_components_non_none h.1,
    type_has_no_none_components_non_none h.2⟩

theorem type_has_no_none_components_dtc_app_components_non_none
    {A B : SmtType}
    (h : type_has_no_none_components (SmtType.DtcAppType A B)) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  exact ⟨type_has_no_none_components_non_none h.1,
    type_has_no_none_components_non_none h.2⟩

private theorem guard_wf_type_has_no_none_components_of_non_none
    {T U : SmtType}
    (hU : type_has_no_none_components U)
    (hNN : __smtx_typeof_guard_wf T U ≠ SmtType.None) :
    type_has_no_none_components (__smtx_typeof_guard_wf T U) := by
  have hGuard : __smtx_typeof_guard_wf T U = U :=
    smtx_typeof_guard_wf_of_non_none T U hNN
  simpa [hGuard] using hU

private theorem var_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.Var s T)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.Var s T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  simpa [__smtx_typeof] using
    guard_wf_type_has_no_none_components_of_non_none
      (type_has_no_none_components_of_wf hWf) hGuardNN

private theorem uconst_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.UConst s T)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.UConst s T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  simpa [__smtx_typeof] using
    guard_wf_type_has_no_none_components_of_non_none
      (type_has_no_none_components_of_wf hWf) hGuardNN

private theorem seq_empty_type_has_no_none_components_of_non_none
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.seq_empty T)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.seq_empty T)) := by
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hWf : __smtx_type_wf (SmtType.Seq T) = true :=
    smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuardNN
  simpa [__smtx_typeof] using
    guard_wf_type_has_no_none_components_of_non_none
      (by
        have hGoodT : type_has_no_none_components (SmtType.Seq T) :=
          type_has_no_none_components_of_wf hWf
        exact hGoodT) hGuardNN

private theorem set_empty_type_has_no_none_components_of_non_none
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.set_empty T)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.set_empty T)) := by
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hWf : __smtx_type_wf (SmtType.Set T) = true :=
    smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuardNN
  simpa [__smtx_typeof] using
    guard_wf_type_has_no_none_components_of_non_none
      (by
        have hGoodT : type_has_no_none_components (SmtType.Set T) :=
          type_has_no_none_components_of_wf hWf
        exact hGoodT) hGuardNN

private theorem choice_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.choice s T body)) := by
  have hTy : __smtx_typeof (SmtTerm.choice s T body) = T :=
    choice_term_typeof_of_non_none ht
  have hGuardTy :
      __smtx_typeof (SmtTerm.choice s T body) = __smtx_typeof_guard_wf T T :=
    choice_term_guard_type_of_non_none ht
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    rw [← hGuardTy]
    exact ht
  have hWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  rw [hTy]
  exact type_has_no_none_components_of_wf hWf

private theorem supported_apply_term_of_non_none
    {f x : SmtTerm}
    (ihf : term_has_non_none_type f -> supported_preservation_term f)
    (ihx : term_has_non_none_type x -> supported_preservation_term x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x)) :
    supported_preservation_term (SmtTerm.Apply f x) := by
  by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
  · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
    have htx : term_has_non_none_type x :=
      term_has_non_none_of_type_eq (dt_sel_arg_datatype_of_non_none ht) (by simp)
    exact supported_dt_sel_of_non_none ht
      (dt_sel_wrong_map_type_wf_of_non_none ht) (ihx htx)
  · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
    · rcases hTesterWitness with ⟨s, d, i, rfl⟩
      exact supported_preservation_term.dt_tester s d i x
    · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
        intro s d i j hEq
        exact hSelWitness ⟨s, d, i, j, hEq⟩
      have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
        intro s d i hEq
        exact hTesterWitness ⟨s, d, i, hEq⟩
      have hTy : generic_apply_type f x :=
        generic_apply_type_of_non_datatype_head hSel hTester
      have hEval : generic_apply_eval f x :=
        generic_apply_eval_of_non_datatype_head hSel hTester
      have hTyEq :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTyEq]
        exact hNone
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have htf : term_has_non_none_type f := by
        rcases hF with hFun | hDtc
        · exact term_has_non_none_of_type_eq hFun (by simp)
        · exact term_has_non_none_of_type_eq hDtc (by simp)
      have htx : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hX hA
      exact supported_preservation_term.apply
        hTy hEval htf (ihf htf) htx (ihx htx)


/-- Builds support for `ite` directly from support of its subterms and a non-`None` typing judgment. -/
theorem supported_ite_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2))
    (hsc : supported_preservation_term c)
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2) :
    supported_preservation_term (SmtTerm.ite c t1 t2) := by
  rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, _hT⟩
  have htc : term_has_non_none_type c :=
    term_has_non_none_of_type_eq hc (by simp)
  have ht1 : term_has_non_none_type t1 :=
    term_has_non_none_of_type_eq h1 _hT
  have ht2 : term_has_non_none_type t2 :=
    term_has_non_none_of_type_eq h2 _hT
  exact supported_preservation_term.ite htc hsc ht1 hs1 ht2 hs2

/-- Builds support for `select` directly from support of its subterms and a non-`None` typing judgment. -/
private theorem supported_select_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.select t1 t2))
    (hMapTy : type_has_no_none_components (__smtx_typeof t1))
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2) :
    supported_preservation_term (SmtTerm.select t1 t2) := by
  rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  have hMapNN : A ≠ SmtType.None ∧ B ≠ SmtType.None :=
    type_has_no_none_components_map_components_non_none hMapTy'
  have ht1 : term_has_non_none_type t1 :=
    term_has_non_none_of_type_eq h1 (by simp)
  have ht2 : term_has_non_none_type t2 :=
    term_has_non_none_of_type_eq h2 hMapNN.1
  exact supported_preservation_term.select ht1 hs1 ht2 hs2

/-- Builds support for `store` directly from support of its subterms and a non-`None` typing judgment. -/
private theorem supported_store_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.store t1 t2 t3))
    (hMapTy : type_has_no_none_components (__smtx_typeof t1))
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2)
    (hs3 : supported_preservation_term t3) :
    supported_preservation_term (SmtTerm.store t1 t2 t3) := by
  rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  have hMapNN : A ≠ SmtType.None ∧ B ≠ SmtType.None :=
    type_has_no_none_components_map_components_non_none hMapTy'
  have ht1 : term_has_non_none_type t1 :=
    term_has_non_none_of_type_eq h1 (by simp)
  have ht2 : term_has_non_none_type t2 :=
    term_has_non_none_of_type_eq h2 hMapNN.1
  have ht3 : term_has_non_none_type t3 :=
    term_has_non_none_of_type_eq h3 hMapNN.2
  exact supported_preservation_term.store ht1 hs1 ht2 hs2 ht3 hs3

private theorem type_default_typed_canonical_of_map_domain_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    __smtx_typeof_value (__smtx_type_default A) = A ∧
      value_canonical (__smtx_type_default A) := by
  have hAll :
      native_inhabited_type (SmtType.Map A B) = true ∧
        ((native_inhabited_type A = true ∧
          __smtx_type_wf_rec A = true) ∧
          (native_inhabited_type B = true ∧
            __smtx_type_wf_rec B = true)) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] using h
  exact type_default_typed_canonical_of_inhabited_wf_rec A hAll.2.1.1 hAll.2.1.2

private theorem type_default_typed_canonical_of_set_element_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    __smtx_typeof_value (__smtx_type_default A) = A ∧
      value_canonical (__smtx_type_default A) := by
  have hAll :
      native_inhabited_type (SmtType.Set A) = true ∧
        (native_inhabited_type A = true ∧
          __smtx_type_wf_rec A = true) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] using h
  exact type_default_typed_canonical_of_inhabited_wf_rec A hAll.2.1 hAll.2.2

private theorem map_diff_default_typed_canonical_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.map_diff t1 t2)) :
    ∀ {A : SmtType},
      __smtx_typeof (SmtTerm.map_diff t1 t2) = A ->
        __smtx_typeof_value (__smtx_type_default A) = A ∧
          value_canonical (__smtx_type_default A) := by
  intro A hA
  rcases map_diff_args_of_non_none ht with hMap | hSet
  · rcases hMap with ⟨D, R, h1, h2, hRes⟩
    have ht1 : term_has_non_none_type t1 :=
      term_has_non_none_of_type_eq h1 (by simp)
    have hGood := tp_smt_term_result_seq_components_wf_of_non_none t1 ht1
    have hMapWf : __smtx_type_wf (SmtType.Map D R) = true := by
      simpa [h1, tp_result_seq_components_wf] using hGood
    have hDA : D = A := hRes.symm.trans hA
    rw [← hDA]
    exact type_default_typed_canonical_of_map_domain_wf hMapWf
  · rcases hSet with ⟨D, h1, h2, hRes⟩
    have ht1 : term_has_non_none_type t1 :=
      term_has_non_none_of_type_eq h1 (by simp)
    have hGood := tp_smt_term_result_seq_components_wf_of_non_none t1 ht1
    have hSetWf : __smtx_type_wf (SmtType.Set D) = true := by
      simpa [h1, tp_result_seq_components_wf] using hGood
    have hDA : D = A := hRes.symm.trans hA
    rw [← hDA]
    exact type_default_typed_canonical_of_set_element_wf hSetWf

private theorem binary_type_has_no_none_components_of_non_none
    {w n : native_Int}
    (ht : term_has_non_none_type (SmtTerm.Binary w n)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.Binary w n)) := by
  unfold term_has_non_none_type at ht
  unfold __smtx_typeof at ht ⊢
  cases hWidth : native_zleq 0 w <;>
    simp [native_ite, SmtEval.native_and, hWidth] at ht ⊢
  cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
    simp [hMod, type_has_no_none_components] at ht ⊢

private theorem seq_unit_type_has_no_none_components_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_unit t))
    (hTy : type_has_no_none_components (__smtx_typeof t)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.seq_unit t)) := by
  rw [__smtx_typeof.eq_def] <;> simp only
  have hGuard :
      __smtx_typeof_guard_wf (SmtType.Seq (__smtx_typeof t))
          (SmtType.Seq (__smtx_typeof t)) =
        SmtType.Seq (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Seq (__smtx_typeof t))
      (SmtType.Seq (__smtx_typeof t)) (by
        unfold term_has_non_none_type at ht
        simpa [__smtx_typeof] using ht)
  rw [hGuard]
  simpa [type_has_no_none_components] using hTy

private theorem set_singleton_type_has_no_none_components_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.set_singleton t))
    (hTy : type_has_no_none_components (__smtx_typeof t)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.set_singleton t)) := by
  rw [__smtx_typeof.eq_def] <;> simp only
  have hGuard :
      __smtx_typeof_guard_wf (SmtType.Set (__smtx_typeof t))
          (SmtType.Set (__smtx_typeof t)) =
        SmtType.Set (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Set (__smtx_typeof t))
      (SmtType.Set (__smtx_typeof t)) (by
        unfold term_has_non_none_type at ht
        simpa [__smtx_typeof] using ht)
  rw [hGuard]
  simpa [type_has_no_none_components] using hTy

private theorem seq_nth_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.seq_nth t1 t2)) := by
  rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  have hT : type_has_no_none_components T := by
    simpa [type_has_no_none_components] using hSeqTy'
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_seq_nth_eq t1 t2] at ht
    simpa [__smtx_typeof_seq_nth, h1, h2] using ht
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T hGuardNN
  rw [typeof_seq_nth_eq]
  simpa [__smtx_typeof_seq_nth, h1, h2, hGuard] using hT

private theorem ite_type_has_no_none_components_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2))
    (hTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.ite c t1 t2)) := by
  rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, _hT⟩
  have hT : type_has_no_none_components T := by
    simpa [h1] using hTy
  rw [typeof_ite_eq]
  simpa [__smtx_typeof_ite, native_ite, native_Teq, hc, h1, h2] using hT

private theorem select_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.select t1 t2))
    (hMapTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.select t1 t2)) := by
  rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  rw [typeof_select_eq]
  simpa [__smtx_typeof_select, native_ite, native_Teq, h1, h2] using hMapTy'.2

private theorem store_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.store t1 t2 t3))
    (hMapTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.store t1 t2 t3)) := by
  rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  rw [typeof_store_eq]
  simpa [__smtx_typeof_store, native_ite, native_Teq, h1, h2, h3] using hMapTy'

private theorem map_diff_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.map_diff t1 t2))
    (hTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.map_diff t1 t2)) := by
  rcases map_diff_args_of_non_none ht with hMap | hSet
  · rcases hMap with ⟨A, B, h1, h2, hRes⟩
    have hMapTy : type_has_no_none_components (SmtType.Map A B) := by
      simpa [h1] using hTy
    rw [hRes]
    exact hMapTy.1
  · rcases hSet with ⟨A, h1, h2, hRes⟩
    have hSetTy : type_has_no_none_components (SmtType.Set A) := by
      simpa [h1] using hTy
    rw [hRes]
    simpa [type_has_no_none_components] using hSetTy

private theorem dt_wf_cons_of_wf
    {dd : SmtDatatypeDecl} {c : SmtDatatypeCons} {d : SmtDatatype}
    (h : __smtx_dt_wf_rec dd (SmtDatatype.sum c d) = true) :
    __smtx_dt_cons_wf_rec dd c = true :=
  tp_dt_wf_cons_of_wf h

private theorem dt_wf_tail_of_nonempty_tail_wf
    {dd : SmtDatatypeDecl} {c cTail : SmtDatatypeCons} {dTail : SmtDatatype}
    (h : __smtx_dt_wf_rec dd
        (SmtDatatype.sum c (SmtDatatype.sum cTail dTail)) = true) :
    __smtx_dt_wf_rec dd (SmtDatatype.sum cTail dTail) = true :=
  tp_dt_wf_tail_of_nonempty_tail_wf h

private theorem dt_cons_wf_tail_of_wf
    {dd : SmtDatatypeDecl} {T : SmtType} {c : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec dd (SmtDatatypeCons.cons T c) = true) :
    __smtx_dt_cons_wf_rec dd c = true :=
  tp_dt_cons_wf_rec_tail_of_true h

private theorem typeof_dt_cons_value_rec_zero_has_no_none_components_of_cons_wf
    {s : native_String}
    {dd : SmtDatatypeDecl} :
    ∀ (c : SmtDatatypeCons) (dF : SmtDatatype),
      __smtx_dt_cons_wf_rec dd c = true ->
      type_has_no_none_components
        (__smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s dd)
          (SmtDatatype.sum (__smtx_dtc_resolve c dd) dF)
          0)
  | SmtDatatypeCons.unit, dF, _ => by
      simp [__smtx_dtc_resolve, __smtx_typeof_dt_cons_value_rec, type_has_no_none_components]
  | SmtDatatypeCons.cons T c, dF, h => by
      have hTail : __smtx_dt_cons_wf_rec dd c = true :=
        dt_cons_wf_tail_of_wf h
      have hTailTy :
          type_has_no_none_components
            (__smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s dd)
              (SmtDatatype.sum (__smtx_dtc_resolve c dd) dF)
              0) :=
        typeof_dt_cons_value_rec_zero_has_no_none_components_of_cons_wf c dF hTail
      cases T with
      | TypeRef r =>
          simpa [__smtx_dtc_resolve, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components] using hTailTy
      | Seq A =>
          have hW : __smtx_type_wf_rec (SmtType.Seq A) = true := by
            simp only [__smtx_dt_cons_wf_rec, native_and, Bool.and_eq_true] at h
            exact h.1.2
          have hHeadTy := type_has_no_none_components_of_wf_rec hW
          simpa [__smtx_dtc_resolve, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components] using And.intro hHeadTy hTailTy
      | Set A =>
          have hW : __smtx_type_wf_rec (SmtType.Set A) = true := by
            simp only [__smtx_dt_cons_wf_rec, native_and, Bool.and_eq_true] at h
            exact h.1.2
          have hHeadTy := type_has_no_none_components_of_wf_rec hW
          simpa [__smtx_dtc_resolve, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components] using And.intro hHeadTy hTailTy
      | Map A B =>
          have hW : __smtx_type_wf_rec (SmtType.Map A B) = true := by
            simp only [__smtx_dt_cons_wf_rec, native_and, Bool.and_eq_true] at h
            exact h.1.2
          have hHeadTy := type_has_no_none_components_of_wf_rec hW
          simpa [__smtx_dtc_resolve, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components] using And.intro hHeadTy hTailTy
      | None =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_and] at h
      | FunType A B =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_and] at h
      | DtcAppType A B =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_and] at h
      | _ =>
          simpa [__smtx_dtc_resolve, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components] using hTailTy

  private theorem typeof_dt_cons_value_rec_has_no_none_components_of_non_none
    {s : native_String}
    {dd : SmtDatatypeDecl} :
    ∀ {d : SmtDatatype} {i : Nat},
      __smtx_dt_wf_rec dd d = true ->
      __smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s dd)
          (__smtx_dt_resolve d dd) i ≠ SmtType.None ->
      type_has_no_none_components
        (__smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s dd)
          (__smtx_dt_resolve d dd) i)
  | SmtDatatype.null, i, _, hNN => by
      cases i <;> simp [__smtx_dt_resolve, __smtx_typeof_dt_cons_value_rec,
        __smtx_typeof_dt_cons_value_rec] at hNN ⊢
  | SmtDatatype.sum c d, 0, hWf, _ => by
      have hc : __smtx_dt_cons_wf_rec dd c = true :=
        dt_wf_cons_of_wf hWf
      simpa [__smtx_dt_resolve] using
        typeof_dt_cons_value_rec_zero_has_no_none_components_of_cons_wf
          c (__smtx_dt_resolve d dd) hc
  | SmtDatatype.sum c d, Nat.succ i, hWf, hNN => by
      cases d with
      | null =>
          simp [__smtx_typeof_dt_cons_value_rec, __smtx_dt_resolve] at hNN
      | sum cTail dTail =>
          have hd :
              __smtx_dt_wf_rec dd (SmtDatatype.sum cTail dTail) = true :=
            dt_wf_tail_of_nonempty_tail_wf hWf
          have hNN' :
              __smtx_typeof_dt_cons_value_rec
                  (SmtType.Datatype s dd)
                  (__smtx_dt_resolve (SmtDatatype.sum cTail dTail) dd) i ≠
                SmtType.None := by
            simpa [__smtx_typeof_dt_cons_value_rec, __smtx_dt_resolve] using hNN
          simpa [__smtx_typeof_dt_cons_value_rec, __smtx_dt_resolve] using
            typeof_dt_cons_value_rec_has_no_none_components_of_non_none
              (d := SmtDatatype.sum cTail dTail) (i := i) hd hNN'

private theorem dt_cons_type_has_no_none_components_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    (ht : term_has_non_none_type (SmtTerm.DtCons s d i)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.DtCons s d i)) := by
  have hGuardNN :
      __smtx_typeof_guard_wf (SmtType.Datatype s d)
        (__smtx_typeof_dt_cons_rec
          (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) ≠
        SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [typeof_dt_cons_eq] using ht
  have hBaseWf : __smtx_dt_wf_rec d (__smtx_dd_lookup s d) = true := by
    have hWf : __smtx_type_wf (SmtType.Datatype s d) = true :=
      smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Datatype s d)
        (__smtx_typeof_dt_cons_rec
          (SmtType.Datatype s d)
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) hGuardNN
    exact datatype_wf_rec_of_type_wf hWf
  have hInnerNN :
      __smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i ≠
        SmtType.None := by
    rw [typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]
    intro hNone
    apply hGuardNN
    rw [smtx_typeof_guard_wf_of_non_none
      (SmtType.Datatype s d)
      (__smtx_typeof_dt_cons_rec
        (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) hGuardNN, hNone]
  have hInnerTy :
      type_has_no_none_components
        (__smtx_typeof_dt_cons_rec
          (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) := by
    rw [← typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]
    exact typeof_dt_cons_value_rec_has_no_none_components_of_non_none
      hBaseWf hInnerNN
  rw [typeof_dt_cons_eq]
  exact guard_wf_type_has_no_none_components_of_non_none hInnerTy hGuardNN

private theorem dt_sel_type_has_no_none_components_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type ((SmtTerm.DtSel s d i j).Apply x)) :
    type_has_no_none_components (__smtx_typeof ((SmtTerm.DtSel s d i j).Apply x)) := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner :=
    __smtx_typeof_apply
      (SmtType.FunType (SmtType.Datatype s d) R)
      (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_dt_sel_apply_eq] at ht
    simpa [R, inner] using ht
  have hWf : __smtx_type_wf R = true :=
    smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
  rw [dt_sel_term_typeof_of_non_none ht]
  exact type_has_no_none_components_of_wf hWf

private theorem dt_tester_type_has_no_none_components_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type ((SmtTerm.DtTester s d i).Apply x)) :
    type_has_no_none_components (__smtx_typeof ((SmtTerm.DtTester s d i).Apply x)) := by
  rw [dt_tester_term_typeof_of_non_none ht]
  simp [type_has_no_none_components]

private theorem apply_type_has_no_none_components_of_non_none
    {f x : SmtTerm}
    (hTy : generic_apply_type f x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hFunTy : type_has_no_none_components (__smtx_typeof f)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.Apply f x)) := by
  have hTyEq :
      __smtx_typeof (SmtTerm.Apply f x) =
        __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
    unfold generic_apply_type at hTy
    exact hTy
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    intro hNone
    apply ht
    rw [hTyEq]
    exact hNone
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
  rcases hF with hFun | hDtc
  ·
      have hFunTy' : type_has_no_none_components (SmtType.FunType A B) := by
        simpa [hFun] using hFunTy
      rw [hTyEq]
      simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hFun, hX, hA]
        using hFunTy'.2
  ·
      have hDtcTy' : type_has_no_none_components (SmtType.DtcAppType A B) := by
        simpa [hDtc] using hFunTy
      rw [hTyEq]
      simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hDtc, hX, hA]
        using hDtcTy'.2

private theorem seq_op_1_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_seq_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases seq_arg_of_non_none (op := op) hTy ht with ⟨T, hArg⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [hArg] using hSeqTy
  rw [hTy]
  simpa [__smtx_typeof_seq_op_1, native_ite, native_Teq, hArg, type_has_no_none_components]
    using hSeqTy'

private theorem seq_op_2_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_seq_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases seq_binop_args_of_non_none (op := op) hTy ht with ⟨T, h1, h2⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [hTy]
  simpa [__smtx_typeof_seq_op_2, native_ite, native_Teq, h1, h2, type_has_no_none_components]
    using hSeqTy'

private theorem seq_op_3_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2 t3) =
        __smtx_typeof_seq_op_3 (__smtx_typeof t1) (__smtx_typeof t2)
          (__smtx_typeof t3))
    (ht : term_has_non_none_type (op t1 t2 t3))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2 t3)) := by
  rcases seq_triop_args_of_non_none (op := op) hTy ht with ⟨T, h1, h2, h3⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [hTy]
  simpa [__smtx_typeof_seq_op_3, native_ite, native_Teq, h1, h2, h3,
    type_has_no_none_components] using hSeqTy'
private theorem set_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_sets_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2))
    (hSetTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases set_binop_args_of_non_none (op := op) hTy ht with ⟨A, h1, h2⟩
  have hSetTy' : type_has_no_none_components (SmtType.Set A) := by
    simpa [h1] using hSetTy
  rw [hTy]
  simpa [__smtx_typeof_sets_op_2, native_ite, native_Teq, h1, h2, type_has_no_none_components]
    using hSetTy'

private theorem str_substr_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_substr t1 t2 t3))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_substr t1 t2 t3)) := by
  rcases str_substr_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [typeof_str_substr_eq]
  simpa [__smtx_typeof_str_substr, h1, h2, h3, type_has_no_none_components] using hSeqTy'

private theorem str_at_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_at t1 t2))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_at t1 t2)) := by
  rcases str_at_args_of_non_none ht with ⟨T, h1, h2⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [typeof_str_at_eq]
  simpa [__smtx_typeof_str_at, h1, h2, type_has_no_none_components] using hSeqTy'

private theorem str_update_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_update t1 t2 t3))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_update t1 t2 t3)) := by
  rcases str_update_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [typeof_str_update_eq]
  simpa [__smtx_typeof_str_update, native_ite, native_Teq, h1, h2, h3,
    type_has_no_none_components] using hSeqTy'

private theorem str_replace_re_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2 t3) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof t3) (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2 t3)) := by
  have hArgs := str_replace_re_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2, type_has_no_none_components]

private theorem bool_unop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.Bool := bool_unop_arg_of_non_none hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArg, type_has_no_none_components]

private theorem bool_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := bool_binop_args_bool_of_non_none hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2, type_has_no_none_components]

private theorem arith_unop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_arith_overload_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases arith_unop_arg_of_non_none hTy ht with hArg | hArg
  · rw [hTy]
    simp [__smtx_typeof_arith_overload_op_1, hArg, type_has_no_none_components]
  · rw [hTy]
    simp [__smtx_typeof_arith_overload_op_1, hArg, type_has_no_none_components]

private theorem arith_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases arith_binop_args_of_non_none (op := op) hTy ht with hArgs | hArgs
  · rw [hTy]
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2, type_has_no_none_components]
  · rw [hTy]
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2, type_has_no_none_components]

private theorem arith_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) R)
    (ht : term_has_non_none_type (op t1 t2))
    (hR : type_has_no_none_components R) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases arith_binop_ret_args_of_non_none (op := op) hTy ht with hArgs | hArgs
  · rw [hTy]
    simpa [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2] using hR
  · rw [hTy]
    simpa [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2] using hR

private theorem int_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Int) ret SmtType.None)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_arg_of_non_none_ret (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArg] using hRet

private theorem int_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) ret SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := int_binop_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArgs.1, hArgs.2] using hRet

private theorem real_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Real) ret SmtType.None)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArg] using hRet

private theorem seq_op_1_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_seq_op_1_ret (__smtx_typeof t) ret)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases seq_arg_of_non_none_ret (op := op) hTy ht with ⟨T, hArg⟩
  rw [hTy]
  simpa [__smtx_typeof_seq_op_1_ret, hArg] using hRet

private theorem seq_op_2_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_seq_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases seq_binop_args_of_non_none_ret (op := op) hTy ht with ⟨T, h1, h2⟩
  rw [hTy]
  simpa [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, h1, h2] using hRet

private theorem set_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_sets_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases set_binop_ret_args_of_non_none (op := op) hTy ht with ⟨A, h1, h2⟩
  rw [hTy]
  simpa [__smtx_typeof_sets_op_2_ret, native_ite, native_Teq, h1, h2] using hRet

private theorem seq_char_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) ret
          SmtType.None)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArg] using hRet

private theorem seq_char_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char)) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := seq_char_binop_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArgs.1, hArgs.2] using hRet

private theorem seq_char_reglan_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := seq_char_reglan_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArgs.1, hArgs.2] using hRet

private theorem reglan_unop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := op) hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArg, type_has_no_none_components]

private theorem reglan_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) SmtType.RegLan
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := reglan_binop_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2, type_has_no_none_components]

private theorem bv_unop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_bv_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases bv_unop_arg_of_non_none (op := op) hTy ht with ⟨w, hArg⟩
  rw [hTy]
  simp [__smtx_typeof_bv_op_1, hArg, type_has_no_none_components]

private theorem bv_unop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_bv_op_1_ret (__smtx_typeof t) ret)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases bv_unop_ret_arg_of_non_none (op := op) hTy ht with ⟨w, hArg⟩
  rw [hTy]
  simpa [__smtx_typeof_bv_op_1_ret, hArg] using hRet

private theorem bv_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases bv_binop_args_of_non_none hTy ht with ⟨w, h1, h2⟩
  rw [hTy]
  simp [__smtx_typeof_bv_op_2, native_ite, native_nateq, Smtm.native_nateq,
    h1, h2, type_has_no_none_components]

private theorem bv_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases bv_binop_ret_args_of_non_none hTy ht with ⟨w, h1, h2⟩
  rw [hTy]
  simpa [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, Smtm.native_nateq,
    h1, h2] using hRet

private theorem eq_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.eq t1 t2)) := by
  rw [eq_term_typeof_of_non_none ht]
  simp [type_has_no_none_components]

private theorem exists_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.exists s T body)) := by
  rw [exists_term_typeof_of_non_none ht]
  simp [type_has_no_none_components]

private theorem forall_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.forall s T body)) := by
  rw [forall_term_typeof_of_non_none ht]
  simp [type_has_no_none_components]

private theorem to_real_type_has_no_none_components_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.to_real t)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.to_real t)) := by
  have hArg := to_real_arg_of_non_none ht
  rw [typeof_to_real_eq]
  simp [native_ite, native_Teq, hArg, type_has_no_none_components]

private theorem str_indexof_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_indexof t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_indexof t1 t2 t3)) := by
  rcases str_indexof_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [typeof_str_indexof_eq]
  simp [__smtx_typeof_str_indexof, native_ite, native_Teq, h1, h2, h3,
    type_has_no_none_components]

private theorem str_indexof_re_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_indexof_re t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_indexof_re t1 t2 t3)) := by
  have hArgs := str_indexof_re_args_of_non_none ht
  rw [typeof_str_indexof_re_eq]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2, type_has_no_none_components]

private theorem at_strings_occur_index_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm._at_strings_occur_index t1 t2 t3)) :
    type_has_no_none_components
      (__smtx_typeof (SmtTerm._at_strings_occur_index t1 t2 t3)) := by
  rcases at_strings_occur_index_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [typeof_at_strings_occur_index_eq]
  simp [__smtx_typeof_str_indexof, native_ite, native_Teq, h1, h2, h3,
    type_has_no_none_components]

private theorem at_strings_occur_index_re_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm._at_strings_occur_index_re t1 t2 t3)) :
    type_has_no_none_components
      (__smtx_typeof (SmtTerm._at_strings_occur_index_re t1 t2 t3)) := by
  have hArgs := at_strings_occur_index_re_args_of_non_none ht
  rw [typeof_at_strings_occur_index_re_eq]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2,
    type_has_no_none_components]

private theorem str_indexof_re_split_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_indexof_re_split t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_indexof_re_split t1 t2 t3)) := by
  have hArgs := str_indexof_re_split_args_of_non_none ht
  rw [typeof_str_indexof_re_split_eq]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2, type_has_no_none_components]

private theorem re_exp_type_has_no_none_components_of_non_none
    {n : native_Int}
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.re_exp (SmtTerm.Numeral n) t)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.re_exp (SmtTerm.Numeral n) t)) := by
  have hArgs := re_exp_arg_of_non_none ht
  rw [typeof_re_exp_eq]
  simp [__smtx_typeof_re_exp, native_ite, hArgs.1, hArgs.2, type_has_no_none_components]

private theorem re_loop_type_has_no_none_components_of_non_none
    {n1 n2 : native_Int}
    {t : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t)) :
    type_has_no_none_components
      (__smtx_typeof (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t)) := by
  have hArgs := re_loop_arg_of_non_none ht
  rw [typeof_re_loop_eq]
  simp [__smtx_typeof_re_loop, native_ite, hArgs.1, hArgs.2.1, hArgs.2.2,
    type_has_no_none_components]

private theorem concat_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.concat t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.concat t1 t2)) := by
  rcases bv_concat_args_of_non_none ht with ⟨w1, w2, h1, h2⟩
  rw [typeof_concat_eq]
  simp [__smtx_typeof_concat, h1, h2, type_has_no_none_components]

private theorem extract_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.extract t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.extract t1 t2 t3)) := by
  rcases extract_args_of_non_none ht with ⟨i, j, w, h1, h2, h3, hj0, hji, hiw⟩
  rw [typeof_extract_eq]
  simp [__smtx_typeof_extract, native_ite, h1, h2, h3, hj0, hji, hiw,
    type_has_no_none_components]

private theorem repeat_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.repeat t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.repeat t1 t2)) := by
  rcases repeat_args_of_non_none ht with ⟨i, w, h1, h2, hi1⟩
  rw [typeof_repeat_eq]
  simp [__smtx_typeof_repeat, native_ite, h1, h2, hi1, type_has_no_none_components]

private theorem zero_extend_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.zero_extend t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.zero_extend t1 t2)) := by
  rcases zero_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [typeof_zero_extend_eq]
  simp [__smtx_typeof_zero_extend, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem sign_extend_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.sign_extend t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.sign_extend t1 t2)) := by
  rcases sign_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [typeof_sign_extend_eq]
  simp [__smtx_typeof_sign_extend, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem rotate_left_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.rotate_left t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.rotate_left t1 t2)) := by
  rcases rotate_left_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [typeof_rotate_left_eq]
  simp [__smtx_typeof_rotate_left, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem rotate_right_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.rotate_right t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.rotate_right t1 t2)) := by
  rcases rotate_right_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [typeof_rotate_right_eq]
  simp [__smtx_typeof_rotate_right, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem int_to_bv_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.int_to_bv t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.int_to_bv t1 t2)) := by
  rcases int_to_bv_args_of_non_none ht with ⟨i, h1, h2, hi0⟩
  rw [typeof_int_to_bv_eq]
  simp [__smtx_typeof_int_to_bv, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem apply_term_type_has_no_none_components_of_non_none
    {f x : SmtTerm}
    (ihf : term_has_non_none_type f -> type_has_no_none_components (__smtx_typeof f))
    (ht : term_has_non_none_type (SmtTerm.Apply f x)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.Apply f x)) := by
  by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
  · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
    exact dt_sel_type_has_no_none_components_of_non_none ht
  · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
    · rcases hTesterWitness with ⟨s, d, i, rfl⟩
      exact dt_tester_type_has_no_none_components_of_non_none ht
    · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
        intro s d i j hEq
        exact hSelWitness ⟨s, d, i, j, hEq⟩
      have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
        intro s d i hEq
        exact hTesterWitness ⟨s, d, i, hEq⟩
      have hTy : generic_apply_type f x :=
        generic_apply_type_of_non_datatype_head hSel hTester
      have hTyEq :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTyEq]
        exact hNone
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have htf : term_has_non_none_type f := by
        rcases hF with hFun | hDtc
        · exact term_has_non_none_of_type_eq hFun (by simp)
        · exact term_has_non_none_of_type_eq hDtc (by simp)
      exact apply_type_has_no_none_components_of_non_none hTy ht (ihf htf)

theorem term_type_has_no_none_components_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> type_has_no_none_components (__smtx_typeof t) := by
  let rec go (t : SmtTerm) (ht : term_has_non_none_type t) :
      type_has_no_none_components (__smtx_typeof t) := by
    match t with
    | SmtTerm.None =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.Boolean _ =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.Numeral _ =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.Rational _ =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.String s =>
        cases hValid : native_string_valid s
        · exact False.elim (ht (by simp [__smtx_typeof, native_ite, hValid]))
        · simp [__smtx_typeof, native_ite, hValid, type_has_no_none_components]
    | SmtTerm.Binary _ _ =>
        exact binary_type_has_no_none_components_of_non_none ht
    | SmtTerm._at_purify t1 =>
        have ht1 : term_has_non_none_type t1 := by
          intro hNone
          apply ht
          simpa [__smtx_typeof] using hNone
        simpa [__smtx_typeof] using go t1 ht1
    | SmtTerm.Apply f x =>
        exact apply_term_type_has_no_none_components_of_non_none (ihf := fun hf => go f hf) ht
    | SmtTerm.Var _ _ =>
        exact var_type_has_no_none_components_of_non_none ht
    | SmtTerm.ite c t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
          exact term_has_non_none_of_type_eq h1 hT
        exact ite_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.eq _ _ =>
        exact eq_type_has_no_none_components_of_non_none ht
    | SmtTerm.exists _ _ _ =>
        exact exists_type_has_no_none_components_of_non_none ht
    | SmtTerm.forall _ _ _ =>
        exact forall_type_has_no_none_components_of_non_none ht
    | SmtTerm.choice _ _ _ =>
        exact choice_type_has_no_none_components_of_non_none ht
    | SmtTerm.bind s T x1 x2 =>
        have hTyEq : __smtx_typeof (SmtTerm.bind s T x1 x2) = __smtx_typeof x2 :=
          bind_term_typeof_of_non_none ht
        have hx2NN : term_has_non_none_type x2 := by
          unfold term_has_non_none_type at ht ⊢
          rw [hTyEq] at ht
          exact ht
        rw [hTyEq]
        exact go x2 hx2NN
    | SmtTerm.DtCons _ _ _ =>
        exact dt_cons_type_has_no_none_components_of_non_none ht
    | SmtTerm.DtSel _ _ _ _ =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.DtTester _ _ _ =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.UConst _ _ =>
        exact uconst_type_has_no_none_components_of_non_none ht
    | SmtTerm.not t1 =>
        exact bool_unop_type_has_no_none_components_of_non_none (typeof_not_eq t1) ht
    | SmtTerm.or t1 t2 =>
        exact bool_binop_type_has_no_none_components_of_non_none (typeof_or_eq t1 t2) ht
    | SmtTerm.and t1 t2 =>
        exact bool_binop_type_has_no_none_components_of_non_none (typeof_and_eq t1 t2) ht
    | SmtTerm.imp t1 t2 =>
        exact bool_binop_type_has_no_none_components_of_non_none (typeof_imp_eq t1 t2) ht
    | SmtTerm.xor t1 t2 =>
        exact bool_binop_type_has_no_none_components_of_non_none (typeof_xor_eq t1 t2) ht
    | SmtTerm.plus t1 t2 =>
        exact arith_binop_type_has_no_none_components_of_non_none (typeof_plus_eq t1 t2) ht
    | SmtTerm.neg t1 t2 =>
        exact arith_binop_type_has_no_none_components_of_non_none (typeof_neg_eq t1 t2) ht
    | SmtTerm.mult t1 t2 =>
        exact arith_binop_type_has_no_none_components_of_non_none (typeof_mult_eq t1 t2) ht
    | SmtTerm.lt t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_lt_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.leq t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_leq_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.gt t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_gt_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.geq t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_geq_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.to_real _ =>
        exact to_real_type_has_no_none_components_of_non_none ht
    | SmtTerm.to_int t1 =>
        exact real_ret_type_has_no_none_components_of_non_none
          (typeof_to_int_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.is_int t1 =>
        exact real_ret_type_has_no_none_components_of_non_none
          (typeof_is_int_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.abs t1 =>
        exact arith_unop_type_has_no_none_components_of_non_none (typeof_abs_eq t1) ht
    | SmtTerm.uneg t1 =>
        exact arith_unop_type_has_no_none_components_of_non_none (typeof_uneg_eq t1) ht
    | SmtTerm.div t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_div_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.mod t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_mod_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.divisible t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_divisible_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.int_pow2 t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_int_pow2_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.int_log2 t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_int_log2_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.div_total t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_div_total_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.mod_total t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_mod_total_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.select t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact select_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.store t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact store_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.map_diff t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases map_diff_args_of_non_none ht with hMap | hSet
          · rcases hMap with ⟨A, B, h1, h2, hRes⟩
            exact term_has_non_none_of_type_eq h1 (by simp)
          · rcases hSet with ⟨A, h1, h2, hRes⟩
            exact term_has_non_none_of_type_eq h1 (by simp)
        exact map_diff_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.seq_diff t1 t2 =>
        exact seq_op_2_ret_type_has_no_none_components_of_non_none
          (typeof_seq_diff_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.concat _ _ =>
        exact concat_type_has_no_none_components_of_non_none ht
    | SmtTerm.extract _ _ _ =>
        exact extract_type_has_no_none_components_of_non_none ht
    | SmtTerm.repeat _ _ =>
        exact repeat_type_has_no_none_components_of_non_none ht
    | SmtTerm.bvnot t1 =>
        exact bv_unop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvnot t1) = __smtx_typeof_bv_op_1 (__smtx_typeof t1) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvand t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvand t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvor t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvor t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvnand t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvnand t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvnor t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvnor t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvxor t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvxor t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvxnor t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvxnor t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvcomp t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvcomp t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) (SmtType.BitVec 1) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvneg t1 =>
        exact bv_unop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvneg t1) = __smtx_typeof_bv_op_1 (__smtx_typeof t1) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvadd t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvadd t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvmul t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvmul t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvudiv t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvudiv t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvurem t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvurem t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvsub t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsub t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvsdiv t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsdiv t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvsrem t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsrem t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvsmod t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsmod t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvult t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvult t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvule t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvule t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvugt t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvugt t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvuge t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvuge t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvslt t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvslt t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsle t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsle t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsgt t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsgt t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsge t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsge t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvshl t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvshl t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvlshr t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvlshr t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.bvashr t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvashr t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_def] <;> simp only) ht
    | SmtTerm.zero_extend _ _ =>
        exact zero_extend_type_has_no_none_components_of_non_none ht
    | SmtTerm.sign_extend _ _ =>
        exact sign_extend_type_has_no_none_components_of_non_none ht
    | SmtTerm.rotate_left _ _ =>
        exact rotate_left_type_has_no_none_components_of_non_none ht
    | SmtTerm.rotate_right _ _ =>
        exact rotate_right_type_has_no_none_components_of_non_none ht
    | SmtTerm.bvuaddo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvuaddo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvnego t1 =>
        exact bv_unop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvnego t1) =
              __smtx_typeof_bv_op_1_ret (__smtx_typeof t1) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsaddo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsaddo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvumulo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvumulo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsmulo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsmulo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvusubo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvusubo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvssubo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvssubo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsdivo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsdivo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.seq_empty _ =>
        exact seq_empty_type_has_no_none_components_of_non_none ht
    | SmtTerm.str_len t1 =>
        exact seq_op_1_ret_type_has_no_none_components_of_non_none
          (typeof_str_len_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_concat t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat) (typeof_str_concat_eq t1 t2) ht with
            ⟨T, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact seq_op_2_type_has_no_none_components_of_non_none
          (typeof_str_concat_eq t1 t2) ht (go t1 ht1)
    | SmtTerm.str_substr t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases str_substr_args_of_non_none ht with ⟨T, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact str_substr_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.str_contains t1 t2 =>
        exact seq_op_2_ret_type_has_no_none_components_of_non_none
          (typeof_str_contains_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_replace t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace) (typeof_str_replace_eq t1 t2 t3) ht with
            ⟨T, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact seq_op_3_type_has_no_none_components_of_non_none
          (typeof_str_replace_eq t1 t2 t3) ht (go t1 ht1)
    | SmtTerm.str_indexof _ _ _ =>
        exact str_indexof_type_has_no_none_components_of_non_none ht
    | SmtTerm.str_at t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases str_at_args_of_non_none ht with ⟨T, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact str_at_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.str_prefixof t1 t2 =>
        exact seq_op_2_ret_type_has_no_none_components_of_non_none
          (typeof_str_prefixof_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_suffixof t1 t2 =>
        exact seq_op_2_ret_type_has_no_none_components_of_non_none
          (typeof_str_suffixof_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_rev t1 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_arg_of_non_none (op := SmtTerm.str_rev) (typeof_str_rev_eq t1) ht with ⟨T, hArg⟩
          exact term_has_non_none_of_type_eq hArg (by simp)
        exact seq_op_1_type_has_no_none_components_of_non_none
          (typeof_str_rev_eq t1) ht (go t1 ht1)
    | SmtTerm.str_update t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases str_update_args_of_non_none ht with ⟨T, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact str_update_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.str_to_lower t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_lower_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_to_upper t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_upper_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_to_code t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_code_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_from_code t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_str_from_code_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_is_digit t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_is_digit_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_to_int t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_int_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_from_int t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_str_from_int_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_lt t1 t2 =>
        exact seq_char_binop_ret_type_has_no_none_components_of_non_none
          (typeof_str_lt_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_leq t1 t2 =>
        exact seq_char_binop_ret_type_has_no_none_components_of_non_none
          (typeof_str_leq_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_replace_all t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all) (typeof_str_replace_all_eq t1 t2 t3) ht with
            ⟨T, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact seq_op_3_type_has_no_none_components_of_non_none
          (typeof_str_replace_all_eq t1 t2 t3) ht (go t1 ht1)
    | SmtTerm.str_replace_re t1 t2 t3 =>
        exact str_replace_re_type_has_no_none_components_of_non_none
          (typeof_str_replace_re_eq t1 t2 t3) ht
    | SmtTerm.str_replace_re_all t1 t2 t3 =>
        exact str_replace_re_type_has_no_none_components_of_non_none
          (typeof_str_replace_re_all_eq t1 t2 t3) ht
    | SmtTerm.str_indexof_re _ _ _ =>
        exact str_indexof_re_type_has_no_none_components_of_non_none ht
    | SmtTerm.str_indexof_re_split _ _ _ =>
        exact str_indexof_re_split_type_has_no_none_components_of_non_none ht
    | SmtTerm._at_strings_occur_index _ _ _ =>
        exact at_strings_occur_index_type_has_no_none_components_of_non_none ht
    | SmtTerm._at_strings_occur_index_re _ _ _ =>
        exact at_strings_occur_index_re_type_has_no_none_components_of_non_none ht
    | SmtTerm.re_allchar =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.re_none =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.re_all =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.str_to_re t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_re_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.re_mult t1 =>
        exact reglan_unop_type_has_no_none_components_of_non_none
          (typeof_re_mult_eq t1) ht
    | SmtTerm.re_plus t1 =>
        exact reglan_unop_type_has_no_none_components_of_non_none
          (typeof_re_plus_eq t1) ht
    | SmtTerm.re_exp t1 t2 =>
        cases t1 with
        | Numeral _ =>
            exact re_exp_type_has_no_none_components_of_non_none ht
        | _ =>
            exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_exp]))
    | SmtTerm.re_opt t1 =>
        exact reglan_unop_type_has_no_none_components_of_non_none
          (typeof_re_opt_eq t1) ht
    | SmtTerm.re_comp t1 =>
        exact reglan_unop_type_has_no_none_components_of_non_none
          (typeof_re_comp_eq t1) ht
    | SmtTerm.re_range t1 t2 =>
        exact seq_char_binop_ret_type_has_no_none_components_of_non_none
          (typeof_re_range_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.re_concat t1 t2 =>
        exact reglan_binop_type_has_no_none_components_of_non_none
          (typeof_re_concat_eq t1 t2) ht
    | SmtTerm.re_inter t1 t2 =>
        exact reglan_binop_type_has_no_none_components_of_non_none
          (typeof_re_inter_eq t1 t2) ht
    | SmtTerm.re_union t1 t2 =>
        exact reglan_binop_type_has_no_none_components_of_non_none
          (typeof_re_union_eq t1 t2) ht
    | SmtTerm.re_diff t1 t2 =>
        exact reglan_binop_type_has_no_none_components_of_non_none
          (typeof_re_diff_eq t1 t2) ht
    | SmtTerm.re_loop t1 t2 t3 =>
        cases t1 with
        | Numeral _ =>
            cases t2 with
            | Numeral _ =>
                exact re_loop_type_has_no_none_components_of_non_none ht
            | _ =>
                exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_loop]))
        | _ =>
            exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_loop]))
    | SmtTerm.str_in_re t1 t2 =>
        exact seq_char_reglan_ret_type_has_no_none_components_of_non_none
          (typeof_str_in_re_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.seq_unit t1 =>
        have ht1 : term_has_non_none_type t1 :=
          seq_unit_arg_non_none_of_non_none ht
        exact seq_unit_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.seq_nth t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact seq_nth_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.set_empty _ =>
        exact set_empty_type_has_no_none_components_of_non_none ht
    | SmtTerm.set_singleton t1 =>
        have ht1 : term_has_non_none_type t1 :=
          set_singleton_arg_non_none_of_non_none ht
        exact set_singleton_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.set_union t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases set_binop_args_of_non_none (op := SmtTerm.set_union) (typeof_set_union_eq t1 t2) ht with
            ⟨A, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact set_binop_type_has_no_none_components_of_non_none
          (typeof_set_union_eq t1 t2) ht (go t1 ht1)
    | SmtTerm.set_inter t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases set_binop_args_of_non_none (op := SmtTerm.set_inter) (typeof_set_inter_eq t1 t2) ht with
            ⟨A, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact set_binop_type_has_no_none_components_of_non_none
          (typeof_set_inter_eq t1 t2) ht (go t1 ht1)
    | SmtTerm.set_minus t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases set_binop_args_of_non_none (op := SmtTerm.set_minus) (typeof_set_minus_eq t1 t2) ht with
            ⟨A, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact set_binop_type_has_no_none_components_of_non_none
          (typeof_set_minus_eq t1 t2) ht (go t1 ht1)
    | SmtTerm.set_member _ _ =>
        have hArgs := set_member_args_of_non_none ht
        rcases hArgs with ⟨A, h1, h2⟩
        rw [typeof_set_member_eq]
        simp [__smtx_typeof_set_member, native_ite, native_Teq, h1, h2, type_has_no_none_components]
    | SmtTerm.set_subset t1 t2 =>
        exact set_binop_ret_type_has_no_none_components_of_non_none
          (typeof_set_subset_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.qdiv t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_qdiv_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.qdiv_total t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_qdiv_total_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.int_to_bv _ _ =>
        exact int_to_bv_type_has_no_none_components_of_non_none ht
    | SmtTerm.ubv_to_int t1 =>
        exact bv_unop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.ubv_to_int t1) =
              __smtx_typeof_bv_op_1_ret (__smtx_typeof t1) SmtType.Int by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
    | SmtTerm.sbv_to_int t1 =>
        exact bv_unop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.sbv_to_int t1) =
              __smtx_typeof_bv_op_1_ret (__smtx_typeof t1) SmtType.Int by
            rw [__smtx_typeof.eq_def] <;> simp only) ht (by simp [type_has_no_none_components])
  exact go

/-- Every non-`None` SMT term lies in the supported preservation fragment. -/
theorem supported_preservation_term_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> supported_preservation_term t := by
  let rec go (t : SmtTerm) (ht : term_has_non_none_type t) :
      supported_preservation_term t := by
    match t with
    | SmtTerm.None =>
        exact False.elim (ht (by simp [__smtx_typeof]))
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
    | SmtTerm._at_purify t1 =>
        have ht1 : term_has_non_none_type t1 := by
          intro hNone
          apply ht
          simpa [__smtx_typeof] using hNone
        exact supported_preservation_term.purify ht1 (go t1 ht1)
    | SmtTerm.Apply f x =>
        exact supported_apply_term_of_non_none
          (ihf := fun hf => go f hf)
          (ihx := fun hx => go x hx)
          ht
    | SmtTerm.Var _ _ =>
        exact supported_var_of_non_none ht
    | SmtTerm.ite c t1 t2 =>
        rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
        have htc : term_has_non_none_type c :=
          term_has_non_none_of_type_eq hc (by simp)
        have ht1 : term_has_non_none_type t1 :=
          term_has_non_none_of_type_eq h1 hT
        have ht2 : term_has_non_none_type t2 :=
          term_has_non_none_of_type_eq h2 hT
        exact supported_ite_of_non_none ht (go c htc) (go t1 ht1) (go t2 ht2)
    | SmtTerm.eq t1 t2 =>
        exact supported_preservation_term.eq t1 t2
    | SmtTerm.exists s T body =>
        exact supported_preservation_term.exists s T body
    | SmtTerm.forall s T body =>
        exact supported_preservation_term.forall s T body
    | SmtTerm.choice _ _ _ =>
        exact supported_choice_of_non_none ht
    | SmtTerm.bind s T x1 x2 =>
        exact supported_bind_of_non_none ht
          (go x1 (bind_arg1_non_none_of_non_none ht))
          (go x2 (bind_arg2_non_none_of_non_none ht))
    | SmtTerm.DtCons s d i =>
        exact supported_preservation_term.dt_cons s d i
    | SmtTerm.DtSel _ _ _ _ =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.DtTester _ _ _ =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.UConst _ _ =>
        exact supported_uconst_of_non_none ht
    | SmtTerm.not t1 =>
        have h1 : __smtx_typeof t1 = SmtType.Bool :=
          bool_unop_arg_of_non_none (typeof_not_eq t1) ht
        have ht1 : term_has_non_none_type t1 :=
          term_has_non_none_of_type_eq h1 (by simp)
        exact supported_preservation_term.not ht1 (go t1 ht1)
    | SmtTerm.or t1 t2 =>
        have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) (typeof_or_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.or ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.and t1 t2 =>
        have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) (typeof_and_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.and ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.imp t1 t2 =>
        have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) (typeof_imp_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.imp ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.xor t1 t2 =>
        exact supported_preservation_term.xor t1 t2
    | SmtTerm.plus t1 t2 =>
        rcases arith_binop_args_of_non_none (op := SmtTerm.plus) (typeof_plus_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.plus ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.plus ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.neg t1 t2 =>
        rcases arith_binop_args_of_non_none (op := SmtTerm.neg) (typeof_neg_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.arith_neg ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.arith_neg ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.mult t1 t2 =>
        rcases arith_binop_args_of_non_none (op := SmtTerm.mult) (typeof_mult_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.mult ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.mult ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.lt t1 t2 =>
        rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt) (typeof_lt_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.lt ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.lt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.leq t1 t2 =>
        rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq) (typeof_leq_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.leq ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.leq ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.gt t1 t2 =>
        rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt) (typeof_gt_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.gt ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.gt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.geq t1 t2 =>
        rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq) (typeof_geq_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.geq ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.geq ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.to_real t1 =>
        have hArg := to_real_arg_of_non_none ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.to_real ht1 (go t1 ht1)
    | SmtTerm.to_int t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Real :=
          real_arg_of_non_none (op := SmtTerm.to_int) (typeof_to_int_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.to_int ht1 (go t1 ht1)
    | SmtTerm.is_int t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Real :=
          real_arg_of_non_none (op := SmtTerm.is_int) (typeof_is_int_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.is_int ht1 (go t1 ht1)
    | SmtTerm.abs t1 =>
        rcases abs_arg_of_non_none ht with hArg | hArg
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
          exact supported_preservation_term.abs ht1 (go t1 ht1)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
          exact supported_preservation_term.abs ht1 (go t1 ht1)
    | SmtTerm.uneg t1 =>
        rcases arith_unop_arg_of_non_none (op := SmtTerm.uneg) (typeof_uneg_eq t1) ht with hArg | hArg
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
          exact supported_preservation_term.uneg ht1 (go t1 ht1)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
          exact supported_preservation_term.uneg ht1 (go t1 ht1)
    | SmtTerm.div t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.div) (typeof_div_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.div ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.mod t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod) (typeof_mod_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.mod ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.divisible t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.divisible) (typeof_divisible_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.divisible ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.int_pow2 t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int :=
          int_ret_arg_of_non_none (op := SmtTerm.int_pow2) (typeof_int_pow2_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.int_pow2 ht1 (go t1 ht1)
    | SmtTerm.int_log2 t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int :=
          int_ret_arg_of_non_none (op := SmtTerm.int_log2) (typeof_int_log2_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.int_log2 ht1 (go t1 ht1)
    | SmtTerm.div_total t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.div_total) (typeof_div_total_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.div_total ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.mod_total t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod_total) (typeof_mod_total_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.mod_total ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.select t1 t2 =>
        rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have hMapTy := term_type_has_no_none_components_of_non_none t1 ht1
        have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
          simpa [h1] using hMapTy
        have hMapNN := type_has_no_none_components_map_components_non_none hMapTy'
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 hMapNN.1
        exact supported_select_of_non_none ht hMapTy (go t1 ht1) (go t2 ht2)
    | SmtTerm.store t1 t2 t3 =>
        rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have hMapTy := term_type_has_no_none_components_of_non_none t1 ht1
        have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
          simpa [h1] using hMapTy
        have hMapNN := type_has_no_none_components_map_components_non_none hMapTy'
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 hMapNN.1
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 hMapNN.2
        exact supported_store_of_non_none ht hMapTy (go t1 ht1) (go t2 ht2) (go t3 ht3)
    | SmtTerm.map_diff t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases map_diff_args_of_non_none ht with hMap | hSet
          · rcases hMap with ⟨A, B, h1, h2, hRes⟩
            exact term_has_non_none_of_type_eq h1 (by simp)
          · rcases hSet with ⟨A, h1, h2, hRes⟩
            exact term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := by
          rcases map_diff_args_of_non_none ht with hMap | hSet
          · rcases hMap with ⟨A, B, h1, h2, hRes⟩
            exact term_has_non_none_of_type_eq h2 (by simp)
          · rcases hSet with ⟨A, h1, h2, hRes⟩
            exact term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.map_diff ht1 (go t1 ht1) ht2 (go t2 ht2)
          (map_diff_default_typed_canonical_of_non_none ht)
    | SmtTerm.seq_diff t1 t2 =>
        rcases seq_binop_args_of_non_none_ret (op := SmtTerm.seq_diff)
            (typeof_seq_diff_eq t1 t2) ht with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.seq_diff ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.concat t1 t2 =>
        rcases bv_concat_args_of_non_none ht with ⟨w1, w2, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bv_concat ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.extract t1 t2 t3 =>
        rcases extract_args_of_non_none ht with ⟨i, j, w, h1, h2, h3, hj0, hji, hiw⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := by
          rw [h2]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.extract ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.repeat t1 t2 =>
        rcases repeat_args_of_non_none ht with ⟨i, w, h1, h2, hi1⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.repeat ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvnot t1 =>
        rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot) (by rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.bvnot ht1 (go t1 ht1)
    | SmtTerm.bvand t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvand t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvand ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvor t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvor t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvor ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvnand t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvnand t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvnand ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvnor t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvnor t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvnor ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvxor t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvxor t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvxor ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvxnor t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvxnor t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvxnor ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvcomp t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvcomp t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) (SmtType.BitVec 1) by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvcomp ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvneg t1 =>
        rcases bv_unop_arg_of_non_none (op := SmtTerm.bvneg) (by rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.bvneg ht1 (go t1 ht1)
    | SmtTerm.bvadd t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvadd t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvadd ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvmul t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvmul t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvmul ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvudiv t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvudiv t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvudiv ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvurem t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvurem t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvurem ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsub t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvsub t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsub ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsdiv t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvsdiv t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsdiv ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsrem t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvsrem t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsrem ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsmod t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvsmod t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsmod ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvult t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvult t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvult ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvule t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvule t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvule ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvugt t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvugt t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvugt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvuge t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvuge t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvuge ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvslt t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvslt t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvslt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsle t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsle t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsle ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsgt t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsgt t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsgt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsge t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsge t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsge ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvshl t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvshl t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvshl ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvlshr t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvlshr t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvlshr ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvashr t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvashr t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_def] <;> simp only) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvashr ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.zero_extend t1 t2 =>
        rcases zero_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.zero_extend ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.sign_extend t1 t2 =>
        rcases sign_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.sign_extend ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.rotate_left t1 t2 =>
        rcases rotate_left_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.rotate_left ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.rotate_right t1 t2 =>
        rcases rotate_right_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.rotate_right ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvuaddo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvuaddo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvuaddo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvnego t1 =>
        rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.bvnego) (by rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.bvnego ht1 (go t1 ht1)
    | SmtTerm.bvsaddo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsaddo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsaddo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvumulo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvumulo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvumulo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsmulo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsmulo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsmulo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvusubo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvusubo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvusubo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvssubo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvssubo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvssubo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsdivo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsdivo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsdivo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.seq_empty _ =>
        exact supported_seq_empty_of_non_none ht
    | SmtTerm.str_len t1 =>
        rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len) (typeof_str_len_eq t1) ht with ⟨T, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_len ht1 (go t1 ht1)
    | SmtTerm.str_concat t1 t2 =>
        rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat) (typeof_str_concat_eq t1 t2) ht with
          ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.str_concat ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_substr t1 t2 t3 =>
        rcases str_substr_args_of_non_none ht with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_substr ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_contains t1 t2 =>
        rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains) (typeof_str_contains_eq t1 t2) ht with
          ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.str_contains ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_replace t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace) (typeof_str_replace_eq t1 t2 t3) ht with
          ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_replace ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_indexof t1 t2 t3 =>
        rcases str_indexof_args_of_non_none ht with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_indexof ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_at t1 t2 =>
        rcases str_at_args_of_non_none ht with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.str_at ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_prefixof t1 t2 =>
        rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_prefixof)
            (typeof_str_prefixof_eq t1 t2) ht with
          ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.str_prefixof ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_suffixof t1 t2 =>
        rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_suffixof)
            (typeof_str_suffixof_eq t1 t2) ht with
          ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.str_suffixof ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_rev t1 =>
        rcases seq_arg_of_non_none (op := SmtTerm.str_rev) (typeof_str_rev_eq t1) ht with ⟨T, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_rev ht1 (go t1 ht1)
    | SmtTerm.str_update t1 t2 t3 =>
        rcases str_update_args_of_non_none ht with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_update ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_to_lower t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_lower) (typeof_str_to_lower_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_lower ht1 (go t1 ht1)
    | SmtTerm.str_to_upper t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_upper) (typeof_str_to_upper_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_upper ht1 (go t1 ht1)
    | SmtTerm.str_to_code t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_code) (typeof_str_to_code_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_code ht1 (go t1 ht1)
    | SmtTerm.str_from_code t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int :=
          int_arg_of_non_none_ret (op := SmtTerm.str_from_code) (typeof_str_from_code_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_from_code ht1 (go t1 ht1)
    | SmtTerm.str_is_digit t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_is_digit) (typeof_str_is_digit_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_is_digit ht1 (go t1 ht1)
    | SmtTerm.str_to_int t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_int) (typeof_str_to_int_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_int ht1 (go t1 ht1)
    | SmtTerm.str_from_int t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int :=
          int_arg_of_non_none_ret (op := SmtTerm.str_from_int) (typeof_str_from_int_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_from_int ht1 (go t1 ht1)
    | SmtTerm.str_lt t1 t2 =>
        have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_lt) (typeof_str_lt_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.str_lt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_leq t1 t2 =>
        have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_leq) (typeof_str_leq_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.str_leq ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_replace_all t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all) (typeof_str_replace_all_eq t1 t2 t3) ht with
          ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_replace_all ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_replace_re t1 t2 t3 =>
        have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re) (typeof_str_replace_re_eq t1 t2 t3) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2.1 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
        exact supported_preservation_term.str_replace_re ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_replace_re_all t1 t2 t3 =>
        have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all) (typeof_str_replace_re_all_eq t1 t2 t3) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2.1 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
        exact supported_preservation_term.str_replace_re_all ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_indexof_re t1 t2 t3 =>
        have hArgs := str_indexof_re_args_of_non_none ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2.1 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
        exact supported_preservation_term.str_indexof_re ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm._at_strings_occur_index t1 t2 t3 =>
        rcases at_strings_occur_index_args_of_non_none ht with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term._at_strings_occur_index ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm._at_strings_occur_index_re t1 t2 t3 =>
        have hArgs := at_strings_occur_index_re_args_of_non_none ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2.1 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
        exact supported_preservation_term._at_strings_occur_index_re ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_indexof_re_split t1 t2 t3 =>
        have hArgs := str_indexof_re_split_args_of_non_none ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2.1 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
        exact supported_preservation_term.str_indexof_re_split ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.re_allchar =>
        exact supported_preservation_term.re_allchar
    | SmtTerm.re_none =>
        exact supported_preservation_term.re_none
    | SmtTerm.re_all =>
        exact supported_preservation_term.re_all
    | SmtTerm.str_to_re t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_re) (typeof_str_to_re_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_re ht1 (go t1 ht1)
    | SmtTerm.re_mult t1 =>
        have hArg : __smtx_typeof t1 = SmtType.RegLan :=
          reglan_arg_of_non_none (op := SmtTerm.re_mult) (typeof_re_mult_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.re_mult ht1 (go t1 ht1)
    | SmtTerm.re_plus t1 =>
        have hArg : __smtx_typeof t1 = SmtType.RegLan :=
          reglan_arg_of_non_none (op := SmtTerm.re_plus) (typeof_re_plus_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.re_plus ht1 (go t1 ht1)
    | SmtTerm.re_exp t1 t2 =>
        cases t1 with
        | Numeral n =>
            have hArgs := re_exp_arg_of_non_none ht
            have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
            exact supported_preservation_term.re_exp n ht2 (go t2 ht2)
        | _ =>
            exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_exp]))
    | SmtTerm.re_opt t1 =>
        have hArg : __smtx_typeof t1 = SmtType.RegLan :=
          reglan_arg_of_non_none (op := SmtTerm.re_opt) (typeof_re_opt_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.re_opt ht1 (go t1 ht1)
    | SmtTerm.re_comp t1 =>
        have hArg : __smtx_typeof t1 = SmtType.RegLan :=
          reglan_arg_of_non_none (op := SmtTerm.re_comp) (typeof_re_comp_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.re_comp ht1 (go t1 ht1)
    | SmtTerm.re_range t1 t2 =>
        have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.re_range) (typeof_re_range_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_range ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_concat t1 t2 =>
        have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_concat) (typeof_re_concat_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_concat ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_inter t1 t2 =>
        have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_inter) (typeof_re_inter_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_inter ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_union t1 t2 =>
        have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_union) (typeof_re_union_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_union ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_diff t1 t2 =>
        have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_diff) (typeof_re_diff_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_diff ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_loop t1 t2 t3 =>
        cases t1 with
        | Numeral n1 =>
            cases t2 with
            | Numeral n2 =>
                have hArgs := re_loop_arg_of_non_none ht
                have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
                exact supported_preservation_term.re_loop n1 n2 ht3 (go t3 ht3)
            | _ =>
                exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_loop]))
        | _ =>
            exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_loop]))
    | SmtTerm.str_in_re t1 t2 =>
        have hArgs := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re) (typeof_str_in_re_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.str_in_re ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.seq_unit t1 =>
        have ht1 : term_has_non_none_type t1 :=
          seq_unit_arg_non_none_of_non_none ht
        exact supported_seq_unit_of_non_none ht (go t1 ht1)
    | SmtTerm.seq_nth t1 t2 =>
        rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_seq_nth_of_non_none ht (go t1 ht1) (go t2 ht2)
          (seq_nth_elem_wf_rec_of_non_none ht)
    | SmtTerm.set_empty _ =>
        exact supported_set_empty_of_non_none ht
    | SmtTerm.set_singleton t1 =>
        have ht1 : term_has_non_none_type t1 :=
          set_singleton_arg_non_none_of_non_none ht
        exact supported_set_singleton_of_non_none ht (go t1 ht1)
    | SmtTerm.set_union t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union) (typeof_set_union_eq t1 t2) ht with
          ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.set_union ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.set_inter t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_inter) (typeof_set_inter_eq t1 t2) ht with
          ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.set_inter ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.set_minus t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_minus) (typeof_set_minus_eq t1 t2) ht with
          ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.set_minus ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.set_member t1 t2 =>
        rcases set_member_args_of_non_none ht with ⟨A, h1, h2⟩
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have hSetTy := term_type_has_no_none_components_of_non_none t2 ht2
        have hSetTy' : type_has_no_none_components (SmtType.Set A) := by
          simpa [h2] using hSetTy
        have hA : A ≠ SmtType.None := type_has_no_none_components_set_component_non_none hSetTy'
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 hA
        exact supported_preservation_term.set_member ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.set_subset t1 t2 =>
        rcases set_binop_ret_args_of_non_none (op := SmtTerm.set_subset) (typeof_set_subset_eq t1 t2) ht with
          ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.set_subset ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.qdiv t1 t2 =>
        rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (typeof_qdiv_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.qdiv ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.qdiv ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.qdiv_total t1 t2 =>
        rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (typeof_qdiv_total_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.qdiv_total ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.qdiv_total ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.int_to_bv t1 t2 =>
        rcases int_to_bv_args_of_non_none ht with ⟨i, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.int_to_bv ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.ubv_to_int t1 =>
        rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.ubv_to_int) (by rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.ubv_to_int ht1 (go t1 ht1)
    | SmtTerm.sbv_to_int t1 =>
        rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.sbv_to_int) (by rw [__smtx_typeof.eq_def] <;> simp only) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.sbv_to_int ht1 (go t1 ht1)
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

/-- Backwards-compatible wrapper around `type_preservation` for explicit type equalities. -/
theorem smt_model_eval_preserves_type
    (M : SmtModel) (hM : model_wf M)
    (t : SmtTerm) (T : SmtType) :
  __smtx_typeof t = T ->
  T ≠ SmtType.None ->
  type_inhabited T ->
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  intro hTy hNonNone _hInh
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact hNonNone
  simpa [hTy] using
    smt_model_eval_preserves_type_of_non_none M hM t hNN

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

end Smtm
