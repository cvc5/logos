module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.Proofs.TypePreservation.Helpers
public import Cpc.Proofs.TypePreservation.SeqStringRegex
import all Cpc.Proofs.TypePreservation.SeqStringRegex

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

abbrev mkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

abbrev mkConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y

abbrev mkPair (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) x) y

theorem seq_ne_none (T : SmtType) : SmtType.Seq T ≠ SmtType.None := by
  intro h
  cases h

theorem type_inhabited_of_type_wf (T : SmtType)
    (h : __smtx_type_wf T = true) :
    type_inhabited T := by
  exact Smtm.type_inhabited_of_type_wf T h

theorem seq_component_inhabited_wf_of_seq_wf (T : SmtType)
    (h : __smtx_type_wf (SmtType.Seq T) = true) :
    type_inhabited T ∧ __smtx_type_wf T = true := by
  have hTWf : __smtx_type_wf T = true :=
    seq_type_wf_component_of_wf h
  exact ⟨_root_.type_inhabited_of_type_wf T hTWf, hTWf⟩

theorem term_has_non_none_of_type_eq
    {t : SmtTerm}
    {T : SmtType}
    (h : __smtx_typeof t = T)
    (hT : T ≠ SmtType.None) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type
  rw [h]
  exact hT

def type_result_seq_components_wf : SmtType -> Prop
  | SmtType.Seq A => __smtx_type_wf (SmtType.Seq A) = true
  | SmtType.Set A => __smtx_type_wf (SmtType.Set A) = true
  | SmtType.Datatype s d => __smtx_type_wf (SmtType.Datatype s d) = true
  | SmtType.Map A B => __smtx_type_wf (SmtType.Map A B) = true
  | SmtType.FunType A B => __smtx_type_wf (SmtType.FunType A B) = true
  | SmtType.DtcAppType _ B => type_result_seq_components_wf B
  | _ => True

@[simp] theorem type_result_seq_components_wf_if
    {c : Prop} [Decidable c] {A B : SmtType}
    (hA : type_result_seq_components_wf A)
    (hB : type_result_seq_components_wf B) :
    type_result_seq_components_wf (if c then A else B) := by
  by_cases hc : c <;> simp [hc, hA, hB]

@[simp] theorem type_result_seq_components_wf_native_ite
    (c : native_Bool) {A B : SmtType}
    (hA : type_result_seq_components_wf A)
    (hB : type_result_seq_components_wf B) :
    type_result_seq_components_wf (native_ite c A B) := by
  cases c <;> simp [native_ite, hA, hB]

theorem type_result_seq_components_wf_typeof_eq
    (T U : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_eq T U) := by
  cases T <;> cases U <;>
    simp [__smtx_typeof_eq, __smtx_typeof_guard,
      type_result_seq_components_wf, native_ite, native_Teq]
  all_goals
    repeat (first | split)
    all_goals simp [type_result_seq_components_wf]

theorem type_result_seq_components_wf_arith_overload_op_1
    (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_arith_overload_op_1 T) := by
  cases T <;> simp [__smtx_typeof_arith_overload_op_1,
    type_result_seq_components_wf]

theorem type_result_seq_components_wf_arith_overload_op_2
    (T U : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_arith_overload_op_2 T U) := by
  cases T <;> cases U <;> simp [__smtx_typeof_arith_overload_op_2,
    type_result_seq_components_wf]

theorem type_result_seq_components_wf_arith_overload_op_2_ret
    (T U R : SmtType)
    (hR : type_result_seq_components_wf R) :
    type_result_seq_components_wf
      (__smtx_typeof_arith_overload_op_2_ret T U R) := by
  cases T <;> cases U <;> simp [__smtx_typeof_arith_overload_op_2_ret,
    type_result_seq_components_wf, hR]

theorem type_result_seq_components_wf_bv_op_1
    (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_bv_op_1 T) := by
  cases T <;> simp [__smtx_typeof_bv_op_1, type_result_seq_components_wf]

theorem type_result_seq_components_wf_bv_op_1_ret
    (T R : SmtType)
    (hR : type_result_seq_components_wf R) :
    type_result_seq_components_wf (__smtx_typeof_bv_op_1_ret T R) := by
  cases T <;> simp [__smtx_typeof_bv_op_1_ret, type_result_seq_components_wf,
    hR]

theorem type_result_seq_components_wf_bv_op_2
    (T U : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_bv_op_2 T U) := by
  cases T <;> cases U <;>
    simp [__smtx_typeof_bv_op_2, type_result_seq_components_wf]
  all_goals
    apply type_result_seq_components_wf_native_ite <;>
      simp [type_result_seq_components_wf]

theorem type_result_seq_components_wf_bv_op_2_ret
    (T U R : SmtType)
    (hR : type_result_seq_components_wf R) :
    type_result_seq_components_wf (__smtx_typeof_bv_op_2_ret T U R) := by
  cases T <;> cases U <;> simp [__smtx_typeof_bv_op_2_ret,
    type_result_seq_components_wf, hR]
  all_goals
    apply type_result_seq_components_wf_native_ite <;>
      simp [type_result_seq_components_wf, hR]

theorem type_result_seq_components_wf_seq_op_1_ret
    (T R : SmtType)
    (hR : type_result_seq_components_wf R) :
    type_result_seq_components_wf (__smtx_typeof_seq_op_1_ret T R) := by
  cases T <;> simp [__smtx_typeof_seq_op_1_ret,
    type_result_seq_components_wf, hR]

theorem type_result_seq_components_wf_seq_op_2_ret
    (T U R : SmtType)
    (hR : type_result_seq_components_wf R) :
    type_result_seq_components_wf (__smtx_typeof_seq_op_2_ret T U R) := by
  cases T <;> cases U <;> simp [__smtx_typeof_seq_op_2_ret,
    type_result_seq_components_wf, hR, native_ite, native_Teq]
  all_goals
    apply type_result_seq_components_wf_if <;>
      simp [type_result_seq_components_wf, hR]

theorem type_result_seq_components_wf_seq_diff
    (T U : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_seq_diff T U) := by
  cases T <;> cases U <;> simp [__smtx_typeof_seq_diff,
    type_result_seq_components_wf, native_ite, native_Teq]
  all_goals
    apply type_result_seq_components_wf_if <;>
      simp [type_result_seq_components_wf]

theorem type_result_seq_components_wf_str_indexof
    (T U V : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_str_indexof T U V) := by
  cases T <;> cases U <;> cases V <;> simp [__smtx_typeof_str_indexof,
    type_result_seq_components_wf, native_ite, native_Teq]
  all_goals
    apply type_result_seq_components_wf_if <;>
      simp [type_result_seq_components_wf]

theorem type_result_seq_components_wf_str_indexof_re
    (T U V : SmtType) :
    type_result_seq_components_wf
      (if T = SmtType.Seq SmtType.Char then
        if U = SmtType.RegLan then
          if V = SmtType.Int then SmtType.Int else SmtType.None
        else SmtType.None
      else SmtType.None) := by
  by_cases hT : T = SmtType.Seq SmtType.Char <;>
    by_cases hU : U = SmtType.RegLan <;>
    by_cases hV : V = SmtType.Int <;>
    simp [hT, hU, hV, type_result_seq_components_wf]

theorem type_result_seq_components_wf_str_indexof_re_split
    (T U V : SmtType) :
    type_result_seq_components_wf
      (if T = SmtType.Seq SmtType.Char then
        if U = SmtType.RegLan then
          if V = SmtType.RegLan then SmtType.Int else SmtType.None
        else SmtType.None
      else SmtType.None) := by
  by_cases hT : T = SmtType.Seq SmtType.Char <;>
    by_cases hU : U = SmtType.RegLan <;>
    by_cases hV : V = SmtType.RegLan <;>
    simp [hT, hU, hV, type_result_seq_components_wf]

theorem type_result_seq_components_wf_re_exp
    (n : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_re_exp n T) := by
  cases n <;> try simp [__smtx_typeof_re_exp, type_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [type_result_seq_components_wf] <;>
      exact type_result_seq_components_wf_native_ite _ (by trivial) (by trivial)

theorem type_result_seq_components_wf_re_loop
    (m n : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_re_loop m n T) := by
  cases m <;> try simp [__smtx_typeof_re_loop, type_result_seq_components_wf]
  case Numeral i =>
    cases n <;> try simp [type_result_seq_components_wf]
    case Numeral j =>
      cases T <;> simp [type_result_seq_components_wf] <;>
        exact type_result_seq_components_wf_native_ite _
          (type_result_seq_components_wf_native_ite _ (by trivial) (by trivial))
          (by trivial)

theorem type_result_seq_components_wf_set_member
    (T U : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_set_member T U) := by
  cases T <;> cases U <;> simp [__smtx_typeof_set_member,
    type_result_seq_components_wf, native_ite, native_Teq]
  all_goals
    apply type_result_seq_components_wf_if <;> trivial

theorem type_result_seq_components_wf_sets_op_2_ret
    (T U R : SmtType)
    (hR : type_result_seq_components_wf R) :
    type_result_seq_components_wf (__smtx_typeof_sets_op_2_ret T U R) := by
  cases T <;> cases U <;> simp [__smtx_typeof_sets_op_2_ret,
    type_result_seq_components_wf, hR, native_ite, native_Teq]
  all_goals
    apply type_result_seq_components_wf_if
    · exact hR
    · trivial

theorem type_result_seq_components_wf_int_to_bv
    (n : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_int_to_bv n T) := by
  cases n <;> try simp [__smtx_typeof_int_to_bv, type_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [type_result_seq_components_wf] <;>
      exact type_result_seq_components_wf_native_ite _ (by trivial) (by trivial)

theorem type_result_seq_components_wf_concat
    (T U : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_concat T U) := by
  cases T <;> cases U <;> simp [__smtx_typeof_concat,
    type_result_seq_components_wf]

theorem type_result_seq_components_wf_extract
    (i j : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_extract i j T) := by
  cases i <;> try simp [__smtx_typeof_extract, type_result_seq_components_wf]
  case Numeral hi =>
    cases j <;> try simp [type_result_seq_components_wf]
    case Numeral lo =>
      cases T <;> try simp [type_result_seq_components_wf]
      case BitVec w =>
        cases h0 : native_zleq 0 lo <;>
          simp [type_result_seq_components_wf, native_ite] <;>
          apply type_result_seq_components_wf_if
        · apply type_result_seq_components_wf_if <;> trivial
        · trivial

theorem type_result_seq_components_wf_repeat
    (n : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_repeat n T) := by
  cases n <;> try simp [__smtx_typeof_repeat, type_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [type_result_seq_components_wf] <;>
      exact type_result_seq_components_wf_native_ite _ (by trivial) (by trivial)

theorem type_result_seq_components_wf_zero_extend
    (n : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_zero_extend n T) := by
  cases n <;> try simp [__smtx_typeof_zero_extend, type_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [type_result_seq_components_wf] <;>
      exact type_result_seq_components_wf_native_ite _ (by trivial) (by trivial)

theorem type_result_seq_components_wf_sign_extend
    (n : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_sign_extend n T) := by
  cases n <;> try simp [__smtx_typeof_sign_extend, type_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [type_result_seq_components_wf] <;>
      exact type_result_seq_components_wf_native_ite _ (by trivial) (by trivial)

theorem type_result_seq_components_wf_rotate_left
    (n : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_rotate_left n T) := by
  cases n <;> try simp [__smtx_typeof_rotate_left, type_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [type_result_seq_components_wf] <;>
      exact type_result_seq_components_wf_native_ite _ (by trivial) (by trivial)

theorem type_result_seq_components_wf_rotate_right
    (n : SmtTerm) (T : SmtType) :
    type_result_seq_components_wf (__smtx_typeof_rotate_right n T) := by
  cases n <;> try simp [__smtx_typeof_rotate_right, type_result_seq_components_wf]
  case Numeral k =>
    cases T <;> simp [type_result_seq_components_wf] <;>
      exact type_result_seq_components_wf_native_ite _ (by trivial) (by trivial)

theorem type_result_seq_components_wf_of_type_wf
    {T : SmtType} (h : __smtx_type_wf T = true) :
    type_result_seq_components_wf T := by
  let rec go (T : SmtType) (h : __smtx_type_wf T = true) :
      type_result_seq_components_wf T := by
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
      simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
        native_and] at h
    all_goals
      simp [type_result_seq_components_wf]
  exact go T h

theorem type_result_seq_components_wf_dt_cons_rec
    (T : SmtType) (hT : type_result_seq_components_wf T) :
    ∀ (d : SmtDatatype) (i : native_Nat),
      type_result_seq_components_wf (__smtx_typeof_dt_cons_rec T d i)
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero => by
      simpa [__smtx_typeof_dt_cons_rec] using hT
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero => by
      simpa [__smtx_typeof_dt_cons_rec, type_result_seq_components_wf] using
        type_result_seq_components_wf_dt_cons_rec T hT
          (SmtDatatype.sum c d) native_nat_zero
  | SmtDatatype.sum c d, native_nat_succ i => by
      simpa [__smtx_typeof_dt_cons_rec] using
        type_result_seq_components_wf_dt_cons_rec T hT d i
  | SmtDatatype.null, i => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec, type_result_seq_components_wf]

private theorem seq_char_wf :
    __smtx_type_wf (SmtType.Seq SmtType.Char) = true := by
  have hSeqInh :
      native_inhabited_type (SmtType.Seq SmtType.Char) = true :=
    native_inhabited_type_seq SmtType.Char
  have hCharInh : native_inhabited_type SmtType.Char = true :=
    native_inhabited_type_char
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, hSeqInh, hCharInh]

theorem smt_term_result_seq_components_wf_of_non_none
    (x : SmtTerm) (hxNN : term_has_non_none_type x) :
    type_result_seq_components_wf (__smtx_typeof x) := by
  let rec go (x : SmtTerm) (hxNN : term_has_non_none_type x) :
      type_result_seq_components_wf (__smtx_typeof x) := by
    cases x
    case _at_purify t =>
      have htNN : term_has_non_none_type t := by
        unfold term_has_non_none_type at hxNN ⊢
        simpa [__smtx_typeof] using hxNN
      simpa [__smtx_typeof] using go t htNN
    case String s =>
      cases hValid : native_string_valid s <;>
        simp [__smtx_typeof, native_ite, hValid, type_result_seq_components_wf, seq_char_wf]
    case Var s T =>
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      simpa [__smtx_typeof,
        smtx_typeof_guard_wf_of_non_none T T hGuardNN] using
        type_result_seq_components_wf_of_type_wf hWf
    case UConst s T =>
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      simpa [__smtx_typeof,
        smtx_typeof_guard_wf_of_non_none T T hGuardNN] using
        type_result_seq_components_wf_of_type_wf hWf
    case «exists» s T body =>
      have hBody : __smtx_typeof body = SmtType.Bool :=
        exists_body_bool_of_non_none hxNN
      have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
        simpa [native_Teq] using hBody
      have hGuardNN : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        intro hNone
        apply hxNN
        rw [smtx_typeof_exists_term_eq]
        simp [hEq, native_ite, hNone]
      have hGuard : __smtx_typeof_guard_wf T SmtType.Bool = SmtType.Bool :=
        smtx_typeof_guard_wf_of_non_none T SmtType.Bool hGuardNN
      rw [smtx_typeof_exists_term_eq]
      simp [hEq, native_ite, hGuard, type_result_seq_components_wf]
    case «forall» s T body =>
      have hBody : __smtx_typeof body = SmtType.Bool :=
        forall_body_bool_of_non_none hxNN
      have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
        simpa [native_Teq] using hBody
      have hGuardNN : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        intro hNone
        apply hxNN
        rw [smtx_typeof_forall_term_eq]
        simp [hEq, native_ite, hNone]
      have hGuard : __smtx_typeof_guard_wf T SmtType.Bool = SmtType.Bool :=
        smtx_typeof_guard_wf_of_non_none T SmtType.Bool hGuardNN
      rw [smtx_typeof_forall_term_eq]
      simp [hEq, native_ite, hGuard, type_result_seq_components_wf]
    case seq_empty T =>
      have hGuardNN : __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) ≠
          SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf (SmtType.Seq T) = true :=
        smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuardNN
      rw [smtx_typeof_seq_empty_term_eq,
        smtx_typeof_guard_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuardNN]
      exact hWf
    case set_empty T =>
      have hGuardNN : __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) ≠
          SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf (SmtType.Set T) = true :=
        smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuardNN
      rw [smtx_typeof_set_empty_term_eq,
        smtx_typeof_guard_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuardNN]
      exact hWf
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
      rw [smtx_typeof_seq_unit_term_eq,
        smtx_typeof_guard_wf_of_non_none (SmtType.Seq (__smtx_typeof t))
          (SmtType.Seq (__smtx_typeof t)) hGuardNN]
      exact hWf
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
      rw [smtx_typeof_set_singleton_term_eq,
        smtx_typeof_guard_wf_of_non_none (SmtType.Set (__smtx_typeof t))
          (SmtType.Set (__smtx_typeof t)) hGuardNN]
      exact hWf
    case str_concat x y =>
      rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat)
          (typeof_str_concat_eq x y) hxNN with ⟨T, hxT, hyT⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_concat_eq x y, hxT, hyT]
      simpa [__smtx_typeof_seq_op_2, native_ite, native_Teq, hxT,
        type_result_seq_components_wf] using hxGood
    case str_rev t =>
      rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
          (typeof_str_rev_eq t) hxNN with ⟨T, htT⟩
      have htNN : term_has_non_none_type t :=
        _root_.term_has_non_none_of_type_eq htT (by simp)
      have htGood := go t htNN
      rw [typeof_str_rev_eq t, htT]
      simpa [__smtx_typeof_seq_op_1, htT,
        type_result_seq_components_wf] using htGood
    case str_substr x y z =>
      rcases str_substr_args_of_non_none hxNN with ⟨T, hxT, hy, hz⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_substr_eq x y z]
      simp [__smtx_typeof_str_substr, hxT, hy, hz]
      simpa [hxT, type_result_seq_components_wf] using hxGood
    case str_replace x y z =>
      rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
          (typeof_str_replace_eq x y z) hxNN with ⟨T, hxT, hyT, hzT⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_replace_eq x y z, hxT, hyT, hzT]
      simpa [__smtx_typeof_seq_op_3, native_ite, native_Teq, hxT,
        type_result_seq_components_wf] using hxGood
    case str_replace_all x y z =>
      rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
          (typeof_str_replace_all_eq x y z) hxNN with ⟨T, hxT, hyT, hzT⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_replace_all_eq x y z, hxT, hyT, hzT]
      simpa [__smtx_typeof_seq_op_3, native_ite, native_Teq, hxT,
        type_result_seq_components_wf] using hxGood
    case str_at x y =>
      rcases str_at_args_of_non_none hxNN with ⟨T, hxT, hy⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_at_eq x y]
      simp [__smtx_typeof_str_at, hxT, hy]
      simpa [hxT, type_result_seq_components_wf] using hxGood
    case str_update x y z =>
      rcases str_update_args_of_non_none hxNN with ⟨T, hxT, hy, hzT⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxT (by simp)
      have hxGood := go x hxNN'
      rw [typeof_str_update_eq x y z]
      simpa [__smtx_typeof_str_update, native_ite, native_Teq, hxT, hy,
        hzT, type_result_seq_components_wf] using hxGood
    case str_to_lower t =>
      have ht : __smtx_typeof t = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
          (typeof_str_to_lower_eq t) hxNN
      rw [typeof_str_to_lower_eq, ht]
      simpa [type_result_seq_components_wf, native_ite] using seq_char_wf
    case str_to_upper t =>
      have ht : __smtx_typeof t = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
          (typeof_str_to_upper_eq t) hxNN
      rw [typeof_str_to_upper_eq, ht]
      simpa [type_result_seq_components_wf, native_ite] using seq_char_wf
    case str_from_code t =>
      rw [typeof_str_from_code_eq]
      cases h : __smtx_typeof t <;>
        simp [type_result_seq_components_wf, native_ite, native_Teq]
      exact seq_char_wf
    case str_from_int t =>
      rw [typeof_str_from_int_eq]
      cases h : __smtx_typeof t <;>
        simp [type_result_seq_components_wf, native_ite, native_Teq]
      exact seq_char_wf
    case str_replace_re x y z =>
      rw [typeof_str_replace_re_eq x y z]
      rcases str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re)
          (typeof_str_replace_re_eq x y z) hxNN with ⟨hx, hy, hz⟩
      simpa [hx, hy, hz, type_result_seq_components_wf, native_ite] using seq_char_wf
    case str_replace_re_all x y z =>
      rw [typeof_str_replace_re_all_eq x y z]
      rcases str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all)
          (typeof_str_replace_re_all_eq x y z) hxNN with ⟨hx, hy, hz⟩
      simpa [hx, hy, hz, type_result_seq_components_wf, native_ite] using seq_char_wf
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
        type_result_seq_components_wf_of_type_wf hWf
    case select x y =>
      rcases select_args_of_non_none hxNN with ⟨A, B, hxMap, hyA⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxMap (by simp)
      have hxGood := go x hxNN'
      have hBGood : type_result_seq_components_wf B := by
        rw [hxMap] at hxGood
        exact type_result_seq_components_wf_of_type_wf
          (map_type_wf_components_of_wf hxGood).2
      rw [typeof_select_eq x y]
      simpa [__smtx_typeof_select, native_ite, native_Teq, hxMap, hyA] using hBGood
    case store x y z =>
      rcases store_args_of_non_none hxNN with ⟨A, B, hxMap, hyA, hzB⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxMap (by simp)
      have hxGood := go x hxNN'
      rw [typeof_store_eq x y z]
      simpa [__smtx_typeof_store, native_ite, native_Teq, hxMap, hyA, hzB,
        type_result_seq_components_wf] using hxGood
    case map_diff x y =>
      rcases map_diff_args_of_non_none hxNN with hMap | hSet
      · rcases hMap with ⟨A, B, hxMap, hyMap, hTy⟩
        have hxNN' : term_has_non_none_type x :=
          _root_.term_has_non_none_of_type_eq hxMap (by simp)
        have hxGood := go x hxNN'
        have hMapWf : __smtx_type_wf (SmtType.Map A B) = true := by
          simpa [hxMap, type_result_seq_components_wf] using hxGood
        rw [hTy]
        exact type_result_seq_components_wf_of_type_wf
          (map_type_wf_components_of_wf hMapWf).1
      · rcases hSet with ⟨A, hxSet, hySet, hTy⟩
        have hxNN' : term_has_non_none_type x :=
          _root_.term_has_non_none_of_type_eq hxSet (by simp)
        have hxGood := go x hxNN'
        have hSetWf : __smtx_type_wf (SmtType.Set A) = true := by
          simpa [hxSet, type_result_seq_components_wf] using hxGood
        rw [hTy]
        exact type_result_seq_components_wf_of_type_wf
          (set_type_wf_component_of_wf hSetWf)
    case ite c x y =>
      rcases ite_args_of_non_none hxNN with ⟨T, hc, hxT, hyT, hTNN⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxT hTNN
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
      exact type_result_seq_components_wf_of_type_wf hWf
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
      exact type_result_seq_components_wf_dt_cons_rec (SmtType.Datatype s d)
        (by simpa [type_result_seq_components_wf] using hBaseWf)
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
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
        exact type_result_seq_components_wf_of_type_wf hWf
      · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
        · rcases hTesterWitness with ⟨s, d, i, rfl⟩
          rw [dt_tester_term_typeof_of_non_none hxNN]
          simp [type_result_seq_components_wf]
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
              simpa [hF, type_result_seq_components_wf] using hfGood
            exact type_result_seq_components_wf_of_type_wf
              (fun_type_wf_components_of_wf hHeadGood).2
          · simpa [hF, type_result_seq_components_wf] using hfGood
    case set_union x y =>
      rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
          (typeof_set_union_eq x y) hxNN with ⟨A, hxSet, hySet⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxSet (by simp)
      have hxGood := go x hxNN'
      rw [typeof_set_union_eq x y, hxSet, hySet]
      simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
      simpa [hxSet, type_result_seq_components_wf] using hxGood
    case set_inter x y =>
      rcases set_binop_args_of_non_none (op := SmtTerm.set_inter)
          (typeof_set_inter_eq x y) hxNN with ⟨A, hxSet, hySet⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxSet (by simp)
      have hxGood := go x hxNN'
      rw [typeof_set_inter_eq x y, hxSet, hySet]
      simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
      simpa [hxSet, type_result_seq_components_wf] using hxGood
    case set_minus x y =>
      rcases set_binop_args_of_non_none (op := SmtTerm.set_minus)
          (typeof_set_minus_eq x y) hxNN with ⟨A, hxSet, hySet⟩
      have hxNN' : term_has_non_none_type x :=
        _root_.term_has_non_none_of_type_eq hxSet (by simp)
      have hxGood := go x hxNN'
      rw [typeof_set_minus_eq x y, hxSet, hySet]
      simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
      simpa [hxSet, type_result_seq_components_wf] using hxGood
    all_goals
      repeat split
      all_goals
      simp [type_result_seq_components_wf, __smtx_typeof, native_ite,
        native_Teq, type_result_seq_components_wf_typeof_eq,
        type_result_seq_components_wf_arith_overload_op_1,
        type_result_seq_components_wf_arith_overload_op_2,
        type_result_seq_components_wf_bv_op_1,
        type_result_seq_components_wf_bv_op_2,
        type_result_seq_components_wf_seq_diff,
        type_result_seq_components_wf_str_indexof,
        type_result_seq_components_wf_str_indexof_re,
        type_result_seq_components_wf_str_indexof_re_split,
        type_result_seq_components_wf_re_exp,
        type_result_seq_components_wf_re_loop,
        type_result_seq_components_wf_set_member,
        type_result_seq_components_wf_int_to_bv,
        type_result_seq_components_wf_concat,
        type_result_seq_components_wf_extract,
        type_result_seq_components_wf_repeat,
        type_result_seq_components_wf_zero_extend,
        type_result_seq_components_wf_sign_extend,
        type_result_seq_components_wf_rotate_left,
        type_result_seq_components_wf_rotate_right]
      all_goals first
        | exact type_result_seq_components_wf_arith_overload_op_2_ret _ _ _
            (by trivial)
        | exact type_result_seq_components_wf_bv_op_1_ret _ _ (by trivial)
        | exact type_result_seq_components_wf_bv_op_2_ret _ _ _ (by trivial)
        | exact type_result_seq_components_wf_seq_op_1_ret _ _ (by trivial)
        | exact type_result_seq_components_wf_seq_op_2_ret _ _ _ (by trivial)
        | exact type_result_seq_components_wf_sets_op_2_ret _ _ _ (by trivial)
        | (repeat (first
              | apply type_result_seq_components_wf_if
              | apply type_result_seq_components_wf_native_ite)
           all_goals trivial)
  exact go x hxNN

theorem smt_seq_component_wf_of_non_none_type
    (x : SmtTerm) (T : SmtType)
    (hxTy : __smtx_typeof x = SmtType.Seq T) :
    type_inhabited T ∧ __smtx_type_wf T = true := by
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    exact seq_ne_none T
  have hGood := smt_term_result_seq_components_wf_of_non_none x hxNN
  rw [hxTy] at hGood
  have hTWf : __smtx_type_wf T = true :=
    seq_type_wf_component_of_wf hGood
  exact ⟨_root_.type_inhabited_of_type_wf T hTWf, hTWf⟩

theorem eval_seq_empty_of_type (M : SmtModel) (A : Term) (T : SmtType) :
    __eo_to_smt_type A = SmtType.Seq T ->
    __smtx_model_eval M (__eo_to_smt (__seq_empty A)) =
      SmtValue.Seq (SmtSeq.empty T) := by
  intro hA
  by_cases hSpecial : A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst hSpecial
    simp [__eo_to_smt_type, __smtx_typeof_guard] at hA
    cases hA
    change __smtx_model_eval M (SmtTerm.String (native_string_lit "")) =
      SmtValue.Seq (SmtSeq.empty SmtType.Char)
    rw [__smtx_model_eval.eq_4]
    simp [native_pack_string, native_string_lit, native_pack_seq]
  · by_cases hStuck : A = Term.Stuck
    · subst hStuck
      simp [__eo_to_smt_type] at hA
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault]
      rw [show __eo_to_smt (Term.seq_empty A) =
          __eo_to_smt_seq_empty (__eo_to_smt_type A) by
        rfl]
      rw [hA]
      change __smtx_model_eval M (SmtTerm.seq_empty T) =
        SmtValue.Seq (SmtSeq.empty T)
      rw [__smtx_model_eval.eq_79]

theorem eval_seq_empty_typeof (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  exact eval_seq_empty_of_type M (__eo_typeof x) T hA

theorem smt_typeof_seq_empty_of_type (A : Term) (T : SmtType) :
    __eo_to_smt_type A = SmtType.Seq T ->
    __smtx_typeof (__eo_to_smt (__seq_empty A)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (__seq_empty A)) = SmtType.Seq T := by
  intro hA hEmptyNN
  by_cases hSpecial : A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst hSpecial
    simp [__eo_to_smt_type, __smtx_typeof_guard] at hA
    cases hA
    change __smtx_typeof (SmtTerm.String (native_string_lit "")) = SmtType.Seq SmtType.Char
    rw [__smtx_typeof.eq_4]
    simp [native_string_lit, native_string_valid, native_ite]
  · by_cases hStuck : A = Term.Stuck
    · subst hStuck
      simp [__eo_to_smt_type] at hA
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault] at hEmptyNN
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None at hEmptyNN
      rw [hA] at hEmptyNN
      change __smtx_typeof (SmtTerm.seq_empty T) ≠ SmtType.None at hEmptyNN
      rw [hDefault]
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
        SmtType.Seq T
      rw [hA]
      exact TranslationProofs.smtx_typeof_seq_empty_of_non_none T hEmptyNN

theorem smt_typeof_seq_empty_seq_of_non_none (A : Term)
    (hEmptyNN : __smtx_typeof (__eo_to_smt (__seq_empty A)) ≠
      SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt (__seq_empty A)) = SmtType.Seq T := by
  by_cases hSpecial :
      A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst A
    exact ⟨SmtType.Char, by
      change __smtx_typeof (SmtTerm.String (native_string_lit "")) =
        SmtType.Seq SmtType.Char
      rw [__smtx_typeof.eq_4]
      simp [native_string_lit, native_string_valid, native_ite]⟩
  · by_cases hStuck : A = Term.Stuck
    · subst A
      have hNone : __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.None := by
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
      exact False.elim (hEmptyNN (by simpa [__seq_empty] using hNone))
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault] at hEmptyNN ⊢
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None at hEmptyNN
      change ∃ T,
        __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
          SmtType.Seq T
      cases hA : __eo_to_smt_type A <;>
        simp [__eo_to_smt_seq_empty, hA] at hEmptyNN ⊢
      rename_i T
      exact ⟨T, TranslationProofs.smtx_typeof_seq_empty_of_non_none T
        (by simpa [__eo_to_smt_seq_empty, hA] using hEmptyNN)⟩

theorem eo_to_smt_type_seq_of_seq_empty_non_none (A : Term)
    (hEmptyNN : __smtx_typeof (__eo_to_smt (__seq_empty A)) ≠
      SmtType.None) :
    ∃ T,
      __eo_to_smt_type A = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__seq_empty A)) =
          SmtType.Seq T := by
  by_cases hSpecial :
      A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst A
    exact ⟨SmtType.Char, by
      have hNe : SmtType.Char ≠ SmtType.None := by
        intro h
        cases h
      simp [__eo_to_smt_type, __smtx_typeof_guard, native_Teq, native_ite,
        hNe],
      by
        change __smtx_typeof (SmtTerm.String (native_string_lit "")) =
          SmtType.Seq SmtType.Char
        rw [__smtx_typeof.eq_4]
        simp [native_string_lit, native_string_valid, native_ite]⟩
  · by_cases hStuck : A = Term.Stuck
    · subst A
      have hNone : __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.None := by
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
      exact False.elim (hEmptyNN (by simpa [__seq_empty] using hNone))
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault] at hEmptyNN ⊢
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None at hEmptyNN
      change ∃ T,
        __eo_to_smt_type A = SmtType.Seq T ∧
          __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
            SmtType.Seq T
      cases hA : __eo_to_smt_type A <;>
        simp [__eo_to_smt_seq_empty, hA] at hEmptyNN
      rename_i T
      exact ⟨T, rfl,
        TranslationProofs.smtx_typeof_seq_empty_of_non_none T
          (by simpa [__eo_to_smt_seq_empty, hA] using hEmptyNN)⟩

theorem smt_typeof_seq_of_seq_empty_typeof_non_none
    (x : Term)
    (hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None) :
    ∃ T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T := by
  rcases eo_to_smt_type_seq_of_seq_empty_non_none (__eo_typeof x)
      hEmptyNN with ⟨T, hType, hEmptyTy⟩
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXNN
  exact ⟨T, by rw [hTypeMatch, hType], hEmptyTy⟩

theorem smt_typeof_eq_seq_empty_seq_of_non_none
    (x A : Term)
    (hEq : x = __seq_empty A)
    (hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  subst x
  exact smt_typeof_seq_empty_seq_of_non_none A hXNN

theorem smt_typeof_seq_empty_typeof (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  exact smt_typeof_seq_empty_of_type (__eo_typeof x) T hA hEmptyNN

theorem seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
      SmtType.None := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true := by
    have hGood :=
      smt_term_result_seq_components_wf_of_non_none (__eo_to_smt x) hTrans
    rw [hxTy] at hGood
    change __smtx_type_wf (SmtType.Seq T) = true at hGood
    exact hGood
  by_cases hSpecial :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · rw [hSpecial]
    change __smtx_typeof (SmtTerm.String (native_string_lit "")) ≠ SmtType.None
    rw [__smtx_typeof.eq_4]
    exact seq_ne_none SmtType.Char
  · by_cases hStuck : __eo_typeof x = Term.Stuck
    · rw [hStuck] at hA
      simp [__eo_to_smt_type] at hA
    · have hDefault :
          __seq_empty (__eo_typeof x) = Term.seq_empty (__eo_typeof x) := by
        cases hTy : __eo_typeof x <;>
          simp [__seq_empty, hTy] at hStuck hSpecial ⊢
        case Apply f a =>
          cases f <;> simp at hSpecial ⊢
          case UOp op =>
            cases op <;> simp at hSpecial ⊢
            case Seq =>
              cases a <;> simp at hSpecial ⊢
              case UOp op' =>
                cases op' <;> simp at hSpecial ⊢
      rw [hDefault]
      change
        __smtx_typeof (__eo_to_smt_seq_empty
          (__eo_to_smt_type (__eo_typeof x))) ≠ SmtType.None
      rw [hA]
      change __smtx_typeof (SmtTerm.seq_empty T) ≠ SmtType.None
      simp [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hSeqWF]

theorem eo_disamb_type_seq_empty_stuck_of_not_seq
    (A : Term)
    (hNotSeq : ¬ ∃ T, A = Term.Apply (Term.UOp UserOp.Seq) T) :
    __eo_disamb_type_seq_empty A = Term.Stuck := by
  cases A with
  | Apply f a =>
      cases f with
      | UOp op =>
          by_cases hop : op = UserOp.Seq
          · subst op
            exact False.elim (hNotSeq ⟨a, rfl⟩)
          · simp [__eo_disamb_type_seq_empty, hop]
      | _ =>
          simp [__eo_disamb_type_seq_empty]
  | _ =>
      simp [__eo_disamb_type_seq_empty]

theorem seq_empty_default_of_not_seq_ne_stuck
    (A : Term)
    (hA : A ≠ Term.Stuck)
    (hNotSeq : ¬ ∃ T, A = Term.Apply (Term.UOp UserOp.Seq) T) :
    __seq_empty A = Term.seq_empty A := by
  cases A with
  | Stuck =>
      exact False.elim (hA rfl)
  | Apply f a =>
      cases f with
      | UOp op =>
          by_cases hop : op = UserOp.Seq
          · subst op
            exact False.elim (hNotSeq ⟨a, rfl⟩)
          · simp [__seq_empty, hop]
      | _ =>
          simp [__seq_empty]
  | _ =>
      simp [__seq_empty]

theorem eo_typeof_seq_empty_stuck_of_not_seq_ne_stuck
    (A : Term)
    (hA : A ≠ Term.Stuck)
    (hNotSeq : ¬ ∃ T, A = Term.Apply (Term.UOp UserOp.Seq) T) :
    __eo_typeof (Term.seq_empty A) = Term.Stuck := by
  change __eo_typeof_seq_empty (__eo_typeof A) A = Term.Stuck
  by_cases hType : __eo_typeof A = Term.Type
  · rw [hType]
    simpa [__eo_typeof_seq_empty, hA] using
      eo_disamb_type_seq_empty_stuck_of_not_seq A hNotSeq
  · cases hTy : __eo_typeof A <;>
      simp [__eo_typeof_seq_empty, hTy] at hType ⊢

theorem seq_empty_typeof_seq_type_of_elim_ne_stuck
    (A : Term)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty A)) ≠ SmtType.None)
    (hElim : __str_nary_elim (__seq_empty A) ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Seq) T := by
  rcases eo_to_smt_type_seq_of_seq_empty_non_none A hEmptyNN with
    ⟨T, hType, _hEmptyTy⟩
  rcases TranslationProofs.eo_to_smt_type_eq_seq hType with
    ⟨U, hA, _hU⟩
  exact ⟨U, hA⟩

theorem seq_empty_typeof_has_smt_translation_of_elim_ne_stuck
    (x : Term)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hxSeq : ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim :
      __str_nary_elim (__seq_empty (__eo_typeof x)) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
      SmtType.None := by
  rcases hxSeq with ⟨T, hxTy⟩
  rcases smt_seq_component_wf_of_non_none_type
      (__eo_to_smt x) T hxTy with
    ⟨hInh, hWf⟩
  exact seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
    x T hxTy hInh hWf


theorem smtx_model_eval_str_concat_term_eq (M : SmtModel) (x y : Term) :
    __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
      __smtx_model_eval_str_concat (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  rw [show __eo_to_smt (mkConcat x y) =
      SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y) by
    rfl]
  rw [__smtx_model_eval.eq_81]

theorem str_concat_args_of_non_none (x y : Term) :
    __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None ->
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  intro h
  have h' :
      term_has_non_none_type (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change
      __smtx_typeof (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at h
    exact h
  exact seq_binop_args_of_non_none (op := SmtTerm.str_concat)
    (typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y)) h'

theorem smt_typeof_str_concat_of_seq (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Seq T
  rw [typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y)]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, hxTy, hyTy]

theorem str_concat_args_of_seq_type (x y : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  have hNN :
      __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
    rw [hTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none x y hNN with ⟨U, hxTyU, hyTyU⟩
  have hConcatTyU :
      __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq x y U hxTyU hyTyU
  have hUT : U = T := by
    have hSeq : SmtType.Seq U = SmtType.Seq T := by
      rw [← hConcatTyU, hTy]
    injection hSeq
  constructor
  · simpa [hUT] using hxTyU
  · simpa [hUT] using hyTyU

theorem smt_typeof_str_concat_seq_of_non_none (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T := by
  rcases str_concat_args_of_non_none x y hNN with ⟨T, hxTy, hyTy⟩
  exact ⟨T, smt_typeof_str_concat_of_seq x y T hxTy hyTy⟩

theorem strConcat_nil_is_list_nil_of_type {ty : Term} {T : SmtType}
    (hTy : __eo_to_smt_type ty = SmtType.Seq T) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
        (__eo_nil (Term.UOp UserOp.str_concat) ty) =
      Term.Boolean true := by
  rcases TranslationProofs.eo_to_smt_type_eq_seq hTy with ⟨V, hTyEq, _hV⟩
  subst ty
  cases V <;>
    simp [__eo_nil, __eo_nil_str_concat, __seq_empty, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_eq, native_teq]
  case UOp op =>
    cases op <;> simp

theorem strConcat_nil_eq_seq_empty_of_type {ty : Term} {T : SmtType}
    (hTy : __eo_to_smt_type ty = SmtType.Seq T) :
    __eo_nil (Term.UOp UserOp.str_concat) ty = __seq_empty ty := by
  rcases TranslationProofs.eo_to_smt_type_eq_seq hTy with ⟨V, hTyEq, _hV⟩
  subst ty
  rfl

theorem eo_is_list_boolean_of_ne_stuck (f x : Term)
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    ∃ b, __eo_is_list f x = Term.Boolean b := by
  refine ⟨native_not (native_teq (__eo_get_nil_rec f x) Term.Stuck), ?_⟩
  cases f <;> cases x <;>
    simp [__eo_is_list, __eo_is_ok] at hf hx ⊢

theorem eq_of_eo_eq_true_local (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

theorem eo_eq_true_left_concat_right_not_concat_false
    (sHead sTail t : Term)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hHead : __eo_eq (mkConcat sHead sTail) t = Term.Boolean true) :
    False := by
  have hT : t = mkConcat sHead sTail :=
    eq_of_eo_eq_true_local (mkConcat sHead sTail) t hHead
  exact hTNotConcat ⟨sHead, sTail, hT⟩

theorem eo_eq_true_left_not_concat_right_concat_false
    (s tHead tTail : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hHead : __eo_eq s (mkConcat tHead tTail) = Term.Boolean true) :
    False := by
  have hT : mkConcat tHead tTail = s :=
    eq_of_eo_eq_true_local s (mkConcat tHead tTail) hHead
  exact hSNotConcat ⟨tHead, tTail, hT.symm⟩

theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

theorem eo_eq_cases_of_ne_stuck (x y : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_eq x y = Term.Boolean true ∨
      __eo_eq x y = Term.Boolean false := by
  by_cases hxy : y = x
  · subst y
    exact Or.inl (eo_eq_self_true_of_ne_stuck x hx)
  · right
    cases x <;> cases y <;>
      simp [__eo_eq, native_teq] at hx hy hxy ⊢
    all_goals assumption

theorem eo_eq_cases_of_has_bool_type (x y : Term)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x y)) :
    __eo_eq x y = Term.Boolean true ∨
      __eo_eq x y = Term.Boolean false := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y
      hBool with ⟨hSame, hXNN⟩
  have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    rw [← hSame]
    exact hXNN
  exact eo_eq_cases_of_ne_stuck x y
    (RuleProofs.term_ne_stuck_of_has_smt_translation x hXNN)
    (RuleProofs.term_ne_stuck_of_has_smt_translation y hYNN)

theorem eo_ite_true (x y : Term) :
    __eo_ite (Term.Boolean true) x y = x := by
  rfl

theorem eo_ite_false (x y : Term) :
    __eo_ite (Term.Boolean false) x y = y := by
  rfl

theorem eo_ite_cases_of_ne_stuck (c x y : Term) :
    __eo_ite c x y ≠ Term.Stuck ->
    c = Term.Boolean true ∨ c = Term.Boolean false := by
  intro h
  by_cases hTrue : native_teq c (Term.Boolean true) = true
  · left
    simpa [native_teq] using hTrue
  · by_cases hFalse : native_teq c (Term.Boolean false) = true
    · right
      simpa [native_teq] using hFalse
    · simp [__eo_ite, hTrue, hFalse, SmtEval.native_ite] at h

theorem eo_requires_self_eq_of_ne_stuck (x z : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_requires x x z = z := by
  simp [__eo_requires, hx, native_teq, SmtEval.native_ite, SmtEval.native_not]

theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : native_teq x y = true
  · by_cases hxOk : native_not (native_teq x Term.Stuck) = true
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite]
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite] at h
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h hStuck
  subst x
  simp [__eo_requires, native_teq, SmtEval.native_ite, SmtEval.native_not] at h

theorem eo_requires_result_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro h
  rw [← eo_requires_eq_result_of_ne_stuck x y z h]
  exact h

theorem eo_is_ok_ne_stuck_of_true (x : Term) :
    __eo_is_ok x = Term.Boolean true ->
    x ≠ Term.Stuck := by
  intro h hx
  subst x
  simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at h

theorem eo_is_ok_true_of_ne_stuck (x : Term) :
    x ≠ Term.Stuck ->
    __eo_is_ok x = Term.Boolean true := by
  intro hNe
  cases x <;> simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at hNe ⊢

theorem eo_get_nil_rec_ne_stuck_of_is_list_true (f x : Term) :
    __eo_is_list f x = Term.Boolean true ->
    __eo_get_nil_rec f x ≠ Term.Stuck := by
  intro h
  have hOk : __eo_is_ok (__eo_get_nil_rec f x) = Term.Boolean true := by
    cases f <;> cases x <;>
      simp [__eo_is_list] at h ⊢ <;> exact h
  exact eo_is_ok_ne_stuck_of_true (__eo_get_nil_rec f x) hOk

theorem eo_is_list_true_of_get_nil_rec_ne_stuck (f x : Term) :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  intro hRec
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst f
    simp [__eo_get_nil_rec] at hRec
  have hX : x ≠ Term.Stuck := by
    intro hX
    subst x
    simp [__eo_get_nil_rec] at hRec
  simp [__eo_is_list, eo_is_ok_true_of_ne_stuck (__eo_get_nil_rec f x) hRec]

theorem eo_is_list_cons_head_eq_of_true (f g x y : Term) :
    __eo_is_list f (Term.Apply (Term.Apply g x) y) = Term.Boolean true ->
    g = f := by
  intro h
  have hRec :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f
      (Term.Apply (Term.Apply g x) y) h
  have hReq :
      __eo_requires f g (__eo_get_nil_rec f y) ≠ Term.Stuck := by
    cases f <;> simp [__eo_get_nil_rec] at hRec ⊢ <;> exact hRec
  exact (eo_requires_eq_of_ne_stuck f g (__eo_get_nil_rec f y) hReq).symm

theorem eo_is_list_tail_true_of_cons_self (f x y : Term) :
    __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true ->
    __eo_is_list f y = Term.Boolean true := by
  intro h
  have hRec :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f
      (Term.Apply (Term.Apply f x) y) h
  have hReq :
      __eo_requires f f (__eo_get_nil_rec f y) ≠ Term.Stuck := by
    cases f <;> simp [__eo_get_nil_rec] at hRec ⊢ <;> exact hRec
  have hTail : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck f f (__eo_get_nil_rec f y) hReq
  exact eo_is_list_true_of_get_nil_rec_ne_stuck f y hTail

theorem eo_get_nil_rec_cons_self_eq_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_get_nil_rec f (Term.Apply (Term.Apply f x) y) =
      __eo_get_nil_rec f y := by
  cases f <;> simp [__eo_get_nil_rec] at hF ⊢
  all_goals
    simp [__eo_requires, native_teq, native_ite, SmtEval.native_ite,
      SmtEval.native_not]

theorem eo_get_nil_rec_str_concat_eq_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil = nil := by
  cases nil <;>
    simp [__eo_get_nil_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq, __eo_requires, native_ite, SmtEval.native_ite,
      SmtEval.native_not] at hNil ⊢
  case UOp1 op A =>
    cases op <;>
      simp at hNil ⊢
  case String s =>
    subst s
    simp

theorem eo_list_rev_str_concat_nil_eq_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_list_rev (Term.UOp UserOp.str_concat) nil = nil := by
  cases nil <;>
    simp [__eo_list_rev, __eo_is_list, __eo_get_nil_rec,
      __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_is_ok, __eo_eq, native_teq, __eo_requires, native_ite,
      SmtEval.native_ite, SmtEval.native_not] at hNil ⊢
  case UOp1 op A =>
    cases op <;>
      simp [
        __eo_list_rev_rec
        
        ] at hNil ⊢
  case String s =>
    subst s
    simp [__eo_list_rev_rec
      
      
      ]

theorem eo_list_rev_rec_str_concat_nil_eq_of_nil_true
    (nil acc : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_list_rev_rec nil acc = acc := by
  cases nil <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq] at hNil
  case UOp1 op A =>
    cases op <;>
      simp at hNil
    case seq_empty =>
      cases acc <;> rfl
  case String s =>
    subst s
    cases acc <;> rfl

theorem eo_is_list_str_concat_nil_true_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true := by
  cases nil <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_is_ok, __eo_eq, native_teq,
      __eo_requires, native_ite, SmtEval.native_ite, SmtEval.native_not] at hNil ⊢
  case UOp1 op A =>
    cases op <;>
      simp at hNil ⊢
  case String s =>
    subst s
    simp

theorem eo_is_list_nil_str_concat_boolean_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
      Term.Boolean b := by
  cases x <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
      native_teq] at hx ⊢
  case UOp1 op A =>
    cases op <;> simp

theorem eo_is_list_cons_self_true_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true := by
  have hRec : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f y hTail
  have hGet :
      __eo_get_nil_rec f (Term.Apply (Term.Apply f x) y) ≠ Term.Stuck := by
    rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTail]
    exact hRec
  exact eo_is_list_true_of_get_nil_rec_ne_stuck f
    (Term.Apply (Term.Apply f x) y) hGet

theorem eo_list_rev_is_list_true_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  exact eo_requires_eq_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
    (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

theorem eo_list_rev_rec_ne_stuck_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_list_rev_rec a (__eo_get_nil_rec f a) ≠ Term.Stuck := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  exact eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
    (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

theorem eo_list_rev_eq_rec_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_list_rev f a = __eo_list_rev_rec a (__eo_get_nil_rec f a) := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  simpa [__eo_list_rev] using
    eo_requires_eq_result_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

theorem eo_list_rev_arg_ne_stuck_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    a ≠ Term.Stuck := by
  intro h ha
  subst a
  cases f <;>
    simp [__eo_list_rev, __eo_is_list, __eo_requires, native_ite, native_teq] at h

theorem eo_list_rev_rec_cons (f x y acc : Term)
    (hAcc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) := by
  cases acc <;> simp [__eo_list_rev_rec] at hAcc ⊢

theorem eo_list_rev_cons_eq_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_list_rev f (Term.Apply (Term.Apply f x) y) =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x)
        (__eo_get_nil_rec f y)) := by
  have hRec : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f y hTail
  have hConsList :
      __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list f x y hF hTail
  rw [__eo_list_rev]
  rw [hConsList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_list_rev_rec (Term.Apply (Term.Apply f x) y)
      (__eo_get_nil_rec f (Term.Apply (Term.Apply f x) y))) (by decide)]
  rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTail]
  exact eo_list_rev_rec_cons f x y (__eo_get_nil_rec f y) hRec

theorem eo_list_rev_cons_tail_list_of_ne_stuck (f x y : Term)
    (hRev : __eo_list_rev f (Term.Apply (Term.Apply f x) y) ≠
      Term.Stuck) :
    __eo_is_list f y = Term.Boolean true := by
  have hList :
      __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck f (Term.Apply (Term.Apply f x) y)
      hRev
  exact eo_is_list_tail_true_of_cons_self f x y hList

theorem eo_list_rev_cons_eq_of_ne_stuck (f x y : Term)
    (hRev : __eo_list_rev f (Term.Apply (Term.Apply f x) y) ≠
      Term.Stuck) :
    __eo_list_rev f (Term.Apply (Term.Apply f x) y) =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x)
        (__eo_get_nil_rec f y)) := by
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst f
    simp [__eo_list_rev, __eo_is_list, __eo_requires, native_teq,
      native_ite, SmtEval.native_ite] at hRev
  have hTail := eo_list_rev_cons_tail_list_of_ne_stuck f x y hRev
  exact eo_list_rev_cons_eq_of_tail_list f x y hF hTail

theorem eo_list_rev_str_concat_cons_eq_of_ne_stuck (x y : Term)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat x y) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat x y) =
      __eo_list_rev_rec y
        (mkConcat x (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y)) := by
  exact eo_list_rev_cons_eq_of_ne_stuck (Term.UOp UserOp.str_concat) x y hRev

theorem eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck
    (head nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
      mkConcat head nil := by
  rw [eo_list_rev_str_concat_cons_eq_of_ne_stuck head nil hRev]
  rw [eo_get_nil_rec_str_concat_eq_of_nil_true nil hNil]
  cases nil <;>
    simp [__eo_list_rev_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq] at hNil ⊢

theorem eo_list_rev_str_concat_cons_cons_nil_eq_of_ne_stuck
    (head mid nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat head (mkConcat mid nil)) ≠ Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (mkConcat head (mkConcat mid nil)) =
      mkConcat mid (mkConcat head nil) := by
  rw [eo_list_rev_str_concat_cons_eq_of_ne_stuck head (mkConcat mid nil) hRev]
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil hNil
  rw [eo_get_nil_rec_cons_self_eq_of_tail_list
    (Term.UOp UserOp.str_concat) mid nil (by decide) hNilList]
  rw [eo_get_nil_rec_str_concat_eq_of_nil_true nil hNil]
  have hAcc : mkConcat head nil ≠ Term.Stuck := by
    intro h
    cases h
  rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) mid nil
    (mkConcat head nil) hAcc]
  rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil
    (mkConcat mid (mkConcat head nil)) hNil]

theorem eo_list_rev_rec_cons_ne_stuck_of_ne_stuck (f x y acc : Term) :
    __eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc ≠ Term.Stuck ->
    __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) ≠ Term.Stuck := by
  intro h
  have hAcc : acc ≠ Term.Stuck := by
    intro hAcc
    subst acc
    simp [__eo_list_rev_rec] at h
  simpa [eo_list_rev_rec_cons f x y acc hAcc] using h

theorem eo_list_rev_rec_acc_ne_stuck_of_ne_stuck (a acc : Term) :
    __eo_list_rev_rec a acc ≠ Term.Stuck ->
    acc ≠ Term.Stuck := by
  intro h hAcc
  subst acc
  cases a <;> simp [__eo_list_rev_rec] at h

theorem eo_list_rev_rec_is_list_true_of_lists (f a acc : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f acc = Term.Boolean true ->
    __eo_list_rev_rec a acc ≠ Term.Stuck ->
    __eo_is_list f (__eo_list_rev_rec a acc) = Term.Boolean true := by
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      intro hListA hListAcc hRev
      simp [__eo_list_rev_rec] at hRev
  | case2 a hA =>
      intro hListA hListAcc hRev
      simp [__eo_list_rev_rec] at hRev
  | case3 g x y acc hAcc ih =>
      intro hListA hListAcc hRev
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hListA
      subst g
      have hF : f ≠ Term.Stuck := by
        intro hF
        subst f
        simp [__eo_is_list] at hListA
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hListA
      have hNewAccList :
          __eo_is_list f (Term.Apply (Term.Apply f x) acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list f x acc hF hListAcc
      have hTailRev :
          __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) ≠
            Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      simpa [__eo_list_rev_rec] using
        ih hTailList hNewAccList hTailRev
  | case4 nil acc hNil hAcc hNot =>
      intro hListA hListAcc hRev
      simpa [__eo_list_rev_rec] using hListAcc

theorem eo_get_nil_rec_is_list_true_of_is_list_true (f a : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f (__eo_get_nil_rec f a) = Term.Boolean true := by
  induction f, a using __eo_get_nil_rec.induct with
  | case1 a =>
      intro hList
      simp [__eo_is_list] at hList
  | case2 f hF =>
      intro hList
      simp [__eo_is_list] at hList
  | case3 f g x y hF ih =>
      intro hList
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTailList]
      exact ih hTailList
  | case4 f nil hF hNil hNot =>
      intro hList
      have hGet : __eo_get_nil_rec f nil ≠ Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true f nil hList
      have hReq :
          __eo_requires (__eo_is_list_nil f nil) (Term.Boolean true) nil ≠
            Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hGetEq :
          __eo_get_nil_rec f nil = nil := by
        simpa [__eo_get_nil_rec] using
          eo_requires_eq_result_of_ne_stuck
            (__eo_is_list_nil f nil) (Term.Boolean true) nil hReq
      rw [hGetEq]
      exact hList

theorem eo_is_list_nil_get_nil_rec_of_is_list_true (f a : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list_nil f (__eo_get_nil_rec f a) = Term.Boolean true := by
  induction f, a using __eo_get_nil_rec.induct with
  | case1 a =>
      intro hList
      simp [__eo_is_list] at hList
  | case2 f hF =>
      intro hList
      simp [__eo_is_list] at hList
  | case3 f g x y hF ih =>
      intro hList
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTailList]
      exact ih hTailList
  | case4 f nil hF hNil hNot =>
      intro hList
      have hGet : __eo_get_nil_rec f nil ≠ Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true f nil hList
      have hReq :
          __eo_requires (__eo_is_list_nil f nil) (Term.Boolean true) nil ≠
            Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hNilTrue :
          __eo_is_list_nil f nil = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck (__eo_is_list_nil f nil)
          (Term.Boolean true) nil hReq
      have hGetEq :
          __eo_get_nil_rec f nil = nil := by
        simpa [__eo_get_nil_rec] using
          eo_requires_eq_result_of_ne_stuck
            (__eo_is_list_nil f nil) (Term.Boolean true) nil hReq
      rw [hGetEq]
      exact hNilTrue

theorem eo_list_rev_result_is_list_true_of_ne_stuck (f a : Term)
    (hRev : __eo_list_rev f a ≠ Term.Stuck) :
    __eo_is_list f (__eo_list_rev f a) = Term.Boolean true := by
  have hList : __eo_is_list f a = Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck f a hRev
  have hGetList :
      __eo_is_list f (__eo_get_nil_rec f a) = Term.Boolean true :=
    eo_get_nil_rec_is_list_true_of_is_list_true f a hList
  have hRec :
      __eo_list_rev_rec a (__eo_get_nil_rec f a) ≠ Term.Stuck :=
    eo_list_rev_rec_ne_stuck_of_ne_stuck f a hRev
  rw [eo_list_rev_eq_rec_of_ne_stuck f a hRev]
  exact eo_list_rev_rec_is_list_true_of_lists f a (__eo_get_nil_rec f a)
    hList hGetList hRec

theorem eo_list_rev_rec_ne_stuck_of_list (f a acc : Term) :
    __eo_is_list f a = Term.Boolean true ->
    acc ≠ Term.Stuck ->
    __eo_list_rev_rec a acc ≠ Term.Stuck := by
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      intro hList hAcc
      cases f <;> simp [__eo_is_list] at hList
  | case2 a hA =>
      intro hList hAcc
      exact False.elim (hAcc rfl)
  | case3 g x y acc hAcc ih =>
      intro hList hAccNonStuck
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      have hNewAcc :
          Term.Apply (Term.Apply f x) acc ≠ Term.Stuck := by
        intro h
        cases h
      simpa [__eo_list_rev_rec] using ih hTailList hNewAcc
  | case4 nil acc hNil hAcc hNot =>
      intro hList hAccNonStuck
      simpa [__eo_list_rev_rec] using hAccNonStuck

theorem eo_list_rev_ne_stuck_of_is_list_true (f a : Term)
    (hList : __eo_is_list f a = Term.Boolean true) :
    __eo_list_rev f a ≠ Term.Stuck := by
  have hGet : __eo_get_nil_rec f a ≠ Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f a hList
  have hRec :
      __eo_list_rev_rec a (__eo_get_nil_rec f a) ≠ Term.Stuck :=
    eo_list_rev_rec_ne_stuck_of_list f a (__eo_get_nil_rec f a) hList hGet
  rw [__eo_list_rev, hList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_list_rev_rec a (__eo_get_nil_rec f a)) (by decide)]
  exact hRec

theorem eo_list_concat_rec_str_concat_nil_eq_of_nil_true
    (nil z : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_list_concat_rec nil z = z := by
  cases nil <;>
    simp [__eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_eq, native_teq] at hNil ⊢
  case UOp1 op A =>
    cases op <;>
      simp at hNil
    case seq_empty =>
      cases z <;> rfl
  case String s =>
    subst s
    cases z <;> rfl

theorem eo_list_concat_rec_cons_eq_of_tail_ne_stuck
    (f head tail z : Term)
    (hTail : __eo_list_concat_rec tail z ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f head) tail) z =
      Term.Apply (Term.Apply f head) (__eo_list_concat_rec tail z) := by
  have hLeft :
      __eo_list_concat_rec (Term.Apply (Term.Apply f head) tail) z =
        __eo_mk_apply (Term.Apply f head) (__eo_list_concat_rec tail z) := by
    cases z <;> try rfl
    case Stuck =>
      cases tail <;> simp [__eo_list_concat_rec] at hTail
  rw [hLeft]
  cases hRec : __eo_list_concat_rec tail z <;>
    simp [__eo_mk_apply, hRec] at hTail ⊢

theorem eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
    (head tail z : Term)
    (hTail : __eo_list_concat_rec tail z ≠ Term.Stuck) :
    __eo_list_concat_rec (mkConcat head tail) z =
      mkConcat head (__eo_list_concat_rec tail z) := by
  exact eo_list_concat_rec_cons_eq_of_tail_ne_stuck
    (Term.UOp UserOp.str_concat) head tail z hTail

theorem eo_list_concat_rec_ne_stuck_of_list (f a z : Term) :
    __eo_is_list f a = Term.Boolean true ->
    z ≠ Term.Stuck ->
    __eo_list_concat_rec a z ≠ Term.Stuck := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro hList hZ
      cases f <;> simp [__eo_is_list] at hList
  | case2 a hA =>
      intro hList hZ
      exact False.elim (hZ rfl)
  | case3 g x y z hZ ih =>
      intro hList hZNonStuck
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        ih hTailList hZNonStuck
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck f x y z hTailConcat]
      intro h
      cases h
  | case4 nil z hNil hZ hNot =>
      intro hList hZNonStuck
      simpa [__eo_list_concat_rec] using hZNonStuck

theorem eo_list_concat_rec_is_list_true_of_lists (f a z : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f z = Term.Boolean true ->
    __eo_is_list f (__eo_list_concat_rec a z) = Term.Boolean true := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro hListA hListZ
      cases f <;> simp [__eo_is_list] at hListA
  | case2 a hA =>
      intro hListA hListZ
      cases f <;> simp [__eo_is_list] at hListZ
  | case3 g x y z hZ ih =>
      intro hListA hListZ
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hListA
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hListA
      have hZNonStuck : z ≠ Term.Stuck := by
        intro hz
        subst z
        cases f <;> simp [__eo_is_list] at hListZ
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list f y z hTailList hZNonStuck
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck f x y z hTailConcat]
      exact eo_is_list_cons_self_true_of_tail_list f x
        (__eo_list_concat_rec y z)
        (by
          intro hF
          subst f
          simp [__eo_is_list] at hListA)
        (ih hTailList hListZ)
  | case4 nil z hNil hZ hNot =>
      intro hListA hListZ
      simpa [__eo_list_concat_rec] using hListZ

theorem smt_typeof_list_concat_rec_str_concat_of_seq_aux
    (f a z : Term) :
    f = Term.UOp UserOp.str_concat ->
    ∀ T : SmtType,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt z) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
        SmtType.Seq T := by
  intro hf
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro T hList haTy hzTy
      subst f
      simp [__eo_is_list] at hList
  | case2 a hA =>
      intro T hList haTy hzTy
      change __smtx_typeof SmtTerm.None = SmtType.Seq T at hzTy
      rw [TranslationProofs.smtx_typeof_none] at hzTy
      cases hzTy
  | case3 g x y z hZ ih =>
      intro T hList haTy hzTy
      subst f
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hList
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [haTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with
        ⟨U, hxTy, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTy hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, haTy]
        injection hSeq
      have hxTyT : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        simpa [hUT] using hxTy
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hZNonStuck : z ≠ Term.Stuck := by
        intro hz
        subst z
        change __smtx_typeof SmtTerm.None = SmtType.Seq T at hzTy
        rw [TranslationProofs.smtx_typeof_none] at hzTy
        cases hzTy
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.str_concat)
          y z hTailList hZNonStuck
      have hTailTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y z)) =
            SmtType.Seq T :=
        ih T hTailList hyTy hzTy
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck x y z
        hTailConcat]
      exact smt_typeof_str_concat_of_seq x (__eo_list_concat_rec y z) T
        hxTyT hTailTy
  | case4 nil z hNil hZ hNot =>
      intro T hList haTy hzTy
      simpa [__eo_list_concat_rec] using hzTy

theorem smt_typeof_list_concat_rec_str_concat_of_seq
    (a z : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.Seq T :=
  smt_typeof_list_concat_rec_str_concat_of_seq_aux
    (Term.UOp UserOp.str_concat) a z rfl T hList haTy hzTy

theorem eo_list_rev_rec_list_concat_rec_singleton_eq
    (tail acc head nil : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc = Term.Boolean true) :
    __eo_list_rev_rec tail
        (__eo_list_concat_rec acc (mkConcat head nil)) =
      __eo_list_concat_rec (__eo_list_rev_rec tail acc)
        (mkConcat head nil) := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hTailList
      have hAccNonStuck : acc ≠ Term.Stuck := by
        intro h
        subst acc
        simp [__eo_is_list] at hAccList
      have hSingletonNonStuck : mkConcat head nil ≠ Term.Stuck := by
        intro h
        cases h
      have hAccSnocNonStuck :
          __eo_list_concat_rec acc (mkConcat head nil) ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) acc (mkConcat head nil)
          hAccList hSingletonNonStuck
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.str_concat) x acc (by decide) hAccList
      have hConsAccSnoc :
          mkConcat x (__eo_list_concat_rec acc (mkConcat head nil)) =
            __eo_list_concat_rec (mkConcat x acc) (mkConcat head nil) := by
        exact (eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          x acc (mkConcat head nil) hAccSnocNonStuck).symm
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) x y
        (__eo_list_concat_rec acc (mkConcat head nil)) hAccSnocNonStuck]
      change __eo_list_rev_rec y
          (mkConcat x (__eo_list_concat_rec acc (mkConcat head nil))) =
        __eo_list_concat_rec
          (__eo_list_rev_rec (mkConcat x y) acc) (mkConcat head nil)
      rw [hConsAccSnoc]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) x y acc
        hAccNonStuck]
      exact ih hTailTailList hConsAccList
  | case4 tail acc hTail hAcc hNot =>
      have hGet : __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail ≠
          Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) tail hTailList
      have hReq :
          __eo_requires
              (__eo_is_list_nil (Term.UOp UserOp.str_concat) tail)
              (Term.Boolean true) tail ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hTailNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck
          (__eo_is_list_nil (Term.UOp UserOp.str_concat) tail)
          (Term.Boolean true) tail hReq
      rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true tail
        (__eo_list_concat_rec acc (mkConcat head nil)) hTailNil]
      rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true tail acc hTailNil]

theorem eo_get_nil_rec_list_rev_rec_eq
    (tail acc : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.str_concat)
        (__eo_list_rev_rec tail acc) =
      __eo_get_nil_rec (Term.UOp UserOp.str_concat) acc := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hTailList
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.str_concat) x acc (by decide) hAccList
      simpa [__eo_list_rev_rec, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not] using
        ih hTailTailList hConsAccList
  | case4 nil acc hNil hAcc hNot =>
      simp [__eo_list_rev_rec]

theorem eo_list_rev_rec_rev_rec_get_nil_eq
    (tail acc : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc = Term.Boolean true) :
    __eo_list_rev_rec (__eo_list_rev_rec tail acc)
        (__eo_get_nil_rec (Term.UOp UserOp.str_concat) tail) =
      __eo_list_rev_rec acc tail := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hTailList
      have hAccNonStuck : acc ≠ Term.Stuck := by
        intro h
        subst acc
        simp [__eo_is_list] at hAccList
      have hTailNonStuck : y ≠ Term.Stuck := by
        intro h
        subst y
        simp [__eo_is_list] at hTailTailList
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.str_concat) x acc (by decide) hAccList
      have hGetEq :
          __eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (mkConcat x y) =
            __eo_get_nil_rec (Term.UOp UserOp.str_concat) y :=
        eo_get_nil_rec_cons_self_eq_of_tail_list
          (Term.UOp UserOp.str_concat) x y (by decide) hTailTailList
      rw [hGetEq]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) x y acc
        hAccNonStuck]
      rw [ih hTailTailList hConsAccList]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) x acc y
        hTailNonStuck]
  | case4 nil acc hNil hAcc hNot =>
      have hGet : __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil ≠
          Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) nil hTailList
      have hReq :
          __eo_requires
              (__eo_is_list_nil (Term.UOp UserOp.str_concat) nil)
              (Term.Boolean true) nil ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hNilTrue :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck
          (__eo_is_list_nil (Term.UOp UserOp.str_concat) nil)
          (Term.Boolean true) nil hReq
      have hGetEq :
          __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil = nil :=
        eo_get_nil_rec_str_concat_eq_of_nil_true nil hNilTrue
      rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil acc hNilTrue]
      rw [hGetEq]

theorem eo_list_rev_list_rev_str_concat_eq_of_list_true
    (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) a) = a := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.str_concat) a
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true := by
    simpa [nil] using
      eo_get_nil_rec_is_list_true_of_is_list_true
        (Term.UOp UserOp.str_concat) a hList
  have hNilNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true := by
    simpa [nil] using
      eo_is_list_nil_get_nil_rec_of_is_list_true
        (Term.UOp UserOp.str_concat) a hList
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) a =
        __eo_list_rev_rec a nil := by
    simpa [nil] using
      eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.str_concat) a hRev
  have hRevRecNonStuck :
      __eo_list_rev_rec a nil ≠ Term.Stuck := by
    simpa [hRevEq] using hRev
  have hRevRecList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_rev_rec a nil) = Term.Boolean true :=
    eo_list_rev_rec_is_list_true_of_lists (Term.UOp UserOp.str_concat)
      a nil hList hNilList hRevRecNonStuck
  have hRevRev :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) ≠ Term.Stuck := by
    rw [hRevEq]
    exact eo_list_rev_ne_stuck_of_is_list_true
      (Term.UOp UserOp.str_concat) (__eo_list_rev_rec a nil) hRevRecList
  have hGetRev :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) = nil := by
    rw [hRevEq]
    calc
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (__eo_list_rev_rec a nil) =
        __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil := by
          exact eo_get_nil_rec_list_rev_rec_eq a nil hList hNilList
      _ = nil :=
        eo_get_nil_rec_str_concat_eq_of_nil_true nil hNilNil
  have hRevRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) =
        __eo_list_rev_rec (__eo_list_rev (Term.UOp UserOp.str_concat) a)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a)) :=
    eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) a) hRevRev
  rw [hRevRevEq, hGetRev, hRevEq]
  rw [eo_list_rev_rec_rev_rec_get_nil_eq a nil hList hNilList]
  rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil a hNilNil]

theorem smt_typeof_get_nil_rec_str_concat_of_seq_aux (f a : Term) :
    f = Term.UOp UserOp.str_concat ->
    ∀ T : SmtType,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __eo_get_nil_rec f a ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_get_nil_rec f a)) = SmtType.Seq T := by
  intro hf
  induction f, a using __eo_get_nil_rec.induct with
  | case1 a =>
      intro T hList haTy hGet
      cases hf
  | case2 f hF =>
      intro T hList haTy hGet
      simp [__eo_get_nil_rec] at hGet
  | case3 f g x y hF ih =>
      intro T hList haTy hGet
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      have hReq :
          __eo_requires f f (__eo_get_nil_rec f y) ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hTailGet : __eo_get_nil_rec f y ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck f f (__eo_get_nil_rec f y) hReq
      subst f
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [haTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with ⟨U, hxTy, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTy hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, haTy]
        injection hSeq
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hIH := ih rfl T hTailList hyTy hTailGet
      simpa [__eo_get_nil_rec,
        eo_requires_eq_result_of_ne_stuck (Term.UOp UserOp.str_concat)
          (Term.UOp UserOp.str_concat)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y) hReq] using hIH
  | case4 f nil hF hNil hNot =>
      intro T hList haTy hGet
      have hReq :
          __eo_requires (__eo_is_list_nil f nil) (Term.Boolean true) nil ≠
            Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      simpa [__eo_get_nil_rec,
        eo_requires_eq_result_of_ne_stuck
          (__eo_is_list_nil f nil) (Term.Boolean true) nil hReq] using haTy

theorem smt_typeof_get_nil_rec_str_concat_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hGet :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a)) =
      SmtType.Seq T :=
  smt_typeof_get_nil_rec_str_concat_of_seq_aux
    (Term.UOp UserOp.str_concat) a rfl T hList haTy hGet

theorem smt_typeof_list_rev_eq_rec_of_ne_stuck (f a : Term)
    (hRev : __eo_list_rev f a ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_list_rev f a)) =
      __smtx_typeof
        (__eo_to_smt (__eo_list_rev_rec a (__eo_get_nil_rec f a))) := by
  rw [eo_list_rev_eq_rec_of_ne_stuck f a hRev]

theorem smt_typeof_list_rev_rec_cons_eq
    (f x y acc : Term) (hAcc : acc ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc)) =
      __smtx_typeof
        (__eo_to_smt (__eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc))) := by
  rw [eo_list_rev_rec_cons f x y acc hAcc]

theorem smt_typeof_list_rev_rec_str_concat_of_seq_aux
    (f a acc : Term) :
    f = Term.UOp UserOp.str_concat ->
    ∀ T : SmtType,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T ->
      __eo_list_rev_rec a acc ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_list_rev_rec a acc)) =
        SmtType.Seq T := by
  intro hf
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      intro T hList haTy hAccTy hRev
      simp [__eo_list_rev_rec] at hRev
  | case2 a hA =>
      intro T hList haTy hAccTy hRev
      simp [__eo_list_rev_rec] at hRev
  | case3 g x y acc hAcc ih =>
      intro T hList haTy hAccTy hRev
      subst f
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hList
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [haTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with
        ⟨U, hxTy, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTy hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, haTy]
        injection hSeq
      have hxTyT : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        simpa [hUT] using hxTy
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hNewAccTy :
          __smtx_typeof (__eo_to_smt (mkConcat x acc)) = SmtType.Seq T :=
        smt_typeof_str_concat_of_seq x acc T hxTyT hAccTy
      have hTailRev :
          __eo_list_rev_rec y (mkConcat x acc) ≠ Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      have hIH := ih T hTailList hyTy hNewAccTy hTailRev
      simpa [__eo_list_rev_rec] using hIH
  | case4 nil acc hNil hAcc hNot =>
      intro T hList haTy hAccTy hRev
      simpa [__eo_list_rev_rec] using hAccTy

theorem smt_typeof_list_rev_rec_str_concat_of_seq
    (a acc : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T)
    (hRev : __eo_list_rev_rec a acc ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_list_rev_rec a acc)) = SmtType.Seq T :=
  smt_typeof_list_rev_rec_str_concat_of_seq_aux
    (Term.UOp UserOp.str_concat) a acc rfl T hList haTy hAccTy hRev

theorem smt_typeof_list_rev_str_concat_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.str_concat) a)) =
      SmtType.Seq T := by
  have hGet : __eo_get_nil_rec (Term.UOp UserOp.str_concat) a ≠
      Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat) a
      hList
  have hGetTy :
      __smtx_typeof
          (__eo_to_smt (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a)) =
        SmtType.Seq T :=
    smt_typeof_get_nil_rec_str_concat_of_seq a T hList haTy hGet
  have hRec :
      __eo_list_rev_rec a (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a) ≠
        Term.Stuck :=
    eo_list_rev_rec_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat) a hRev
  rw [smt_typeof_list_rev_eq_rec_of_ne_stuck
    (Term.UOp UserOp.str_concat) a hRev]
  exact smt_typeof_list_rev_rec_str_concat_of_seq a
    (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a) T hList haTy hGetTy hRec

theorem eo_list_rev_list_rev_ne_stuck_of_ne_stuck (f a : Term)
    (hRev : __eo_list_rev f a ≠ Term.Stuck) :
    __eo_list_rev f (__eo_list_rev f a) ≠ Term.Stuck := by
  exact eo_list_rev_ne_stuck_of_is_list_true f (__eo_list_rev f a)
    (eo_list_rev_result_is_list_true_of_ne_stuck f a hRev)

theorem smt_typeof_list_rev_list_rev_str_concat_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a))) =
      SmtType.Seq T := by
  have hRevTy :
      __smtx_typeof
          (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.str_concat) a)) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq a T hList haTy hRev
  have hRevList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) =
        Term.Boolean true :=
    eo_list_rev_result_is_list_true_of_ne_stuck
      (Term.UOp UserOp.str_concat) a hRev
  have hRevRev :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) ≠
        Term.Stuck :=
    eo_list_rev_list_rev_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.str_concat) a hRev
  exact smt_typeof_list_rev_str_concat_of_seq
    (__eo_list_rev (Term.UOp UserOp.str_concat) a) T hRevList hRevTy
    hRevRev

theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

theorem eo_mk_apply_fun_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  intro hf
  subst f
  simp [__eo_mk_apply] at h

theorem eo_mk_apply_arg_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

theorem eo_ite_then_ne_stuck_of_ne_stuck (c x y : Term)
    (h : __eo_ite c x y ≠ Term.Stuck)
    (hc : c = Term.Boolean true) :
    x ≠ Term.Stuck := by
  subst c
  simpa [eo_ite_true] using h

theorem eo_ite_else_ne_stuck_of_ne_stuck (c x y : Term)
    (h : __eo_ite c x y ≠ Term.Stuck)
    (hc : c = Term.Boolean false) :
    y ≠ Term.Stuck := by
  subst c
  simpa [eo_ite_false] using h

theorem str_nary_intro_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_nary_intro x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  exact h (by rfl)

theorem str_nary_elim_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_nary_elim x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  exact h (by rfl)

theorem str_nary_elim_is_list_true_of_ne_stuck (x : Term)
    (h : __str_nary_elim x ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true := by
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) x)
          (Term.Boolean true) (__eo_list_singleton_elim_2 x) ≠
        Term.Stuck := by
    simpa [__str_nary_elim, __eo_list_singleton_elim] using h
  exact eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) x) (Term.Boolean true)
    (__eo_list_singleton_elim_2 x) hReq

theorem term_ne_stuck_of_smt_type_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hxTy
  rw [TranslationProofs.smtx_typeof_none] at hxTy
  cases hxTy

theorem str_nary_intro_eq_self_of_is_list (x : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true) :
    __str_nary_intro x = x := by
  simp [__str_nary_intro, __eo_list_singleton_intro, hList, eo_ite_true]

theorem str_nary_intro_concat_eq (x y : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true) :
    __str_nary_intro (mkConcat x y) = mkConcat x y := by
  have hList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x y) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      x y (by decide) hTailList
  exact str_nary_intro_eq_self_of_is_list (mkConcat x y) hList

theorem str_nary_intro_concat_has_smt_translation
    (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro (mkConcat x y))) ≠
      SmtType.None := by
  rcases smt_typeof_str_concat_seq_of_non_none x y hNN with
    ⟨T, hConcatTy⟩
  have hConcatNe : mkConcat x y ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq (mkConcat x y) T hConcatTy
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat)
      (mkConcat x y) (by decide) hConcatNe with
    ⟨isList, hListBool⟩
  cases isList
  · have hTrans :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        (mkConcat x y) hNN
    have hTy :
        __eo_to_smt_type (__eo_typeof (mkConcat x y)) =
          SmtType.Seq T := by
      rw [← hTrans, hConcatTy]
    let nil := __eo_nil (Term.UOp UserOp.str_concat)
      (__eo_typeof (mkConcat x y))
    have hNilEq : nil = __seq_empty (__eo_typeof (mkConcat x y)) := by
      simpa [nil] using strConcat_nil_eq_seq_empty_of_type hTy
    have hNilNN :
        __smtx_typeof (__eo_to_smt nil) ≠ SmtType.None := by
      rw [hNilEq]
      rcases smt_seq_component_wf_of_non_none_type
          (__eo_to_smt (mkConcat x y)) T hConcatTy with
        ⟨hInh, hWf⟩
      exact seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
        (mkConcat x y) T hConcatTy hInh hWf
    have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
      have hNilNN' :
          __smtx_typeof
              (__eo_to_smt (__seq_empty (__eo_typeof (mkConcat x y)))) ≠
            SmtType.None := by
        simpa [← hNilEq] using hNilNN
      rw [hNilEq]
      exact smt_typeof_seq_empty_typeof (mkConcat x y) T hConcatTy hNilNN'
    have hNilNe : nil ≠ Term.Stuck :=
      term_ne_stuck_of_smt_type_seq nil T hNilTy
    have hNilList :
        __eo_is_list (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true :=
      eo_is_list_str_concat_nil_true_of_nil_true nil
        (by simpa [nil] using strConcat_nil_is_list_nil_of_type hTy)
    have hMkNe :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_concat) (mkConcat x y)) nil ≠
          Term.Stuck := by
      cases hNilCases : nil <;> simp [__eo_mk_apply, hNilCases] at hNilNe ⊢
    have hMkEq :
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_concat) (mkConcat x y)) nil =
          mkConcat (mkConcat x y) nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) (mkConcat x y)) nil hMkNe
    have hWrappedTy :
        __smtx_typeof (__eo_to_smt (mkConcat (mkConcat x y) nil)) =
          SmtType.Seq T :=
      smt_typeof_str_concat_of_seq (mkConcat x y) nil T hConcatTy hNilTy
    have hIntroEq :
        __str_nary_intro (mkConcat x y) =
          mkConcat (mkConcat x y) nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, hListBool,
        eo_ite_false, nil, hNilList, hMkEq, __eo_requires, native_teq,
        native_ite, SmtEval.native_ite, SmtEval.native_not]
    rw [hIntroEq, hWrappedTy]
    exact seq_ne_none T
  · have hIntroEq :
        __str_nary_intro (mkConcat x y) = mkConcat x y := by
      exact str_nary_intro_eq_self_of_is_list (mkConcat x y)
        (by simpa using hListBool)
    simpa [hIntroEq] using hNN

theorem seq_empty_ne_stuck_of_ne_stuck (A : Term)
    (hA : A ≠ Term.Stuck) :
    __seq_empty A ≠ Term.Stuck := by
  cases A with
  | Stuck =>
      exact False.elim (hA rfl)
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__seq_empty]
          case Seq =>
            cases x with
            | UOp op' =>
                cases op' <;> simp
            | _ =>
                simp
      | _ =>
          simp [__seq_empty]
  | _ =>
      simp [__seq_empty]

theorem seq_empty_typeof_ne_stuck_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __seq_empty (__eo_typeof x) ≠ Term.Stuck := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  have hTypeNonStuck : __eo_typeof x ≠ Term.Stuck := by
    intro hType
    rw [hType] at hA
    simp [__eo_to_smt_type] at hA
  exact seq_empty_ne_stuck_of_ne_stuck (__eo_typeof x) hTypeNonStuck

theorem eo_eq_seq_empty_typeof_ne_stuck_of_smt_type_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    ∃ b, __eo_eq y (__seq_empty (__eo_typeof x)) = Term.Boolean b := by
  have hyNonStuck : y ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq y T hyTy
  have hEmptyNonStuck :
      __seq_empty (__eo_typeof x) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
  cases y <;> simp [__eo_eq] at hyNonStuck ⊢
  all_goals
    cases hEmpty : __seq_empty (__eo_typeof x) <;>
      simp [__eo_eq, hEmpty] at hEmptyNonStuck ⊢

theorem eo_is_list_nil_str_concat_seq_empty_of_ne_stuck'
    (A : Term) (hEmpty : __seq_empty A ≠ Term.Stuck) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__seq_empty A) = Term.Boolean true := by
  cases A <;>
    simp [__seq_empty, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq] at hEmpty ⊢
  case Apply f a =>
    cases f with
    | UOp op =>
        cases op <;> try rfl
        case Seq =>
          cases a <;> try rfl
          case UOp op =>
            cases op <;> try rfl
    | _ =>
        rfl

theorem eo_is_list_str_concat_seq_empty_of_ne_stuck
    (A : Term) (hEmpty : __seq_empty A ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) (__seq_empty A) =
      Term.Boolean true :=
  eo_is_list_str_concat_nil_true_of_nil_true (__seq_empty A)
    (eo_is_list_nil_str_concat_seq_empty_of_ne_stuck' A hEmpty)

theorem str_nary_elim_str_concat_cons_ne_stuck_of_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true) :
    __str_nary_elim (mkConcat x y) ≠ Term.Stuck := by
  have hxNe : x ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq x T hxTy
  have hyNe : y ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq y T hyTy
  have hList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x y) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      x y (by decide) hTailList
  rcases eo_is_list_nil_str_concat_boolean_of_ne_stuck y hyNe with
    ⟨isNil, hNilBool⟩
  cases isNil
  · simp [__str_nary_elim, __eo_list_singleton_elim, hList,
      __eo_list_singleton_elim_2, hNilBool, eo_ite_false, __eo_requires,
      native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not]
  · simpa [__str_nary_elim, __eo_list_singleton_elim, hList,
      __eo_list_singleton_elim_2, hNilBool, eo_ite_true, __eo_requires,
      native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not] using hxNe

theorem str_nary_elim_str_nary_intro_default_ne_stuck_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElimDefault :
      __str_nary_elim x =
        __eo_requires x (__seq_empty (__eo_typeof x)) x)
    (hIntroNN :
      __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
                (__seq_empty (__eo_typeof x))))) ≠ SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __str_nary_elim
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x)))) ≠ Term.Stuck := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · have hxNonStuck : x ≠ Term.Stuck :=
      term_ne_stuck_of_smt_type_seq x T hxTy
    have hEmptyEq : __seq_empty (__eo_typeof x) = x :=
      eq_of_eo_eq_true_local x (__seq_empty (__eo_typeof x)) hCond
    rw [hCond, eo_ite_true]
    rw [hElimDefault, hEmptyEq]
    rw [eo_requires_self_eq_of_ne_stuck x x hxNonStuck]
    exact hxNonStuck
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    have hConcatNN :
        __smtx_typeof
            (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
          SmtType.None := by
      simpa [hCond, eo_ite_false, hApplyEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x))
        hConcatNN with ⟨U, hxTyU, hEmptyTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T := by
      simpa [hUT] using hEmptyTyU
    have hEmptyList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__seq_empty (__eo_typeof x)) =
          Term.Boolean true :=
      eo_is_list_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
        (term_ne_stuck_of_smt_type_seq
          (__seq_empty (__eo_typeof x)) T hEmptyTy)
    rw [hCond, eo_ite_false, hApplyEq]
    exact str_nary_elim_str_concat_cons_ne_stuck_of_seq x
      (__seq_empty (__eo_typeof x)) T hxTy hEmptyTy hEmptyList

theorem str_nary_elim_list_rev_rec_ne_stuck_of_seq
    (tail acc : Term) (T : SmtType)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T)
    (hAccElim : __str_nary_elim acc ≠ Term.Stuck)
    (hRev : __eo_list_rev_rec tail acc ≠ Term.Stuck) :
    __str_nary_elim (__eo_list_rev_rec tail acc) ≠ Term.Stuck := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      change __smtx_typeof SmtTerm.None = SmtType.Seq T at hAccTy
      rw [TranslationProofs.smtx_typeof_none] at hAccTy
      cases hAccTy
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          x y hTailList
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [hTailTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with
        ⟨U, hxTyU, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTyU hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, hTailTy]
        injection hSeq
      have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        simpa [hUT] using hxTyU
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hNewAccTy :
          __smtx_typeof (__eo_to_smt (mkConcat x acc)) = SmtType.Seq T :=
        smt_typeof_str_concat_of_seq x acc T hxTy hAccTy
      have hNewAccElim :
          __str_nary_elim (mkConcat x acc) ≠ Term.Stuck :=
        str_nary_elim_str_concat_cons_ne_stuck_of_seq x acc T hxTy
          hAccTy (str_nary_elim_is_list_true_of_ne_stuck acc hAccElim)
      have hTailRev :
          __eo_list_rev_rec y (mkConcat x acc) ≠ Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      simpa [__eo_list_rev_rec] using
        ih hTailTailList hyTy hNewAccTy hNewAccElim hTailRev
  | case4 nil acc hNil hAcc hNot =>
      simpa [__eo_list_rev_rec] using hAccElim

theorem str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq
    (head tail : Term) (T : SmtType)
    (hConsTy : __smtx_typeof (__eo_to_smt (mkConcat head tail)) =
      SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck) :
    __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat head tail)) ≠ Term.Stuck := by
  rcases str_concat_args_of_seq_type head tail T hConsTy with
    ⟨hHeadTy, hTailTy⟩
  have hConsList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (mkConcat head tail) hRevCons
  have hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) head
      tail hConsList
  let nil := __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_get_nil_rec_str_concat_of_seq tail T hTailList hTailTy
        (eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) tail hTailList)
  have hAccTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hAccElim : __str_nary_elim (mkConcat head nil) ≠ Term.Stuck :=
    str_nary_elim_str_concat_cons_ne_stuck_of_seq head nil T hHeadTy
      hNilTy
      (by
        simpa [nil] using
          eo_get_nil_rec_is_list_true_of_is_list_true
            (Term.UOp UserOp.str_concat) tail hTailList)
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        __eo_list_rev_rec tail (mkConcat head nil) := by
    simpa [nil] using
      eo_list_rev_str_concat_cons_eq_of_ne_stuck head tail hRevCons
  have hRevRec :
      __eo_list_rev_rec tail (mkConcat head nil) ≠ Term.Stuck := by
    simpa [hRevEq] using hRevCons
  simpa [hRevEq, nil] using
    str_nary_elim_list_rev_rec_ne_stuck_of_seq tail (mkConcat head nil)
      T hTailList hTailTy hAccTy hAccElim hRevRec

theorem str_nary_elim_2_eq_self_of_not_str_concat
    (x : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __eo_list_singleton_elim_2 x = x := by
  cases x with
  | Apply f a =>
      cases f with
      | Apply g b =>
          have hg : g = Term.UOp UserOp.str_concat :=
            eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat)
              g b a hList
          subst g
          exact False.elim (hNotConcat ⟨b, a, rfl⟩)
      | _ => rfl
  | _ => rfl

theorem str_nary_elim_ne_stuck_of_list_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true) :
    __str_nary_elim x ≠ Term.Stuck := by
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, hEq⟩
    subst x
    rcases str_concat_args_of_seq_type head tail T hxTy with
      ⟨hHeadTy, hTailTy⟩
    have hTailList :
        __eo_is_list (Term.UOp UserOp.str_concat) tail =
          Term.Boolean true :=
      eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
        head tail hList
    exact str_nary_elim_str_concat_cons_ne_stuck_of_seq head tail T
      hHeadTy hTailTy hTailList
  · have hElim2 : __eo_list_singleton_elim_2 x = x :=
      str_nary_elim_2_eq_self_of_not_str_concat x hList hConcat
    have hxNe : x ≠ Term.Stuck := term_ne_stuck_of_smt_type_seq x T hxTy
    rw [__str_nary_elim, __eo_list_singleton_elim, hList]
    rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
      (__eo_list_singleton_elim_2 x) (by decide)]
    rw [hElim2]
    exact hxNe

theorem str_nary_elim_str_nary_intro_ne_stuck_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil
      (by simpa [nil] using strConcat_nil_is_list_nil_of_type hTy)
  have hxNe : x ≠ Term.Stuck := term_ne_stuck_of_smt_type_seq x T hxTy
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
      (by decide) hxNe with ⟨isList, hListBool⟩
  cases isList
  · have hIntroEq :
        __str_nary_intro x =
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false, hNilList, __eo_requires, native_teq, native_ite,
        SmtEval.native_ite, SmtEval.native_not]
    have hApplyNe :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
          Term.Stuck := by
      simpa [hIntroEq] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil =
          mkConcat x nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    have hApplyNN :
        __smtx_typeof (__eo_to_smt (mkConcat x nil)) ≠ SmtType.None := by
      simpa [hIntroEq, hApplyEq] using hIntroNN
    rcases str_concat_args_of_non_none x nil hApplyNN with
      ⟨U, hxTyU, hNilTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
      simpa [hUT] using hNilTyU
    rw [hIntroEq, hApplyEq]
    exact str_nary_elim_str_concat_cons_ne_stuck_of_seq x nil T hxTy
      hNilTy hNilList
  · have hIntroEq : __str_nary_intro x = x :=
      str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
    rw [hIntroEq]
    exact str_nary_elim_ne_stuck_of_list_seq x T hxTy
      (by simpa using hListBool)

theorem pair_first_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __pair_first x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__pair_first] at h

theorem pair_second_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __pair_second x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__pair_second] at h

theorem str_strip_prefix_left_ne_stuck_of_ne_stuck (x y : Term)
    (h : __str_strip_prefix x y ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_strip_prefix] at h

theorem str_strip_prefix_right_ne_stuck_of_ne_stuck (x y : Term)
    (h : __str_strip_prefix x y ≠ Term.Stuck) :
    y ≠ Term.Stuck := by
  intro hy
  subst y
  cases x <;> simp [__str_strip_prefix] at h


theorem pair_first_pair (x y : Term) :
    __pair_first (mkPair x y) = x := by
  rfl

theorem pair_second_pair (x y : Term) :
    __pair_second (mkPair x y) = y := by
  rfl


theorem eo_interprets_strip_prefix_pair_of_eq
    (M : SmtModel) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true)
    (hStrip : __str_strip_prefix x y = mkPair x y) :
    eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y))) true := by
  rw [hStrip]
  simpa [mkPair, pair_first_pair, pair_second_pair] using hXY

theorem eo_interprets_eq_symm_local
    (M : SmtModel) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true) :
    eo_interprets M (mkEq y x) true := by
  have hBool : RuleProofs.eo_has_bool_type (mkEq y x) :=
    RuleProofs.eo_has_bool_type_eq_symm x y
      (RuleProofs.eo_has_bool_type_of_interprets_true M (mkEq x y) hXY)
  exact RuleProofs.eo_interprets_eq_of_rel M y x hBool
    (RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))
      (RuleProofs.eo_interprets_eq_rel M x y hXY))

theorem eo_interprets_eq_self_of_has_bool_type
    (M : SmtModel) (x : Term)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x x)) :
    eo_interprets M (mkEq x x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M x x hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt x)))

theorem str_strip_prefix_left_not_str_concat
    (x y : Term)
    (hx : x ≠ Term.Stuck)
    (hy : y ≠ Term.Stuck)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __str_strip_prefix x y = mkPair x y := by
  cases x with
  | Stuck =>
      exact False.elim (hx rfl)
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                exact False.elim (hNotConcat ⟨t, a, rfl⟩)
              · cases y <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
                  mkPair, hop] at hy ⊢
          | _ =>
              cases y <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
                mkPair] at hy ⊢
      | _ =>
          cases y <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
            mkPair] at hy ⊢
  | _ =>
      cases y <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
        mkPair] at hy ⊢

theorem str_strip_prefix_right_not_str_concat
    (x y : Term)
    (hx : x ≠ Term.Stuck)
    (hy : y ≠ Term.Stuck)
    (hNotConcat : ¬ ∃ head tail : Term, y = mkConcat head tail) :
    __str_strip_prefix x y = mkPair x y := by
  cases y with
  | Stuck =>
      exact False.elim (hy rfl)
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                exact False.elim (hNotConcat ⟨t, a, rfl⟩)
              · cases x <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
                  mkPair, hop] at hx ⊢
          | _ =>
              cases x <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
                mkPair] at hx ⊢
      | _ =>
          cases x <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
            mkPair] at hx ⊢
  | _ =>
      cases x <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
        mkPair] at hx ⊢

theorem str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __str_strip_prefix (mkConcat t t2) (mkConcat u s2) =
      __str_strip_prefix t2 s2 := by
  change __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
    (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __str_strip_prefix t2 s2
  rw [h, eo_ite_true]

theorem term_ne_stuck_of_eo_is_list_nil_true (f nil : Term)
    (hNil : __eo_is_list_nil f nil = Term.Boolean true) :
    nil ≠ Term.Stuck := by
  intro h
  subst nil
  cases f <;> simp [__eo_is_list_nil] at hNil

theorem seq_empty_not_str_concat (A : Term)
    (hEmpty : __seq_empty A ≠ Term.Stuck) :
    ¬ ∃ head tail : Term, __seq_empty A = mkConcat head tail := by
  intro hConcat
  rcases hConcat with ⟨head, tail, hEq⟩
  cases A with
  | Stuck =>
      simp [__seq_empty] at hEmpty
  | Apply f a =>
      cases f with
      | UOp op =>
          by_cases hop : op = UserOp.Seq
          · subst op
            cases a with
            | UOp op' =>
                by_cases hchar : op' = UserOp.Char
                · subst op'
                  simp [__seq_empty, mkConcat] at hEq
                · simp [__seq_empty, mkConcat, hchar] at hEq
            | _ =>
                simp [__seq_empty, mkConcat] at hEq
          · simp [__seq_empty, mkConcat, hop] at hEq
      | _ =>
          simp [__seq_empty, mkConcat] at hEq
  | _ =>
      simp [__seq_empty, mkConcat] at hEq


theorem str_strip_prefix_tail_ne_stuck_of_concat_eo_eq_true
    (t u t2 s2 : Term)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (h : __eo_eq t u = Term.Boolean true) :
    __str_strip_prefix t2 s2 ≠ Term.Stuck := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 h] at hStrip
  exact hStrip

theorem str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __str_strip_prefix (mkConcat t t2) (mkConcat u s2) =
      mkPair (mkConcat t t2) (mkConcat u s2) := by
  change __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
    (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkPair (mkConcat t t2) (mkConcat u s2)
  rw [h, eo_ite_false]
  simp [__eo_l_1___str_strip_prefix, mkPair]

theorem pair_first_str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __pair_first (__str_strip_prefix t2 s2) := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 h]

theorem pair_second_str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __pair_second (__str_strip_prefix t2 s2) := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 h]

theorem pair_first_str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkConcat t t2 := by
  rw [str_strip_prefix_concat_of_eo_eq_false t u t2 s2 h]
  rfl

theorem pair_second_str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkConcat u s2 := by
  rw [str_strip_prefix_concat_of_eo_eq_false t u t2 s2 h]
  rfl

theorem eo_interprets_str_strip_prefix_concat_false
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean false)
    (hXY : eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  exact eo_interprets_strip_prefix_pair_of_eq M (mkConcat t t2) (mkConcat u s2)
    hXY (str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond)

theorem eo_interprets_str_strip_prefix_concat_true_of_tail
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean true)
    (hTail : eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix t2 s2))
        (__pair_second (__str_strip_prefix t2 s2))) true) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  exact hTail

theorem eo_interprets_rev_strip_prefix_concat_true_of_tail
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean true)
    (hTail :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2)))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))) true := by
  rw [pair_first_str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  rw [pair_second_str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  exact hTail

theorem eo_interprets_rev_strip_prefix_concat_false_of_eq
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean false)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))) true := by
  rw [pair_first_str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond]
  rw [pair_second_str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond]
  exact hXY

theorem pair_first_str_strip_prefix_self_eq_pair_second (x : Term)
    (hStrip : __str_strip_prefix x x ≠ Term.Stuck) :
    __pair_first (__str_strip_prefix x x) =
      __pair_second (__str_strip_prefix x x) := by
  fun_cases __str_strip_prefix x x
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2
    subst_vars
    have hIte :
        __eo_ite (__eo_eq t t) (__str_strip_prefix t2 t2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat t t2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t t) (__str_strip_prefix t2 t2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat t t2)) hIte with
      hCond | hCond
    · have hTailNonStuck : __str_strip_prefix t2 t2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      rw [hCond, eo_ite_true]
      exact pair_first_str_strip_prefix_self_eq_pair_second t2 hTailNonStuck
    · cases t <;> simp [__eo_eq, native_teq] at hCond
  · simp [__eo_l_1___str_strip_prefix, pair_first_pair,
      pair_second_pair]
termination_by sizeOf x
decreasing_by
  all_goals subst_vars; simp_wf; omega


theorem eo_interprets_double_rev_intros_of_self
    (M : SmtModel) (s t : Term)
    (hS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          s) true)
    (hT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          t) true)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  let ds :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)))
  let dt :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)))
  have hTdt : eo_interprets M (mkEq t dt) true :=
    eo_interprets_eq_symm_local M dt t (by simpa [dt] using hT)
  have hDsT : eo_interprets M (mkEq ds t) true :=
    RuleProofs.eo_interprets_eq_trans M ds s t
      (by simpa [ds] using hS) hST
  have hDsDt : eo_interprets M (mkEq ds dt) true :=
    RuleProofs.eo_interprets_eq_trans M ds t dt hDsT hTdt
  simpa [ds, dt] using hDsDt

theorem native_unpack_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq, native_unpack_pack_seq T xs]

theorem native_pack_unpack_seq :
    (s : SmtSeq) ->
      native_pack_seq (__smtx_elem_typeof_seq_value s) (native_unpack_seq s) = s
  | SmtSeq.empty _ => rfl
  | SmtSeq.cons _ vs => by
      simp [native_pack_seq, native_unpack_seq, __smtx_elem_typeof_seq_value,
        native_pack_unpack_seq vs]

theorem native_pack_seq_inj (T : SmtType) {xs ys : List SmtValue}
    (h : native_pack_seq T xs = native_pack_seq T ys) :
    xs = ys := by
  have h' := congrArg native_unpack_seq h
  simpa [_root_.native_unpack_pack_seq] using h'

theorem smt_seq_rel_pack_append_cancel (T : SmtType) :
    ∀ xs ys zs : List SmtValue,
      RuleProofs.smt_seq_rel
          (native_pack_seq T (xs ++ ys)) (native_pack_seq T (xs ++ zs)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T ys) (native_pack_seq T zs)
  | xs, ys, zs, h => by
      have hEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 h
      have hList : xs ++ ys = xs ++ zs := native_pack_seq_inj T hEq
      have hTail : ys = zs := List.append_cancel_left hList
      exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 (by rw [hTail])

theorem smt_seq_rel_pack_length_eq (T U : SmtType) :
    ∀ xs ys : List SmtValue,
      RuleProofs.smt_seq_rel (native_pack_seq T xs) (native_pack_seq U ys) ->
      xs.length = ys.length
  | xs, ys, h => by
      have hEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 h
      have hLen := congrArg (fun s => (native_unpack_seq s).length) hEq
      simpa [_root_.native_unpack_pack_seq] using hLen

theorem smt_seq_rel_pack_append_right (T : SmtType) :
    ∀ xs ys zs : List SmtValue,
      RuleProofs.smt_seq_rel (native_pack_seq T xs) (native_pack_seq T ys) ->
      RuleProofs.smt_seq_rel
        (native_pack_seq T (xs ++ zs)) (native_pack_seq T (ys ++ zs))
  | xs, ys, zs, h => by
      have hEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 h
      have hList : xs = ys := native_pack_seq_inj T hEq
      exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 (by rw [hList])

theorem smt_seq_rel_pack_append_left (T : SmtType)
    (xs ys zs : List SmtValue)
    (h : RuleProofs.smt_seq_rel (native_pack_seq T ys) (native_pack_seq T zs)) :
    RuleProofs.smt_seq_rel
      (native_pack_seq T (xs ++ ys)) (native_pack_seq T (xs ++ zs)) := by
  have hEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 h
  have hList : ys = zs := native_pack_seq_inj T hEq
  exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 (by rw [hList])

theorem smt_seq_rel_pack_append_right_cancel (T : SmtType) :
    ∀ ys zs xs : List SmtValue,
      RuleProofs.smt_seq_rel
          (native_pack_seq T (ys ++ xs)) (native_pack_seq T (zs ++ xs)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T ys) (native_pack_seq T zs)
  | ys, zs, xs, h => by
      have hEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 h
      have hList : ys ++ xs = zs ++ xs := native_pack_seq_inj T hEq
      have hHead : ys = zs := List.append_cancel_right hList
      exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 (by rw [hHead])

theorem smt_seq_rel_pack_unpack (T : SmtType) (s : SmtSeq)
    (hT : __smtx_elem_typeof_seq_value s = T) :
    RuleProofs.smt_seq_rel s (native_pack_seq T (native_unpack_seq s)) := by
  exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 (by
    rw [← hT]
    exact (native_pack_unpack_seq s).symm)

theorem elem_typeof_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue,
      __smtx_elem_typeof_seq_value (native_pack_seq T xs) = T
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, __smtx_elem_typeof_seq_value,
        elem_typeof_pack_seq T xs]

theorem smt_value_rel_str_concat_nil_empty
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt nil))
      (SmtValue.Seq (SmtSeq.empty T)) := by
  cases nil <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
      native_teq] at hNil
  case UOp1 op A =>
      cases op <;> simp at hNil
      case seq_empty =>
        change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
          SmtType.Seq T at hNilTy
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt_seq_empty (__eo_to_smt_type A)))
          (SmtValue.Seq (SmtSeq.empty T))
        cases hA : __eo_to_smt_type A with
        | Seq U =>
            rw [hA] at hNilTy
            simp [__eo_to_smt_seq_empty] at hNilTy ⊢
            have hNN : __smtx_typeof (SmtTerm.seq_empty U) ≠ SmtType.None := by
              rw [hNilTy]
              intro h
              cases h
            have hTyU := TranslationProofs.smtx_typeof_seq_empty_of_non_none U hNN
            have hUT : U = T := by
              rw [hTyU] at hNilTy
              injection hNilTy
            subst T
            rw [__smtx_model_eval.eq_79]
            unfold RuleProofs.smt_value_rel
            simp [__smtx_model_eval_eq, native_veq]
        | _ =>
            rw [hA] at hNilTy
            simp [__eo_to_smt_seq_empty, TranslationProofs.smtx_typeof_none] at hNilTy
  case String s =>
      subst s
      change __smtx_typeof (SmtTerm.String (native_string_lit "")) = SmtType.Seq T at hNilTy
      rw [__smtx_typeof.eq_4] at hNilTy
      simp [native_string_lit, native_string_valid, native_ite] at hNilTy
      cases hNilTy
      unfold RuleProofs.smt_value_rel
      change __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.String (native_string_lit "")))
        (SmtValue.Seq (SmtSeq.empty SmtType.Char)) = SmtValue.Boolean true
      rw [__smtx_model_eval.eq_4]
      simp [native_pack_string, native_string_lit,
        native_pack_seq, __smtx_model_eval_eq, native_veq]

theorem smt_value_rel_str_concat_right_empty
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hEmpty := eval_seq_empty_typeof M x T hxTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmpty]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ []))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
  rw [List.append_nil, hsxElem]
  change RuleProofs.smt_seq_rel (native_pack_seq T (native_unpack_seq sx)) sx
  exact RuleProofs.smt_seq_rel_symm sx (native_pack_seq T (native_unpack_seq sx))
    (smt_seq_rel_pack_unpack T sx hsxElem)

theorem smt_value_rel_str_concat_left_empty
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat (__seq_empty (__eo_typeof x)) x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hEmpty := eval_seq_empty_typeof M x T hxTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmpty]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value (SmtSeq.empty T))
      ([] ++ native_unpack_seq sx))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
  simp [__smtx_elem_typeof_seq_value]
  change RuleProofs.smt_seq_rel (native_pack_seq T (native_unpack_seq sx)) sx
  exact RuleProofs.smt_seq_rel_symm sx (native_pack_seq T (native_unpack_seq sx))
    (smt_seq_rel_pack_unpack T sx hsxElem)

theorem smt_value_rel_str_concat_list_nil_left_empty
    (M : SmtModel) (hM : model_wf M) (nil x : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat nil x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hNilValTy := smt_model_eval_preserves_type M hM (__eo_to_smt nil)
    (SmtType.Seq T) hNilTy (seq_ne_none T) (type_inhabited_seq T)
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hNilValTy with ⟨snil, hNilEval⟩
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hNilRel := smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy
  unfold RuleProofs.smt_value_rel at hNilRel ⊢
  rw [hNilEval] at hNilRel
  cases snil with
  | cons v vs =>
      simp [__smtx_model_eval_eq, native_veq] at hNilRel
  | empty U =>
      have hUT : U = T := by
        have hTy : __smtx_typeof_value (SmtValue.Seq (SmtSeq.empty U)) =
            SmtType.Seq T := by
          simpa [hNilEval] using hNilValTy
        simp [__smtx_typeof_value, __smtx_typeof_seq_value] at hTy
        exact hTy
      subst T
      have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq U := by
        simpa [hxEval, __smtx_typeof_value] using hxValTy
      have hsxElem : __smtx_elem_typeof_seq_value sx = U :=
        elem_typeof_seq_value_of_typeof_seq_value hsxTy
      rw [smtx_model_eval_str_concat_term_eq, hNilEval, hxEval]
      change __smtx_model_eval_eq
        (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value
          (SmtSeq.empty U)) ([] ++ native_unpack_seq sx)))
        (SmtValue.Seq sx) = SmtValue.Boolean true
      simp [__smtx_elem_typeof_seq_value]
      change RuleProofs.smt_seq_rel (native_pack_seq U (native_unpack_seq sx)) sx
      exact RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq U (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack U sx hsxElem)

theorem smt_value_rel_str_concat_list_nil_right_empty
    (M : SmtModel) (hM : model_wf M) (x nil : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hNilValTy := smt_model_eval_preserves_type M hM (__eo_to_smt nil)
    (SmtType.Seq T) hNilTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hNilValTy with ⟨snil, hNilEval⟩
  have hNilRel := smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy
  unfold RuleProofs.smt_value_rel at hNilRel ⊢
  rw [hNilEval] at hNilRel
  cases snil with
  | cons v vs =>
      simp [__smtx_model_eval_eq, native_veq] at hNilRel
  | empty U =>
      have hUT : U = T := by
        have hTy : __smtx_typeof_value (SmtValue.Seq (SmtSeq.empty U)) =
            SmtType.Seq T := by
          simpa [hNilEval] using hNilValTy
        simp [__smtx_typeof_value, __smtx_typeof_seq_value] at hTy
        exact hTy
      subst T
      rw [smtx_model_eval_str_concat_term_eq, hxEval, hNilEval]
      change __smtx_model_eval_eq
        (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_unpack_seq sx ++ []))) (SmtValue.Seq sx) =
          SmtValue.Boolean true
      rw [List.append_nil]
      have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq U := by
        simpa [hxEval, __smtx_typeof_value] using hxValTy
      have hsxElem : __smtx_elem_typeof_seq_value sx = U :=
        elem_typeof_seq_value_of_typeof_seq_value hsxTy
      rw [hsxElem]
      change RuleProofs.smt_seq_rel (native_pack_seq U (native_unpack_seq sx)) sx
      exact RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq U (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack U sx hsxElem)

theorem smt_value_rel_str_concat_left_of_rel_empty
    (M : SmtModel) (hM : model_wf M) (empty x : Term) (T : SmtType)
    (hEmptyTy : __smtx_typeof (__eo_to_smt empty) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt empty))
      (SmtValue.Seq (SmtSeq.empty T))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat empty x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hEmptyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt empty)
    (SmtType.Seq T) hEmptyTy (seq_ne_none T) (type_inhabited_seq T)
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hEmptyValTy with ⟨sempty, hEmptyEval⟩
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  unfold RuleProofs.smt_value_rel at hEmptyRel ⊢
  rw [hEmptyEval] at hEmptyRel
  cases sempty with
  | cons v vs =>
      simp [__smtx_model_eval_eq, native_veq] at hEmptyRel
  | empty U =>
      have hUT : U = T := by
        have hTy : __smtx_typeof_value (SmtValue.Seq (SmtSeq.empty U)) =
            SmtType.Seq T := by
          simpa [hEmptyEval] using hEmptyValTy
        simp [__smtx_typeof_value, __smtx_typeof_seq_value] at hTy
        exact hTy
      subst T
      have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq U := by
        simpa [hxEval, __smtx_typeof_value] using hxValTy
      have hsxElem : __smtx_elem_typeof_seq_value sx = U :=
        elem_typeof_seq_value_of_typeof_seq_value hsxTy
      rw [smtx_model_eval_str_concat_term_eq, hEmptyEval, hxEval]
      change __smtx_model_eval_eq
        (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value
          (SmtSeq.empty U)) ([] ++ native_unpack_seq sx)))
        (SmtValue.Seq sx) = SmtValue.Boolean true
      simp [__smtx_elem_typeof_seq_value]
      change RuleProofs.smt_seq_rel (native_pack_seq U (native_unpack_seq sx)) sx
      exact RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq U (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack U sx hsxElem)

theorem smt_value_rel_str_concat_right_of_rel_empty
    (M : SmtModel) (hM : model_wf M) (x empty : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyTy : __smtx_typeof (__eo_to_smt empty) = SmtType.Seq T)
    (hEmptyRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt empty))
      (SmtValue.Seq (SmtSeq.empty T))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x empty)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hEmptyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt empty)
    (SmtType.Seq T) hEmptyTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hEmptyValTy with ⟨sempty, hEmptyEval⟩
  unfold RuleProofs.smt_value_rel at hEmptyRel ⊢
  rw [hEmptyEval] at hEmptyRel
  cases sempty with
  | cons v vs =>
      simp [__smtx_model_eval_eq, native_veq] at hEmptyRel
  | empty U =>
      have hUT : U = T := by
        have hTy : __smtx_typeof_value (SmtValue.Seq (SmtSeq.empty U)) =
            SmtType.Seq T := by
          simpa [hEmptyEval] using hEmptyValTy
        simp [__smtx_typeof_value, __smtx_typeof_seq_value] at hTy
        exact hTy
      subst T
      rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmptyEval]
      change __smtx_model_eval_eq
        (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_unpack_seq sx ++ []))) (SmtValue.Seq sx) =
          SmtValue.Boolean true
      rw [List.append_nil]
      have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq U := by
        simpa [hxEval, __smtx_typeof_value] using hxValTy
      have hsxElem : __smtx_elem_typeof_seq_value sx = U :=
        elem_typeof_seq_value_of_typeof_seq_value hsxTy
      rw [hsxElem]
      change RuleProofs.smt_seq_rel (native_pack_seq U (native_unpack_seq sx)) sx
      exact RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq U (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack U sx hsxElem)

theorem smt_value_rel_str_concat_left_congr
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hxy : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y z))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z)
    (SmtType.Seq T) hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hszTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
    simpa [hzEval, __smtx_typeof_value] using hzValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hszElem : __smtx_elem_typeof_seq_value sz = T :=
    elem_typeof_seq_value_of_typeof_seq_value hszTy
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hxySeq : RuleProofs.smt_seq_rel sx sy := by
    unfold RuleProofs.smt_value_rel at hxy
    unfold RuleProofs.smt_seq_rel
    simpa [hxEval, hyEval] using hxy
  have hPackXY :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sx))
        (native_pack_seq T (native_unpack_seq sy)) :=
    RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx)) sx
      (native_pack_seq T (native_unpack_seq sy))
      (RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq T (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack T sx hsxElem))
      (RuleProofs.smt_seq_rel_trans sx sy
        (native_pack_seq T (native_unpack_seq sy)) hxySeq
        (smt_seq_rel_pack_unpack T sy hsyElem))
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
  rw [hxEval, hyEval, hzEval]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sz)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sz))) =
      SmtValue.Boolean true
  rw [hsxElem, hsyElem]
  exact smt_seq_rel_pack_append_right T
    (native_unpack_seq sx) (native_unpack_seq sy) (native_unpack_seq sz)
    hPackXY

theorem smt_value_rel_str_concat_right_congr
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hyz : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x y)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x z))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z)
    (SmtType.Seq T) hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hszTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
    simpa [hzEval, __smtx_typeof_value] using hzValTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hszElem : __smtx_elem_typeof_seq_value sz = T :=
    elem_typeof_seq_value_of_typeof_seq_value hszTy
  have hyzSeq : RuleProofs.smt_seq_rel sy sz := by
    unfold RuleProofs.smt_value_rel at hyz
    unfold RuleProofs.smt_seq_rel
    simpa [hyEval, hzEval] using hyz
  have hPackYZ :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sy))
        (native_pack_seq T (native_unpack_seq sz)) :=
    RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sy)) sy
      (native_pack_seq T (native_unpack_seq sz))
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem))
      (RuleProofs.smt_seq_rel_trans sy sz
        (native_pack_seq T (native_unpack_seq sz)) hyzSeq
        (smt_seq_rel_pack_unpack T sz hszElem))
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
  rw [hxEval, hyEval, hzEval]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sy)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sz))) =
      SmtValue.Boolean true
  rw [hsxElem]
  exact smt_seq_rel_pack_append_left T (native_unpack_seq sx)
    (native_unpack_seq sy) (native_unpack_seq sz) hPackYZ

theorem smt_value_rel_str_concat_assoc
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat (mkConcat x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (mkConcat y z)))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z)
    (SmtType.Seq T) hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq M (mkConcat x y) z]
  rw [smtx_model_eval_str_concat_term_eq M x y]
  rw [smtx_model_eval_str_concat_term_eq M x (mkConcat y z)]
  rw [smtx_model_eval_str_concat_term_eq M y z]
  rw [hxEval, hyEval, hzEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    _root_.native_unpack_pack_seq, elem_typeof_pack_seq, hsxElem, hsyElem,
    List.append_assoc, RuleProofs.smtx_model_eval_eq_refl]

theorem eo_interprets_str_concat_assoc
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    eo_interprets M
      (mkEq (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z)))
      true := by
  have hXYTy : __smtx_typeof (__eo_to_smt (mkConcat x y)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x y T hxTy hyTy
  have hYZTy : __smtx_typeof (__eo_to_smt (mkConcat y z)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y z T hyTy hzTy
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat (mkConcat x y) z)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (mkConcat x y) z T hXYTy hzTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat x (mkConcat y z))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x (mkConcat y z) T hxTy hYZTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z)) hBool
    (smt_value_rel_str_concat_assoc M hM x y z T hxTy hyTy hzTy)

theorem eo_interprets_str_concat_assoc_symm
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    eo_interprets M
      (mkEq (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z))
      true := by
  have hXYTy : __smtx_typeof (__eo_to_smt (mkConcat x y)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x y T hxTy hyTy
  have hYZTy : __smtx_typeof (__eo_to_smt (mkConcat y z)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y z T hyTy hzTy
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x (mkConcat y z))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x (mkConcat y z) T hxTy hYZTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat (mkConcat x y) z)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (mkConcat x y) z T hXYTy hzTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z) hBool
    (RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt (mkConcat (mkConcat x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (mkConcat y z))))
      (smt_value_rel_str_concat_assoc M hM x y z T hxTy hyTy hzTy))

theorem eo_interprets_str_concat_left_congr_of_seq
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hXY : eo_interprets M (mkEq x y) true) :
    eo_interprets M (mkEq (mkConcat x z) (mkConcat y z)) true := by
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x z)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x z T hxTy hzTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat y z)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y z T hyTy hzTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x z) (mkConcat y z)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M (mkConcat x z)
    (mkConcat y z) hBool
    (smt_value_rel_str_concat_left_congr M hM x y z T hxTy hyTy hzTy
      (RuleProofs.eo_interprets_eq_rel M x y hXY))

theorem eo_interprets_str_concat_right_congr_of_seq
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hYZ : eo_interprets M (mkEq y z) true) :
    eo_interprets M (mkEq (mkConcat x y) (mkConcat x z)) true := by
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x y T hxTy hyTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat x z)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x z T hxTy hzTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x y) (mkConcat x z)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M (mkConcat x y)
    (mkConcat x z) hBool
    (smt_value_rel_str_concat_right_congr M hM x y z T hxTy hyTy hzTy
      (RuleProofs.eo_interprets_eq_rel M y z hYZ))

theorem smt_value_rel_list_concat_rec_str_concat
    (M : SmtModel) (hM : model_wf M) :
    ∀ a z T,
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt z) = SmtType.Seq T ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
  | a, z, T, hList, haTy, hzTy => by
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          simp [__eo_is_list] at hList
      | case2 a hA =>
          change __smtx_typeof SmtTerm.None = SmtType.Seq T at hzTy
          rw [TranslationProofs.smtx_typeof_none] at hzTy
          cases hzTy
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.str_concat :=
            eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat)
              g x y hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.str_concat) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
              x y hList
          have hConcatNN :
              __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
            rw [haTy]
            exact seq_ne_none T
          rcases str_concat_args_of_non_none x y hConcatNN with
            ⟨U, hxTy, hyTyU⟩
          have hConcatTyU :
              __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
            smt_typeof_str_concat_of_seq x y U hxTy hyTyU
          have hUT : U = T := by
            have hSeq : SmtType.Seq U = SmtType.Seq T := by
              rw [← hConcatTyU, haTy]
            injection hSeq
          have hxTyT :
              __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
            simpa [hUT] using hxTy
          have hyTy :
              __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
            simpa [hUT] using hyTyU
          have hZNonStuck : z ≠ Term.Stuck := by
            intro hz
            subst z
            change __smtx_typeof SmtTerm.None = SmtType.Seq T at hzTy
            rw [TranslationProofs.smtx_typeof_none] at hzTy
            cases hzTy
          have hTailConcat :
              __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.str_concat)
              y z hTailList hZNonStuck
          have hTailRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (__eo_list_concat_rec y z)))
                (__smtx_model_eval M (__eo_to_smt (mkConcat y z))) :=
            ih hTailList hyTy hzTy
          have hTailConcatTy :
              __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y z)) =
                SmtType.Seq T :=
            smt_typeof_list_concat_rec_str_concat_of_seq y z T hTailList
              hyTy hzTy
          have hYZTy :
              __smtx_typeof (__eo_to_smt (mkConcat y z)) = SmtType.Seq T :=
            smt_typeof_str_concat_of_seq y z T hyTy hzTy
          rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
            x y z hTailConcat]
          have hCongr :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat x (__eo_list_concat_rec y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat x (mkConcat y z)))) :=
            smt_value_rel_str_concat_right_congr M hM x
              (__eo_list_concat_rec y z) (mkConcat y z) T
              hxTyT hTailConcatTy hYZTy hTailRel
          have hAssoc :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat x (mkConcat y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat (mkConcat x y) z))) :=
            RuleProofs.smt_value_rel_symm
              (__smtx_model_eval M
                (__eo_to_smt (mkConcat (mkConcat x y) z)))
              (__smtx_model_eval M
                (__eo_to_smt (mkConcat x (mkConcat y z))))
              (smt_value_rel_str_concat_assoc M hM x y z T
                hxTyT hyTy hzTy)
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat x (__eo_list_concat_rec y z))))
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat x (mkConcat y z))))
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat (mkConcat x y) z)))
            hCongr hAssoc
      | case4 nil z hNil hZ hNot =>
          have hGet :
              __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil ≠
                Term.Stuck :=
            eo_get_nil_rec_ne_stuck_of_is_list_true
              (Term.UOp UserOp.str_concat) nil hList
          have hReq :
              __eo_requires
                  (__eo_is_list_nil (Term.UOp UserOp.str_concat) nil)
                  (Term.Boolean true) nil ≠ Term.Stuck := by
            simpa [__eo_get_nil_rec] using hGet
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
                Term.Boolean true :=
            eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.str_concat) nil)
              (Term.Boolean true) nil hReq
          rw [eo_list_concat_rec_str_concat_nil_eq_of_nil_true
            nil z hNilTrue]
          exact RuleProofs.smt_value_rel_symm
            (__smtx_model_eval M (__eo_to_smt (mkConcat nil z)))
            (__smtx_model_eval M (__eo_to_smt z))
            (smt_value_rel_str_concat_list_nil_left_empty M hM
              nil z T hNilTrue haTy hzTy)

theorem smt_value_rel_str_nary_intro_ite
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (mkConcat x (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (mkConcat x (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))
  · rw [hCond, eo_ite_false]
    exact smt_value_rel_str_concat_right_empty M hM x T hxTy

theorem smt_value_rel_str_nary_intro_default
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    rw [hCond, eo_ite_false, hApplyEq]
    exact smt_value_rel_str_concat_right_empty M hM x T hxTy

theorem smt_value_rel_str_nary_intro
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hNilEq : nil = __seq_empty (__eo_typeof x) := by
    simpa [nil] using strConcat_nil_eq_seq_empty_of_type hTy
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil
      (by simpa [nil] using strConcat_nil_is_list_nil_of_type hTy)
  have hxNe : x ≠ Term.Stuck := term_ne_stuck_of_smt_type_seq x T hxTy
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
      (by decide) hxNe with ⟨isList, hListBool⟩
  cases isList
  · have hIntroEq :
        __str_nary_intro x =
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false, hNilList, __eo_requires, native_teq, native_ite,
        SmtEval.native_ite, SmtEval.native_not]
    have hApplyNe :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
          Term.Stuck := by
      simpa [hIntroEq] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil =
          mkConcat x nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    rw [hIntroEq, hApplyEq, hNilEq]
    exact smt_value_rel_str_concat_right_empty M hM x T hxTy
  · have hIntroEq : __str_nary_intro x = x :=
      str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
    rw [hIntroEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt x))

theorem smt_typeof_str_nary_intro_default_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))) ≠ SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))))) = SmtType.Seq T := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact hxTy
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    have hApplyNN :
        __smtx_typeof
          (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
            SmtType.None := by
      simpa [hCond, eo_ite_false, hApplyEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x)) hApplyNN with
      ⟨U, hxTyU, hEmptyTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T := by
      simpa [hUT] using hEmptyTyU
    rw [hCond, eo_ite_false, hApplyEq]
    exact smt_typeof_str_concat_of_seq x (__seq_empty (__eo_typeof x)) T
      hxTy hEmptyTy

theorem smt_typeof_str_nary_intro_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN : __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil
      (by simpa [nil] using strConcat_nil_is_list_nil_of_type hTy)
  have hxNe : x ≠ Term.Stuck := term_ne_stuck_of_smt_type_seq x T hxTy
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
      (by decide) hxNe with ⟨isList, hListBool⟩
  cases isList
  · have hIntroEq :
        __str_nary_intro x =
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false, hNilList, __eo_requires, native_teq, native_ite,
        SmtEval.native_ite, SmtEval.native_not]
    have hApplyNN :
        __smtx_typeof
            (__eo_to_smt
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
                nil)) ≠ SmtType.None := by
      simpa [hIntroEq] using hIntroNN
    have hApplyNe :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
          Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil)
        hApplyNN
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil =
          mkConcat x nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    have hConcatNN :
        __smtx_typeof (__eo_to_smt (mkConcat x nil)) ≠ SmtType.None := by
      simpa [hApplyEq] using hApplyNN
    rcases str_concat_args_of_non_none x nil hConcatNN with
      ⟨U, hxTyU, hNilTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
      simpa [hUT] using hNilTyU
    rw [hIntroEq, hApplyEq]
    exact smt_typeof_str_concat_of_seq x nil T hxTy hNilTy
  · have hIntroEq : __str_nary_intro x = x :=
      str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
    rw [hIntroEq]
    exact hxTy

theorem smt_typeof_str_nary_intro_default_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))) ≠ SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))))) = SmtType.Seq T := by
  exact smt_typeof_str_nary_intro_default_of_seq x T hxTy hIntroNN hIntro

theorem smt_typeof_str_nary_intro_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN : __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
      SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T := by
  exact smt_typeof_str_nary_intro_of_seq x T hxTy hIntroNN

theorem smt_typeof_str_nary_intro_default_of_seq_empty_typeof
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))))) = SmtType.Seq T := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact hxTy
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T :=
      smt_typeof_seq_empty_typeof x T hxTy hEmptyNN
    rw [hCond, eo_ite_false, hApplyEq]
    exact smt_typeof_str_concat_of_seq x (__seq_empty (__eo_typeof x))
      T hxTy hEmptyTy

theorem smt_typeof_str_nary_intro_of_seq_empty_typeof
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hNilEq : nil = __seq_empty (__eo_typeof x) := by
    simpa [nil] using strConcat_nil_eq_seq_empty_of_type hTy
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil
      (by simpa [nil] using strConcat_nil_is_list_nil_of_type hTy)
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    rw [hNilEq]
    exact smt_typeof_seq_empty_typeof x T hxTy hEmptyNN
  have hxNe : x ≠ Term.Stuck := term_ne_stuck_of_smt_type_seq x T hxTy
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
      (by decide) hxNe with ⟨isList, hListBool⟩
  cases isList
  · have hIntroEq :
        __str_nary_intro x =
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false, hNilList, __eo_requires, native_teq, native_ite,
        SmtEval.native_ite, SmtEval.native_not]
    have hApplyNe :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
          Term.Stuck := by
      simpa [hIntroEq] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil =
          mkConcat x nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    rw [hIntroEq, hApplyEq]
    exact smt_typeof_str_concat_of_seq x nil T hxTy hNilTy
  · have hIntroEq : __str_nary_intro x = x :=
      str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
    rw [hIntroEq]
    exact hxTy

theorem str_nary_intro_has_smt_translation_of_seq_empty_typeof
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None := by
  rw [smt_typeof_str_nary_intro_of_seq_empty_typeof x T hxTy hEmptyNN
    hIntro]
  exact seq_ne_none T


theorem smt_typeof_double_rev_str_nary_intro_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x)))) =
      SmtType.Seq T := by
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hIntroList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro x) hRevIntro
  exact smt_typeof_list_rev_list_rev_str_concat_of_seq (__str_nary_intro x)
    T hIntroList hIntroTy hRevIntro

theorem smt_value_rel_str_nary_elim_concat_ite
    (M : SmtModel) (hM : model_wf M) (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) ≠
        Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))))
      (__smtx_model_eval M (__eo_to_smt (mkConcat t ss))) := by
  have hConcatNN : __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTy, hssTy⟩
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · have hEmptyEq := eq_of_eo_eq_true_local ss (__seq_empty (__eo_typeof t)) hCond
    have hssEq : ss = __seq_empty (__eo_typeof t) := hEmptyEq.symm
    subst ss
    rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt (mkConcat t (__seq_empty (__eo_typeof t)))))
      (__smtx_model_eval M (__eo_to_smt t))
      (smt_value_rel_str_concat_right_empty M hM t U htTy)
  · rw [hCond, eo_ite_false]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (mkConcat t ss)))

theorem smt_value_rel_str_nary_elim_requires
    (M : SmtModel) (t : Term)
    (hElim : __eo_requires t (__seq_empty (__eo_typeof t)) t ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_requires t (__seq_empty (__eo_typeof t)) t)))
      (__smtx_model_eval M (__eo_to_smt t)) := by
  rw [eo_requires_eq_result_of_ne_stuck t (__seq_empty (__eo_typeof t)) t hElim]
  exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt t))

theorem smt_value_rel_str_nary_elim
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true :=
    str_nary_elim_is_list_true_of_ne_stuck x hElim
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, hEq⟩
    subst x
    rcases str_concat_args_of_seq_type head tail T hxTy with
      ⟨hHeadTy, hTailTy⟩
    have hElimEq :
        __str_nary_elim (mkConcat head tail) =
          __eo_ite (__eo_is_list_nil (Term.UOp UserOp.str_concat) tail)
            head (mkConcat head tail) := by
      rw [__str_nary_elim, __eo_list_singleton_elim, hList]
      rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
        (__eo_list_singleton_elim_2 (mkConcat head tail)) (by decide)]
      rfl
    have hTailNe : tail ≠ Term.Stuck :=
      term_ne_stuck_of_smt_type_seq tail T hTailTy
    rcases eo_is_list_nil_str_concat_boolean_of_ne_stuck tail hTailNe with
      ⟨isNil, hNilBool⟩
    cases isNil
    · rw [hElimEq, hNilBool, eo_ite_false]
      exact RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (__eo_to_smt (mkConcat head tail)))
    · rw [hElimEq, hNilBool, eo_ite_true]
      exact RuleProofs.smt_value_rel_symm
        (__smtx_model_eval M (__eo_to_smt (mkConcat head tail)))
        (__smtx_model_eval M (__eo_to_smt head))
        (smt_value_rel_str_concat_list_nil_right_empty M hM head tail T
          hHeadTy (by simpa using hNilBool) hTailTy)
  · have hElim2 : __eo_list_singleton_elim_2 x = x :=
      str_nary_elim_2_eq_self_of_not_str_concat x hList hConcat
    have hElimEq : __str_nary_elim x = x := by
      rw [__str_nary_elim, __eo_list_singleton_elim, hList]
      rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
        (__eo_list_singleton_elim_2 x) (by decide)]
      exact hElim2
    rw [hElimEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt x))

theorem smt_value_rel_str_nary_elim_list_nil_empty
    (M : SmtModel) (hM : model_wf M) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hElim : __str_nary_elim nil ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim nil)))
      (SmtValue.Seq (SmtSeq.empty T)) := by
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M (__eo_to_smt (__str_nary_elim nil)))
    (__smtx_model_eval M (__eo_to_smt nil))
    (SmtValue.Seq (SmtSeq.empty T))
    (smt_value_rel_str_nary_elim M hM nil T hNilTy hElim)
    (smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy)

theorem smt_typeof_str_nary_elim_concat_of_seq (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElimNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
          (mkConcat t ss))) ≠ SmtType.None)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss))) = SmtType.Seq T := by
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTyU, hssTyU⟩
  have hConcatTyU :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq t ss U htTyU hssTyU
  have hUT : U = T := by
    have hSeq : SmtType.Seq U = SmtType.Seq T := by
      rw [← hConcatTyU, hConcatTy]
    injection hSeq
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    simpa [hUT] using htTyU
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · rw [hCond, eo_ite_true]
    exact htTy
  · rw [hCond, eo_ite_false]
    exact hConcatTy

theorem smt_typeof_str_nary_elim_requires_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __eo_requires x (__seq_empty (__eo_typeof x)) x ≠ Term.Stuck) :
    __smtx_typeof
      (__eo_to_smt (__eo_requires x (__seq_empty (__eo_typeof x)) x)) =
        SmtType.Seq T := by
  rw [eo_requires_eq_result_of_ne_stuck x (__seq_empty (__eo_typeof x)) x hElim]
  exact hxTy

theorem smt_typeof_str_nary_elim_concat_of_seq_ne_stuck
    (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss))) = SmtType.Seq T := by
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTyU, hssTyU⟩
  have hConcatTyU :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq t ss U htTyU hssTyU
  have hUT : U = T := by
    have hSeq : SmtType.Seq U = SmtType.Seq T := by
      rw [← hConcatTyU, hConcatTy]
    injection hSeq
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    simpa [hUT] using htTyU
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · rw [hCond, eo_ite_true]
    exact htTy
  · rw [hCond, eo_ite_false]
    exact hConcatTy

private theorem smt_typeof_str_nary_elim_of_seq_ne_stuck_core
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T := by
  have hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true :=
    str_nary_elim_is_list_true_of_ne_stuck x hElim
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, hEq⟩
    subst x
    rcases str_concat_args_of_seq_type head tail T hxTy with
      ⟨hHeadTy, hTailTy⟩
    have hElimEq :
        __str_nary_elim (mkConcat head tail) =
          __eo_ite (__eo_is_list_nil (Term.UOp UserOp.str_concat) tail)
            head (mkConcat head tail) := by
      rw [__str_nary_elim, __eo_list_singleton_elim, hList]
      rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
        (__eo_list_singleton_elim_2 (mkConcat head tail)) (by decide)]
      rfl
    have hTailNe : tail ≠ Term.Stuck :=
      term_ne_stuck_of_smt_type_seq tail T hTailTy
    rcases eo_is_list_nil_str_concat_boolean_of_ne_stuck tail hTailNe with
      ⟨isNil, hNilBool⟩
    cases isNil
    · rw [hElimEq, hNilBool, eo_ite_false]
      exact hxTy
    · rw [hElimEq, hNilBool, eo_ite_true]
      exact hHeadTy
  · have hElim2 : __eo_list_singleton_elim_2 x = x :=
      str_nary_elim_2_eq_self_of_not_str_concat x hList hConcat
    have hElimEq : __str_nary_elim x = x := by
      rw [__str_nary_elim, __eo_list_singleton_elim, hList]
      rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
        (__eo_list_singleton_elim_2 x) (by decide)]
      exact hElim2
    rw [hElimEq]
    exact hxTy

theorem smt_typeof_str_nary_elim_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElimNN : __smtx_typeof (__eo_to_smt (__str_nary_elim x)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T := by
  exact smt_typeof_str_nary_elim_of_seq_ne_stuck_core x T hxTy
    (RuleProofs.term_ne_stuck_of_has_smt_translation
      (__str_nary_elim x) hElimNN)

theorem smt_typeof_str_nary_elim_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T := by
  exact smt_typeof_str_nary_elim_of_seq_ne_stuck_core x T hxTy hElim

theorem smt_typeof_str_nary_elim_list_rev_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck)
    (hElim :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) a) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) a))) =
      SmtType.Seq T := by
  have hRevTy :
      __smtx_typeof
          (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.str_concat) a)) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq a T hList haTy hRev
  exact smt_typeof_str_nary_elim_of_seq_ne_stuck
    (__eo_list_rev (Term.UOp UserOp.str_concat) a) T hRevTy hElim

theorem smt_typeof_str_nary_elim_list_rev_list_rev_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck)
    (hElim :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a)) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) a)))) =
      SmtType.Seq T := by
  have hRevRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) a))) =
        SmtType.Seq T :=
    smt_typeof_list_rev_list_rev_str_concat_of_seq a T hList haTy hRev
  exact smt_typeof_str_nary_elim_of_seq_ne_stuck
    (__eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) a)) T hRevRevTy hElim

theorem eo_has_bool_type_rev_elim_eq_of_seq
    (x y : Term) (T : SmtType)
    (hxList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true)
    (hyList :
      __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hxRev : __eo_list_rev (Term.UOp UserOp.str_concat) x ≠ Term.Stuck)
    (hyRev : __eo_list_rev (Term.UOp UserOp.str_concat) y ≠ Term.Stuck)
    (hxElim :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) x) ≠
        Term.Stuck)
    (hyElim :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) y) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) x))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) y))) := by
  have hxElimTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) x))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_of_seq x T hxList hxTy hxRev hxElim
  have hyElimTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) y))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_of_seq y T hyList hyTy hyRev hyElim
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hxElimTy, hyElimTy]
  · rw [hxElimTy]
    exact seq_ne_none T

theorem eo_has_bool_type_double_rev_elim_eq_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck)
    (hElimRevRev :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a)) ≠
        Term.Stuck)
    (hElimA : __str_nary_elim a ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a)))
        (__str_nary_elim a)) := by
  have hLeftTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__eo_list_rev (Term.UOp UserOp.str_concat) a)))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_list_rev_of_seq a T hList haTy
      hRev hElimRevRev
  have hRightTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim a)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck a T haTy hElimA
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hLeftTy, hRightTy]
  · rw [hLeftTy]
    exact seq_ne_none T

theorem eo_interprets_double_rev_elim_eq_of_list
    (M : SmtModel) (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck)
    (hElimA : __str_nary_elim a ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a)))
        (__str_nary_elim a)) true := by
  have hRevRevEq :=
    eo_list_rev_list_rev_str_concat_eq_of_list_true a hList hRev
  rw [hRevRevEq]
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim a)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck a T haTy hElimA
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim a) (__str_nary_elim a)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · rw [hElimTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim a) (__str_nary_elim a) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim a))))

theorem eo_interprets_double_rev_intro_elim_eq_of_str_concat
    (M : SmtModel) (head tail : Term) (T : SmtType)
    (hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head tail)) = SmtType.Seq T)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_nary_intro (mkConcat head tail)) ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro (mkConcat head tail)))))
        (__str_nary_elim (__str_nary_intro (mkConcat head tail)))) true := by
  have hConsNN :
      __smtx_typeof (__eo_to_smt (mkConcat head tail)) ≠ SmtType.None := by
    rw [hConsTy]
    exact seq_ne_none T
  have hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro (mkConcat head tail))) ≠
        SmtType.None :=
    str_nary_intro_concat_has_smt_translation head tail hConsNN
  have hIntro : __str_nary_intro (mkConcat head tail) ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro (mkConcat head tail)) hRevIntro
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro (mkConcat head tail))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck (mkConcat head tail) T
      hConsTy hIntroNN hIntro
  have hIntroList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_nary_intro (mkConcat head tail)) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro (mkConcat head tail)) hRevIntro
  have hElimIntro :
      __str_nary_elim (__str_nary_intro (mkConcat head tail)) ≠
        Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq (mkConcat head tail) T
      hConsTy hIntroNN hIntro
  exact eo_interprets_double_rev_elim_eq_of_list M
    (__str_nary_intro (mkConcat head tail)) T hIntroList hIntroTy
    hRevIntro hElimIntro

theorem eo_has_bool_type_double_rev_intro_elim_eq_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck)
    (hElimRevRev :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))) ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) := by
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hElimIntro :
      __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq x T hxTy hIntroNN
      hIntro
  have hIntroList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro x) hRevIntro
  exact eo_has_bool_type_double_rev_elim_eq_of_seq
    (__str_nary_intro x) T hIntroList hIntroTy hRevIntro hElimRevRev
    hElimIntro

theorem eo_has_bool_type_rev_cons_snoc_of_seq
    (head tail : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck)
    (hRevTail :
      __eo_list_rev (Term.UOp UserOp.str_concat) tail ≠ Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)) ≠
        Term.Stuck)
    (hElimTail :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
          head)) := by
  have hConsList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) head tail (by decide) hTailList
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head tail)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head tail T hHeadTy hTailTy
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head tail)))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_of_seq (mkConcat head tail) T
      hConsList hConsTy hRevCons hElimCons
  have hTailElimTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) tail))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_of_seq tail T hTailList hTailTy
      hRevTail hElimTail
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (mkConcat
              (__str_nary_elim
                (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
              head)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq
      (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
      head T hTailElimTy hHeadTy
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hLhsTy, hRhsTy]
  · rw [hLhsTy]
    exact seq_ne_none T

theorem eo_has_bool_type_str_concat_list_nil_left_empty_of_seq
    (nil x : Term) (T : SmtType)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (mkEq (mkConcat nil x) x) := by
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (mkConcat nil x)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq nil x T hNilTy hxTy
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hConcatTy, hxTy]
  · rw [hConcatTy]
    exact seq_ne_none T

theorem eo_has_bool_type_str_concat_list_nil_right_empty_of_seq
    (x nil : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (mkEq (mkConcat x nil) x) := by
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (mkConcat x nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x nil T hxTy hNilTy
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hConcatTy, hxTy]
  · rw [hConcatTy]
    exact seq_ne_none T

theorem eo_has_bool_type_str_nary_elim_eq_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (mkEq (__str_nary_elim x) x) := by
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck x T hxTy hElim
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hElimTy, hxTy]
  · rw [hElimTy]
    exact seq_ne_none T

theorem eo_interprets_str_nary_elim_rev_rec_nil_eq
    (M : SmtModel) (nil acc : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T)
    (hElimAcc : __str_nary_elim acc ≠ Term.Stuck) :
    eo_interprets M
      (mkEq (__str_nary_elim (__eo_list_rev_rec nil acc))
        (__str_nary_elim acc)) true := by
  have hRecEq :
      __eo_list_rev_rec nil acc = acc :=
    eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil acc hNil
  rw [hRecEq]
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim acc)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck acc T hAccTy hElimAcc
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim acc) (__str_nary_elim acc)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · rw [hElimTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim acc) (__str_nary_elim acc) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim acc))))

theorem eo_interprets_rev_cons_snoc_of_list_nil
    (M : SmtModel) (hM : model_wf M) (head nil : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
        Term.Stuck)
    (hRevNil :
      __eo_list_rev (Term.UOp UserOp.str_concat) nil ≠ Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)) ≠
        Term.Stuck)
    (hElimNil :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) nil) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) nil))
          head)) true := by
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil hNil
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) nil))
          head)) :=
    eo_has_bool_type_rev_cons_snoc_of_seq head nil T hHeadTy hNilList
      hNilTy hRevCons hRevNil hElimCons hElimNil
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
        mkConcat head nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck head nil hNil hRevCons
  have hRevNilEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) nil = nil :=
    eo_list_rev_str_concat_nil_eq_of_nil_true nil hNil
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hElimCons' : __str_nary_elim (mkConcat head nil) ≠ Term.Stuck := by
    simpa [hRevConsEq] using hElimCons
  have hElimNil' : __str_nary_elim nil ≠ Term.Stuck := by
    simpa [hRevNilEq] using hElimNil
  let lhs :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil))
  let rhs :=
    mkConcat
      (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) nil))
      head
  have hLhsToCons : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil))) := by
    subst lhs
    rw [hRevConsEq]
    exact smt_value_rel_str_nary_elim M hM (mkConcat head nil) T
      hConsTy hElimCons'
  have hConsToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM head nil T
      hHeadTy hNil hNilTy
  have hLhsToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt head)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) hLhsToCons hConsToHead
  have hElimNilTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim nil)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck nil T hNilTy hElimNil'
  have hElimNilEmpty : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim nil)))
      (SmtValue.Seq (SmtSeq.empty T)) :=
    smt_value_rel_str_nary_elim_list_nil_empty M hM nil T hNil hNilTy
      hElimNil'
  have hRhsToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt rhs))
      (__smtx_model_eval M (__eo_to_smt head)) := by
    subst rhs
    rw [hRevNilEq]
    exact smt_value_rel_str_concat_left_of_rel_empty M hM
      (__str_nary_elim nil) head T hElimNilTy hHeadTy hElimNilEmpty
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt rhs)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M (__eo_to_smt rhs)) hLhsToHead
      (RuleProofs.smt_value_rel_symm
        (__smtx_model_eval M (__eo_to_smt rhs))
        (__smtx_model_eval M (__eo_to_smt head)) hRhsToHead)
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool hRel

theorem eo_interprets_str_concat_right_empty_of_bool
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x (__seq_empty (__eo_typeof x))) x)) :
    eo_interprets M (mkEq (mkConcat x (__seq_empty (__eo_typeof x))) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat x (__seq_empty (__eo_typeof x))) x hBool
    (smt_value_rel_str_concat_right_empty M hM x T hxTy)

theorem eo_interprets_str_concat_left_empty_of_bool
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat (__seq_empty (__eo_typeof x)) x) x)) :
    eo_interprets M (mkEq (mkConcat (__seq_empty (__eo_typeof x)) x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat (__seq_empty (__eo_typeof x)) x) x hBool
    (smt_value_rel_str_concat_left_empty M hM x T hxTy)

theorem eo_interprets_str_concat_list_nil_left_empty_of_bool
    (M : SmtModel) (hM : model_wf M) (nil x : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat nil x) x)) :
    eo_interprets M (mkEq (mkConcat nil x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (mkConcat nil x) x hBool
    (smt_value_rel_str_concat_list_nil_left_empty M hM nil x T
      hNil hNilTy hxTy)

theorem eo_interprets_str_concat_list_nil_right_empty_of_bool
    (M : SmtModel) (hM : model_wf M) (x nil : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat x nil) x)) :
    eo_interprets M (mkEq (mkConcat x nil) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (mkConcat x nil) x hBool
    (smt_value_rel_str_concat_list_nil_right_empty M hM x nil T
      hxTy hNil hNilTy)

theorem eo_interprets_str_nary_intro_ite_eq_of_bool
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (mkConcat x (__seq_empty (__eo_typeof x))) ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))
        x)) :
    eo_interprets M
      (mkEq
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))
        x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (mkConcat x (__seq_empty (__eo_typeof x)))) x hBool
    (smt_value_rel_str_nary_intro_ite M hM x T hxTy hIntro)

theorem eo_interprets_str_nary_elim_concat_ite_eq_of_bool
    (M : SmtModel) (hM : model_wf M) (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) ≠
        Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
        (mkConcat t ss))) :
    eo_interprets M
      (mkEq
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
        (mkConcat t ss)) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
    (mkConcat t ss) hBool
    (smt_value_rel_str_nary_elim_concat_ite M hM t ss T hConcatTy hElim)

theorem eo_interprets_str_nary_elim_requires_eq_of_bool
    (M : SmtModel) (t : Term)
    (hElim : __eo_requires t (__seq_empty (__eo_typeof t)) t ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__eo_requires t (__seq_empty (__eo_typeof t)) t) t)) :
    eo_interprets M
      (mkEq (__eo_requires t (__seq_empty (__eo_typeof t)) t) t) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_requires t (__seq_empty (__eo_typeof t)) t) t hBool
    (smt_value_rel_str_nary_elim_requires M t hElim)

theorem eo_interprets_str_nary_intro_eq_of_bool
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (__str_nary_intro x) x)) :
    eo_interprets M (mkEq (__str_nary_intro x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (__str_nary_intro x) x hBool
    (smt_value_rel_str_nary_intro M hM x T hxTy hIntro)

theorem eo_interprets_str_nary_elim_eq_of_bool
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (__str_nary_elim x) x)) :
    eo_interprets M (mkEq (__str_nary_elim x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (__str_nary_elim x) x hBool
    (smt_value_rel_str_nary_elim M hM x T hxTy hElim)

theorem eo_interprets_str_nary_elim_intro_eq_of_seq
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hElimIntro : __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck) :
    eo_interprets M (mkEq (__str_nary_elim (__str_nary_intro x)) x)
      true := by
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hElimIntroTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (__str_nary_intro x))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (__str_nary_intro x) T
      hIntroTy hElimIntro
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__str_nary_intro x)) x) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimIntroTy, hxTy]
    · rw [hElimIntroTy]
      exact seq_ne_none T
  have hElimRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__str_nary_elim (__str_nary_intro x))))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x))) :=
    smt_value_rel_str_nary_elim M hM (__str_nary_intro x) T
      hIntroTy hElimIntro
  have hIntroRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
        (__smtx_model_eval M (__eo_to_smt x)) :=
    smt_value_rel_str_nary_intro M hM x T hxTy hIntro
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim (__str_nary_intro x)) x hBool
    (RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M
        (__eo_to_smt (__str_nary_elim (__str_nary_intro x))))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt x)) hElimRel hIntroRel)

theorem eo_interprets_str_nary_elim_intro_eq_of_seq_ne_stuck
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    eo_interprets M (mkEq (__str_nary_elim (__str_nary_intro x)) x)
      true := by
  exact eo_interprets_str_nary_elim_intro_eq_of_seq M hM x T hxTy
    hIntroNN hIntro
    (str_nary_elim_str_nary_intro_ne_stuck_of_seq x T hxTy
      hIntroNN hIntro)

theorem eo_interprets_double_rev_intro_elim_eq_of_rel
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck)
    (hElimRevRev :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))) ≠ Term.Stuck)
    (hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro x)))))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  let revrev :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x))
  let intro := __str_nary_intro x
  have hIntroTy :
      __smtx_typeof (__eo_to_smt intro) = SmtType.Seq T := by
    simpa [intro] using
      smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hRevRevTy :
      __smtx_typeof (__eo_to_smt revrev) = SmtType.Seq T := by
    simpa [revrev, intro] using
      smt_typeof_double_rev_str_nary_intro_of_seq x T hxTy hIntroNN
        hIntro hRevIntro
  have hElimIntro : __str_nary_elim intro ≠ Term.Stuck := by
    simpa [intro] using
      str_nary_elim_str_nary_intro_ne_stuck_of_seq x T hxTy hIntroNN
        hIntro
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim revrev) (__str_nary_elim intro)) := by
    simpa [revrev, intro] using
      eo_has_bool_type_double_rev_intro_elim_eq_of_seq x T hxTy hIntroNN
        hIntro hRevIntro hElimRevRev
  have hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim revrev)))
        (__smtx_model_eval M (__eo_to_smt revrev)) :=
    smt_value_rel_str_nary_elim M hM revrev T hRevRevTy
      (by simpa [revrev] using hElimRevRev)
  have hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro)))
        (__smtx_model_eval M (__eo_to_smt intro)) :=
    smt_value_rel_str_nary_elim M hM intro T hIntroTy hElimIntro
  have hAllRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim revrev)))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim revrev)))
      (__smtx_model_eval M (__eo_to_smt revrev))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro)))
      hLeftRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt revrev))
        (__smtx_model_eval M (__eo_to_smt intro))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro)))
        (by simpa [revrev, intro] using hRel)
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro)))
          (__smtx_model_eval M (__eo_to_smt intro)) hRightRel))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim revrev) (__str_nary_elim intro) hBool hAllRel

theorem eo_interprets_double_rev_elim_eq_of_cons_nil
    (M : SmtModel) (head nil : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat head nil))))
        (__str_nary_elim (mkConcat head nil))) true := by
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
        mkConcat head nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck head nil hNil hRevCons
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hElimCons :
      __str_nary_elim (mkConcat head nil) ≠ Term.Stuck :=
    str_nary_elim_str_concat_cons_ne_stuck_of_seq head nil T hHeadTy
      hNilTy (eo_is_list_str_concat_nil_true_of_nil_true nil hNil)
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (mkConcat head nil))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (mkConcat head nil) T
      hConsTy hElimCons
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (mkConcat head nil))
        (__str_nary_elim (mkConcat head nil))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · rw [hElimTy]
      exact seq_ne_none T
  rw [hRevEq, hRevEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim (mkConcat head nil))
    (__str_nary_elim (mkConcat head nil)) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim (mkConcat head nil)))))

theorem eo_is_list_nil_str_concat_seq_empty_of_ne_stuck
    (A : Term) (hEmpty : __seq_empty A ≠ Term.Stuck) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__seq_empty A) = Term.Boolean true := by
  cases A <;>
    simp [__seq_empty, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq] at hEmpty ⊢
  case Apply f a =>
    cases f with
    | UOp op =>
        cases op <;> try rfl
        case Seq =>
          cases a <;> try rfl
          case UOp op =>
            cases op <;> try rfl
    | _ =>
        rfl

theorem eo_is_list_nil_str_concat_seq_empty_typeof_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__seq_empty (__eo_typeof x)) = Term.Boolean true := by
  exact eo_is_list_nil_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
    (seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy)

theorem eo_interprets_double_rev_elim_eq_of_nil
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hElimNil : __str_nary_elim nil ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) nil)))
        (__str_nary_elim nil)) true := by
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) nil = nil :=
    eo_list_rev_str_concat_nil_eq_of_nil_true nil hNil
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim nil)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck nil T hNilTy hElimNil
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim nil) (__str_nary_elim nil)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · rw [hElimTy]
      exact seq_ne_none T
  rw [hRevEq, hRevEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim nil) (__str_nary_elim nil) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim nil))))

theorem eo_interprets_double_rev_intro_elim_eq_of_default
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck)
    (hDefault :
      __str_nary_intro x =
        __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x)))) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  let empty := __seq_empty (__eo_typeof x)
  have hEmptyNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    simpa [empty] using
      eo_is_list_nil_str_concat_seq_empty_typeof_of_seq x T hxTy
  have hIntroIte :
      __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) ≠ Term.Stuck := by
    simpa [empty, hDefault] using hIntro
  rcases eo_ite_cases_of_ne_stuck (__eo_eq x empty) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
      hIntroIte with hCond | hCond
  · have hEmptyEq : empty = x :=
      eq_of_eo_eq_true_local x empty hCond
    have hIntroEq : __str_nary_intro x = x := by
      rw [hDefault]
      simp [empty, hCond, eo_ite_true]
    have hXNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
          Term.Boolean true := by
      simpa [hEmptyEq] using hEmptyNil
    have hElimIntro :
        __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck :=
      str_nary_elim_str_nary_intro_ne_stuck_of_seq x T hxTy hIntroNN
        hIntro
    have hElimX : __str_nary_elim x ≠ Term.Stuck := by
      simpa [hIntroEq] using hElimIntro
    simpa [hIntroEq] using
      eo_interprets_double_rev_elim_eq_of_nil M x T hXNil hxTy hElimX
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntroIte
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty = mkConcat x empty :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hIntroEq : __str_nary_intro x = mkConcat x empty := by
      rw [hDefault]
      simp [empty, hCond, eo_ite_false, hApplyEq]
    have hConcatNN :
        __smtx_typeof (__eo_to_smt (mkConcat x empty)) ≠ SmtType.None := by
      simpa [hIntroEq] using hIntroNN
    rcases str_concat_args_of_non_none x empty hConcatNN with
      ⟨U, hxTyU, hEmptyTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt empty) = SmtType.Seq T := by
      simpa [hUT] using hEmptyTyU
    simpa [hIntroEq, empty] using
      eo_interprets_double_rev_elim_eq_of_cons_nil M x empty T hxTy
        hEmptyNil hEmptyTy
        (by simpa [hIntroEq, empty] using hRevIntro)

theorem strConcat_nil_eq_seq_empty_of_ne_stuck (A : Term)
    (hNil : __eo_nil (Term.UOp UserOp.str_concat) A ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.str_concat) A = __seq_empty A := by
  cases A <;> simp [__eo_nil, __eo_nil_str_concat, __seq_empty] at hNil ⊢
  case Apply f a =>
    cases f <;> try simp at hNil ⊢
    case UOp op =>
      cases op <;> try simp at hNil ⊢

theorem strConcat_nil_is_list_nil_of_ne_stuck (A : Term)
    (hNil : __eo_nil (Term.UOp UserOp.str_concat) A ≠ Term.Stuck) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__eo_nil (Term.UOp UserOp.str_concat) A) = Term.Boolean true := by
  have hEq := strConcat_nil_eq_seq_empty_of_ne_stuck A hNil
  rw [hEq]
  exact eo_is_list_nil_str_concat_seq_empty_of_ne_stuck A
    (by simpa [← hEq] using hNil)

theorem str_nary_elim_str_nary_intro_eq_of_not_str_concat
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_elim (__str_nary_intro x) = x := by
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hxNe : x ≠ Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck x hIntro
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
      (by decide) hxNe with ⟨isList, hListBool⟩
  cases isList
  · have hReq :
        __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) nil)
            (Term.Boolean true)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              nil) ≠ Term.Stuck := by
      simpa [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false] using hIntro
    have hNilList :
        __eo_is_list (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true :=
      eo_requires_eq_of_ne_stuck
        (__eo_is_list (Term.UOp UserOp.str_concat) nil) (Term.Boolean true)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil) hReq
    have hApplyNe :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
          Term.Stuck :=
      eo_requires_result_ne_stuck_of_ne_stuck
        (__eo_is_list (Term.UOp UserOp.str_concat) nil) (Term.Boolean true)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil) hReq
    have hNilNe : nil ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    have hNilNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true := by
      simpa [nil] using
        strConcat_nil_is_list_nil_of_ne_stuck (__eo_typeof x)
          (by simpa [nil] using hNilNe)
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil =
          mkConcat x nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    have hIntroEq : __str_nary_intro x = mkConcat x nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false, hNilList, hApplyEq, __eo_requires, native_teq,
        native_ite, SmtEval.native_ite, SmtEval.native_not]
    rw [hIntroEq]
    simp [__str_nary_elim, __eo_list_singleton_elim,
      eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
        x nil (by decide) hNilList,
      __eo_list_singleton_elim_2, hNilNil, eo_ite_true,
      __eo_requires, native_teq, native_ite, SmtEval.native_ite,
      SmtEval.native_not]
  · have hIntroEq : __str_nary_intro x = x :=
      str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
    have hElimEq : __str_nary_elim x = x := by
      rw [__str_nary_elim, __eo_list_singleton_elim, hListBool]
      rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
        (__eo_list_singleton_elim_2 x) (by decide)]
      exact str_nary_elim_2_eq_self_of_not_str_concat x
        (by simpa using hListBool) hNotConcat
    rw [hIntroEq, hElimEq]

theorem eo_is_list_nil_str_concat_of_list_true_not_concat_local
    (x : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
      Term.Boolean true := by
  cases x with
  | Stuck =>
      simp [__eo_is_list] at hList
  | Apply f a =>
      cases f with
      | Apply g b =>
          by_cases hg : g = Term.UOp UserOp.str_concat
          · subst g
            exact False.elim (hNotConcat ⟨b, a, rfl⟩)
          · simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
              __eo_requires, native_ite, SmtEval.native_not, native_teq]
              at hList
            exact False.elim (hg hList.1.symm)
      | _ =>
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
            __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
            native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList
  | String s =>
      simpa [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
        native_ite, SmtEval.native_not, native_teq, __eo_eq] using hList
  | UOp1 op A =>
      cases op <;>
        simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
          __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
          native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList ⊢
  | _ =>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
        native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList ⊢

theorem str_nary_intro_not_str_concat_cases_nil
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    (__str_nary_intro x = x ∧
        __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
          Term.Boolean true) ∨
      ∃ empty,
        __str_nary_intro x = mkConcat x empty ∧
          __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
            Term.Boolean true := by
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hxNe : x ≠ Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck x hIntro
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
      (by decide) hxNe with ⟨isList, hListBool⟩
  cases isList
  · have hReq :
        __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) nil)
            (Term.Boolean true)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              nil) ≠ Term.Stuck := by
      simpa [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false] using hIntro
    have hNilList :
        __eo_is_list (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true :=
      eo_requires_eq_of_ne_stuck
        (__eo_is_list (Term.UOp UserOp.str_concat) nil) (Term.Boolean true)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil) hReq
    have hApplyNe :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
          Term.Stuck :=
      eo_requires_result_ne_stuck_of_ne_stuck
        (__eo_is_list (Term.UOp UserOp.str_concat) nil) (Term.Boolean true)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil) hReq
    have hNilNe : nil ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil =
          mkConcat x nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    have hIntroEq : __str_nary_intro x = mkConcat x nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false, hNilList, hApplyEq, __eo_requires, native_teq,
        native_ite, SmtEval.native_ite, SmtEval.native_not]
    exact Or.inr ⟨nil, hIntroEq,
      by
        simpa [nil] using
          strConcat_nil_is_list_nil_of_ne_stuck (__eo_typeof x)
            (by simpa [nil] using hNilNe)⟩
  · exact Or.inl
      ⟨str_nary_intro_eq_self_of_is_list x (by simpa using hListBool),
        eo_is_list_nil_str_concat_of_list_true_not_concat_local x
          (by simpa using hListBool) hNotConcat⟩

theorem str_nary_intro_not_str_concat_cases
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_intro x = x ∨
      ∃ empty,
        __str_nary_intro x = mkConcat x empty ∧
          __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
            Term.Boolean true := by
  rcases str_nary_intro_not_str_concat_cases_nil x hNotConcat hIntro with
    ⟨hIntroEq, _hNil⟩ | hConcat
  · exact Or.inl hIntroEq
  · exact Or.inr hConcat

theorem str_nary_intro_not_str_concat_cases_typeof_empty
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_intro x = x ∨
      __str_nary_intro x = mkConcat x (__seq_empty (__eo_typeof x)) ∧
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
            (__seq_empty (__eo_typeof x)) =
          Term.Boolean true := by
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hxNe : x ≠ Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck x hIntro
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
      (by decide) hxNe with ⟨isList, hListBool⟩
  cases isList
  · have hReq :
        __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) nil)
            (Term.Boolean true)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              nil) ≠ Term.Stuck := by
      simpa [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false] using hIntro
    have hNilList :
        __eo_is_list (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true :=
      eo_requires_eq_of_ne_stuck
        (__eo_is_list (Term.UOp UserOp.str_concat) nil) (Term.Boolean true)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil) hReq
    have hApplyNe :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
          Term.Stuck :=
      eo_requires_result_ne_stuck_of_ne_stuck
        (__eo_is_list (Term.UOp UserOp.str_concat) nil) (Term.Boolean true)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil) hReq
    have hNilNe : nil ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    have hNilEq : nil = __seq_empty (__eo_typeof x) := by
      simpa [nil] using
        strConcat_nil_eq_seq_empty_of_ne_stuck (__eo_typeof x)
          (by simpa [nil] using hNilNe)
    have hNilNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true := by
      simpa [nil] using
        strConcat_nil_is_list_nil_of_ne_stuck (__eo_typeof x)
          (by simpa [nil] using hNilNe)
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil =
          mkConcat x nil :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) nil hApplyNe
    have hIntroEq : __str_nary_intro x = mkConcat x nil := by
      simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
        eo_ite_false, hNilList, hApplyEq, __eo_requires, native_teq,
        native_ite, SmtEval.native_ite, SmtEval.native_not]
    right
    exact ⟨by rw [hIntroEq, hNilEq],
      by simpa [← hNilEq] using hNilNil⟩
  · exact Or.inl
      (str_nary_intro_eq_self_of_is_list x (by simpa using hListBool))

theorem str_nary_intro_not_str_concat_eq_self_or_empty_typeof_of_seq_wf
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_intro x = x ∨
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None := by
  rcases str_nary_intro_not_str_concat_cases_typeof_empty x hNotConcat
      hIntro with hIntroEq | _hIntroConcat
  · exact Or.inl hIntroEq
  · exact Or.inr
      (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T
        hxTy hTInh hTWf)

theorem str_nary_intro_not_str_concat_eq_self_or_has_smt_translation_of_seq_wf
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_intro x = x ∨
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
        SmtType.None := by
  rcases
      str_nary_intro_not_str_concat_eq_self_or_empty_typeof_of_seq_wf
        x T hxTy hTInh hTWf hNotConcat hIntro with
    hIntroEq | hEmptyNN
  · exact Or.inl hIntroEq
  · exact Or.inr
      (str_nary_intro_has_smt_translation_of_seq_empty_typeof x T hxTy
        hEmptyNN hIntro)

theorem str_nary_intro_has_smt_translation_of_seq_wf
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
      SmtType.None := by
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, hEq⟩
    subst x
    have hNN :
        __smtx_typeof (__eo_to_smt (mkConcat head tail)) ≠
          SmtType.None := by
      rw [hxTy]
      exact seq_ne_none T
    exact str_nary_intro_concat_has_smt_translation head tail hNN
  · rcases
      str_nary_intro_not_str_concat_eq_self_or_has_smt_translation_of_seq_wf
        x T hxTy hTInh hTWf hConcat hIntro with
      hIntroEq | hIntroNN
    · rw [hIntroEq, hxTy]
      exact seq_ne_none T
    · exact hIntroNN


theorem eo_interprets_str_nary_elim_list_nil_empty_of_bool
    (M : SmtModel) (hM : model_wf M) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hElim : __str_nary_elim nil ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim nil) nil)) :
    eo_interprets M (mkEq (__str_nary_elim nil) nil) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (__str_nary_elim nil) nil hBool
    (smt_value_rel_str_nary_elim M hM nil T hNilTy hElim)

theorem eo_interprets_str_nary_elim_list_concat_rec_singleton
    (M : SmtModel) (hM : model_wf M)
    (a head nil : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hElimConcat :
      __str_nary_elim
          (__eo_list_concat_rec a (mkConcat head nil)) ≠ Term.Stuck)
    (hElimA : __str_nary_elim a ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_concat_rec a (mkConcat head nil)))
        (mkConcat (__str_nary_elim a) head)) true := by
  have hZTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hConcatTy :
      __smtx_typeof
          (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil))) =
        SmtType.Seq T :=
    smt_typeof_list_concat_rec_str_concat_of_seq a (mkConcat head nil) T
      hList haTy hZTy
  have hElimConcatTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_concat_rec a (mkConcat head nil)))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (__eo_list_concat_rec a (mkConcat head nil)) T hConcatTy hElimConcat
  have hElimATy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim a)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck a T haTy hElimA
  have hElimAHeadTy :
      __smtx_typeof (__eo_to_smt (mkConcat (__str_nary_elim a) head)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (__str_nary_elim a) head T
      hElimATy hHeadTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_concat_rec a (mkConcat head nil)))
        (mkConcat (__str_nary_elim a) head)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimConcatTy, hElimAHeadTy]
    · rw [hElimConcatTy]
      exact seq_ne_none T
  have hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_concat_rec a (mkConcat head nil)))))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil)))) :=
    smt_value_rel_str_nary_elim M hM
      (__eo_list_concat_rec a (mkConcat head nil)) T hConcatTy hElimConcat
  have hConcatRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat a (mkConcat head nil)))) :=
    smt_value_rel_list_concat_rec_str_concat M hM a (mkConcat head nil) T
      hList haTy hZTy
  have hAElimRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim a))) :=
    RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim a)))
      (__smtx_model_eval M (__eo_to_smt a))
      (smt_value_rel_str_nary_elim M hM a T haTy hElimA)
  have hLeftCongr :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat a (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (__str_nary_elim a)
            (mkConcat head nil)))) :=
    smt_value_rel_str_concat_left_congr M hM a (__str_nary_elim a)
      (mkConcat head nil) T haTy hElimATy hZTy hAElimRel
  have hAssoc :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (__str_nary_elim a) (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (mkConcat (__str_nary_elim a) head) nil))) :=
    RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M
        (__eo_to_smt
          (mkConcat (mkConcat (__str_nary_elim a) head) nil)))
      (__smtx_model_eval M
        (__eo_to_smt (mkConcat (__str_nary_elim a) (mkConcat head nil))))
      (smt_value_rel_str_concat_assoc M hM (__str_nary_elim a) head nil T
        hElimATy hHeadTy hNilTy)
  have hRightNil :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (mkConcat (__str_nary_elim a) head) nil)))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (__str_nary_elim a) head))) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM
      (mkConcat (__str_nary_elim a) head) nil T hElimAHeadTy hNil hNilTy
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__str_nary_elim
            (__eo_list_concat_rec a (mkConcat head nil)))))
      (__smtx_model_eval M
        (__eo_to_smt (mkConcat (__str_nary_elim a) head))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M
        (__eo_to_smt
          (__str_nary_elim
            (__eo_list_concat_rec a (mkConcat head nil)))))
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil))))
      (__smtx_model_eval M
        (__eo_to_smt (mkConcat (__str_nary_elim a) head))) hLeftRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat a (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (__str_nary_elim a) head))) hConcatRel
        (RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M
            (__eo_to_smt (mkConcat a (mkConcat head nil))))
          (__smtx_model_eval M
            (__eo_to_smt (mkConcat (__str_nary_elim a)
              (mkConcat head nil))))
          (__smtx_model_eval M
            (__eo_to_smt (mkConcat (__str_nary_elim a) head))) hLeftCongr
          (RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat (__str_nary_elim a)
                (mkConcat head nil))))
            (__smtx_model_eval M
              (__eo_to_smt
                (mkConcat (mkConcat (__str_nary_elim a) head) nil)))
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat (__str_nary_elim a) head)))
            hAssoc hRightNil)))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim (__eo_list_concat_rec a (mkConcat head nil)))
    (mkConcat (__str_nary_elim a) head) hBool hRel

theorem eo_interprets_rev_cons_snoc_of_seq
    (M : SmtModel) (hM : model_wf M) (head tail : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck)
    (hRevTail :
      __eo_list_rev (Term.UOp UserOp.str_concat) tail ≠ Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)) ≠
        Term.Stuck)
    (hElimTail :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
          head)) true := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail
  have hGet : nil ≠ Term.Stuck := by
    simpa [nil] using
      eo_get_nil_rec_ne_stuck_of_is_list_true
        (Term.UOp UserOp.str_concat) tail hTailList
  have hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true := by
    simpa [nil] using
      eo_is_list_nil_get_nil_rec_of_is_list_true
        (Term.UOp UserOp.str_concat) tail hTailList
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true := by
    simpa [nil] using
      eo_get_nil_rec_is_list_true_of_is_list_true
        (Term.UOp UserOp.str_concat) tail hTailList
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_get_nil_rec_str_concat_of_seq tail T hTailList hTailTy
        (eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) tail hTailList)
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        __eo_list_rev_rec tail (mkConcat head nil) := by
    simpa [nil] using
      eo_list_rev_str_concat_cons_eq_of_ne_stuck head tail hRevCons
  have hNilConcat :
      __eo_list_concat_rec nil (mkConcat head nil) = mkConcat head nil :=
    eo_list_concat_rec_str_concat_nil_eq_of_nil_true nil (mkConcat head nil)
      hNil
  have hRevConsConcatEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        __eo_list_concat_rec (__eo_list_rev_rec tail nil)
          (mkConcat head nil) := by
    rw [hRevConsEq]
    calc
      __eo_list_rev_rec tail (mkConcat head nil) =
          __eo_list_rev_rec tail
            (__eo_list_concat_rec nil (mkConcat head nil)) := by
        rw [hNilConcat]
      _ = __eo_list_concat_rec (__eo_list_rev_rec tail nil)
            (mkConcat head nil) :=
        eo_list_rev_rec_list_concat_rec_singleton_eq tail nil head nil
          hTailList hNilList
  have hRevTailEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) tail =
        __eo_list_rev_rec tail nil := by
    simpa [nil] using
      eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.str_concat) tail
        hRevTail
  have hRevTailRecNonStuck :
      __eo_list_rev_rec tail nil ≠ Term.Stuck := by
    simpa [hRevTailEq] using hRevTail
  have hRevTailRecList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_rev_rec tail nil) = Term.Boolean true :=
    eo_list_rev_rec_is_list_true_of_lists (Term.UOp UserOp.str_concat)
      tail nil hTailList hNilList hRevTailRecNonStuck
  have hRevTailRecTy :
      __smtx_typeof (__eo_to_smt (__eo_list_rev_rec tail nil)) =
        SmtType.Seq T :=
    smt_typeof_list_rev_rec_str_concat_of_seq tail nil T hTailList
      hTailTy hNilTy hRevTailRecNonStuck
  have hElimRec :
      __str_nary_elim (__eo_list_rev_rec tail nil) ≠ Term.Stuck := by
    simpa [hRevTailEq] using hElimTail
  have hElimConcat :
      __str_nary_elim
          (__eo_list_concat_rec (__eo_list_rev_rec tail nil)
            (mkConcat head nil)) ≠ Term.Stuck := by
    simpa [hRevConsConcatEq] using hElimCons
  have hCore :=
    eo_interprets_str_nary_elim_list_concat_rec_singleton M hM
      (__eo_list_rev_rec tail nil) head nil T hRevTailRecList
      hRevTailRecTy hHeadTy hNil hNilTy hElimConcat hElimRec
  simpa [hRevConsConcatEq, hRevTailEq] using hCore

theorem eo_interprets_rev_cons_snoc_of_cons_nil
    (M : SmtModel) (hM : model_wf M) (head mid nil : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hMidTy : __smtx_typeof (__eo_to_smt mid) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat head (mkConcat mid nil)) ≠ Term.Stuck)
    (hRevTail :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil) ≠
        Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat head (mkConcat mid nil))) ≠ Term.Stuck)
    (hElimTail :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat head (mkConcat mid nil))))
        (mkConcat
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil)))
          head)) true := by
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat head (mkConcat mid nil)) =
        mkConcat mid (mkConcat head nil) :=
    eo_list_rev_str_concat_cons_cons_nil_eq_of_ne_stuck head mid nil hNil
      hRevCons
  have hRevTailEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil) =
        mkConcat mid nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck mid nil hNil hRevTail
  have hHeadNilTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt (mkConcat mid nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq mid nil T hMidTy hNilTy
  have hCons2Ty :
      __smtx_typeof (__eo_to_smt (mkConcat mid (mkConcat head nil))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq mid (mkConcat head nil) T hMidTy
      hHeadNilTy
  have hMidHeadTy :
      __smtx_typeof (__eo_to_smt (mkConcat mid head)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq mid head T hMidTy hHeadTy
  have hElimCons' :
      __str_nary_elim (mkConcat mid (mkConcat head nil)) ≠ Term.Stuck := by
    simpa [hRevConsEq] using hElimCons
  have hElimTail' :
      __str_nary_elim (mkConcat mid nil) ≠ Term.Stuck := by
    simpa [hRevTailEq] using hElimTail
  have hElimTailTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (mkConcat mid nil))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (mkConcat mid nil) T
      hTailTy hElimTail'
  let lhs :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (mkConcat head (mkConcat mid nil)))
  let rhs :=
    mkConcat
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil)))
      head
  let midHead := mkConcat mid head
  have hLhsToCons2 :
      eo_interprets M
        (mkEq lhs (mkConcat mid (mkConcat head nil))) true := by
    subst lhs
    rw [hRevConsEq]
    exact eo_interprets_str_nary_elim_eq_of_bool M hM
      (mkConcat mid (mkConcat head nil)) T hCons2Ty hElimCons'
      (eo_has_bool_type_str_nary_elim_eq_of_seq
        (mkConcat mid (mkConcat head nil)) T hCons2Ty hElimCons')
  have hAssoc :
      eo_interprets M
        (mkEq (mkConcat mid (mkConcat head nil))
          (mkConcat (mkConcat mid head) nil)) true :=
    eo_interprets_str_concat_assoc_symm M hM mid head nil T hMidTy
      hHeadTy hNilTy
  have hRightNil :
      eo_interprets M
        (mkEq (mkConcat (mkConcat mid head) nil) midHead) true := by
    subst midHead
    exact eo_interprets_str_concat_list_nil_right_empty_of_bool M hM
      (mkConcat mid head) nil T hMidHeadTy hNil hNilTy
      (eo_has_bool_type_str_concat_list_nil_right_empty_of_seq
        (mkConcat mid head) nil T hMidHeadTy hNilTy)
  have hLhsToMidHead :
      eo_interprets M (mkEq lhs midHead) true :=
    RuleProofs.eo_interprets_eq_trans M lhs
      (mkConcat mid (mkConcat head nil)) midHead hLhsToCons2
      (RuleProofs.eo_interprets_eq_trans M
        (mkConcat mid (mkConcat head nil))
        (mkConcat (mkConcat mid head) nil) midHead hAssoc hRightNil)
  have hElimTailToTail :
      eo_interprets M
        (mkEq (__str_nary_elim (mkConcat mid nil)) (mkConcat mid nil)) true :=
    eo_interprets_str_nary_elim_eq_of_bool M hM (mkConcat mid nil) T
      hTailTy hElimTail'
      (eo_has_bool_type_str_nary_elim_eq_of_seq (mkConcat mid nil) T
        hTailTy hElimTail')
  have hTailToMid :
      eo_interprets M (mkEq (mkConcat mid nil) mid) true :=
    eo_interprets_str_concat_list_nil_right_empty_of_bool M hM mid nil T
      hMidTy hNil hNilTy
      (eo_has_bool_type_str_concat_list_nil_right_empty_of_seq mid nil T
        hMidTy hNilTy)
  have hElimTailToMid :
      eo_interprets M (mkEq (__str_nary_elim (mkConcat mid nil)) mid) true :=
    RuleProofs.eo_interprets_eq_trans M (__str_nary_elim (mkConcat mid nil))
      (mkConcat mid nil) mid hElimTailToTail hTailToMid
  have hRhsToMidHead :
      eo_interprets M (mkEq rhs midHead) true := by
    subst rhs
    rw [hRevTailEq]
    subst midHead
    exact eo_interprets_str_concat_left_congr_of_seq M hM
      (__str_nary_elim (mkConcat mid nil)) mid head T hElimTailTy
      hMidTy hHeadTy hElimTailToMid
  have hMidHeadToRhs : eo_interprets M (mkEq midHead rhs) true :=
    eo_interprets_eq_symm_local M rhs midHead hRhsToMidHead
  have hGoal : eo_interprets M (mkEq lhs rhs) true :=
    RuleProofs.eo_interprets_eq_trans M lhs midHead rhs hLhsToMidHead
      hMidHeadToRhs
  simpa [lhs, rhs] using hGoal

theorem eo_interprets_str_nary_intro_congr_of_seq
    (M : SmtModel) (hM : model_wf M) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hIntroX : __str_nary_intro x ≠ Term.Stuck)
    (hIntroY : __str_nary_intro y ≠ Term.Stuck)
    (hXY : eo_interprets M (mkEq x y) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_intro x) (__str_nary_intro y))) :
    eo_interprets M (mkEq (__str_nary_intro x) (__str_nary_intro y)) true := by
  have hXRel := smt_value_rel_str_nary_intro M hM x T hxTy hIntroX
  have hYRel := smt_value_rel_str_nary_intro M hM y T hyTy hIntroY
  have hXYRel := RuleProofs.eo_interprets_eq_rel M x y hXY
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) hXRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) hXYRel
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y)))
          (__smtx_model_eval M (__eo_to_smt y)) hYRel))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_intro x) (__str_nary_intro y) hBool hRel

theorem eo_interprets_str_nary_elim_congr_of_seq
    (M : SmtModel) (hM : model_wf M) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hElimX : __str_nary_elim x ≠ Term.Stuck)
    (hElimY : __str_nary_elim y ≠ Term.Stuck)
    (hXY : eo_interprets M (mkEq x y) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim x) (__str_nary_elim y))) :
    eo_interprets M (mkEq (__str_nary_elim x) (__str_nary_elim y)) true := by
  have hXRel := smt_value_rel_str_nary_elim M hM x T hxTy hElimX
  have hYRel := smt_value_rel_str_nary_elim M hM y T hyTy hElimY
  have hXYRel := RuleProofs.eo_interprets_eq_rel M x y hXY
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) hXRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) hXYRel
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y)))
          (__smtx_model_eval M (__eo_to_smt y)) hYRel))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim x) (__str_nary_elim y) hBool hRel

theorem smt_seq_rel_concat_left_cancel (T : SmtType) (sx sy sz : SmtSeq) :
    __smtx_elem_typeof_seq_value sy = T ->
    __smtx_elem_typeof_seq_value sz = T ->
    RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sz)) ->
    RuleProofs.smt_seq_rel sy sz := by
  intro hsyElem hszElem h
  have hTail := smt_seq_rel_pack_append_cancel T (native_unpack_seq sx)
    (native_unpack_seq sy) (native_unpack_seq sz) h
  exact RuleProofs.smt_seq_rel_trans sy (native_pack_seq T (native_unpack_seq sy)) sz
    (smt_seq_rel_pack_unpack T sy hsyElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sz)) sz hTail
      (RuleProofs.smt_seq_rel_symm sz (native_pack_seq T (native_unpack_seq sz))
        (smt_seq_rel_pack_unpack T sz hszElem)))

theorem smt_seq_rel_concat_right_cancel (T : SmtType) (sx sy sz : SmtSeq) :
    __smtx_elem_typeof_seq_value sy = T ->
    __smtx_elem_typeof_seq_value sz = T ->
    RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sz ++ native_unpack_seq sx)) ->
    RuleProofs.smt_seq_rel sy sz := by
  intro hsyElem hszElem h
  have hTail := smt_seq_rel_pack_append_right_cancel T (native_unpack_seq sy)
    (native_unpack_seq sz) (native_unpack_seq sx) h
  exact RuleProofs.smt_seq_rel_trans sy (native_pack_seq T (native_unpack_seq sy)) sz
    (smt_seq_rel_pack_unpack T sy hsyElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sz)) sz hTail
      (RuleProofs.smt_seq_rel_symm sz (native_pack_seq T (native_unpack_seq sz))
        (smt_seq_rel_pack_unpack T sz hszElem)))

theorem smt_value_rel_str_concat_left_cancel
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x y)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x z))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y) (SmtType.Seq T)
    hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z) (SmtType.Seq T)
    hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hszTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
    simpa [hzEval, __smtx_typeof_value] using hzValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hszElem : __smtx_elem_typeof_seq_value sz = T :=
    elem_typeof_seq_value_of_typeof_seq_value hszTy
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hyEval, hzEval] at hRel
  rw [hyEval, hzEval]
  change RuleProofs.smt_seq_rel sy sz
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sy)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sz))) =
      SmtValue.Boolean true at hRel
  exact smt_seq_rel_concat_left_cancel (__smtx_elem_typeof_seq_value sx) sx sy sz
    (hsyElem.trans hsxElem.symm) (hszElem.trans hsxElem.symm) hRel

theorem smt_value_rel_str_concat_right_cancel
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat y x)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat z x))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y) (SmtType.Seq T)
    hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z) (SmtType.Seq T)
    hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hszTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
    simpa [hzEval, __smtx_typeof_value] using hzValTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hszElem : __smtx_elem_typeof_seq_value sz = T :=
    elem_typeof_seq_value_of_typeof_seq_value hszTy
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hyEval, hzEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sx)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sz)
      (native_unpack_seq sz ++ native_unpack_seq sx))) =
      SmtValue.Boolean true at hRel
  rw [hsyElem, hszElem] at hRel
  rw [hyEval, hzEval]
  change RuleProofs.smt_seq_rel sy sz
  exact smt_seq_rel_concat_right_cancel T sx sy sz hsyElem hszElem hRel

theorem eo_interprets_str_concat_left_cancel
    (M : SmtModel) (hM : model_wf M) (x y z : Term) :
    eo_interprets M (mkEq (mkConcat x y) (mkConcat x z)) true ->
    eo_interprets M (mkEq y z) true := by
  intro h
  have hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat x y) (mkConcat x z)) :=
    RuleProofs.eo_has_bool_type_of_interprets_true M _ h
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat x y) (mkConcat x z) hBool with ⟨hSame, hLeftNN⟩
  rcases str_concat_args_of_non_none x y hLeftNN with ⟨T, hxTy, hyTy⟩
  have hRightNN : __smtx_typeof (__eo_to_smt (mkConcat x z)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases str_concat_args_of_non_none x z hRightNN with ⟨U, hxTyU, hzTyU⟩
  have hUT : U = T := by
    have hSeq : SmtType.Seq T = SmtType.Seq U := by
      rw [← hxTy, ← hxTyU]
    injection hSeq with hTU
    exact hTU.symm
  have hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    simpa [hUT] using hzTyU
  have hRel := RuleProofs.eo_interprets_eq_rel M (mkConcat x y) (mkConcat x z) h
  have hTailRel := smt_value_rel_str_concat_left_cancel M hM x y z T hxTy hyTy hzTy hRel
  have hYZBool : RuleProofs.eo_has_bool_type (mkEq y z) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hyTy, hzTy]
    · rw [hyTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M y z hYZBool hTailRel

theorem eo_interprets_str_concat_tails_of_head_eo_eq_true
    (M : SmtModel) (hM : model_wf M) (t u t2 s2 : Term)
    (hHead : __eo_eq t u = Term.Boolean true) :
    eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true ->
    eo_interprets M (mkEq t2 s2) true := by
  intro h
  have hUT : u = t := eq_of_eo_eq_true_local t u hHead
  subst u
  exact eo_interprets_str_concat_left_cancel M hM t t2 s2 h

theorem eo_interprets_str_strip_prefix_concat_step
    (M : SmtModel) (hM : model_wf M) (t u t2 s2 : Term)
    (hXY : eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hTail :
      eo_interprets M (mkEq t2 s2) true ->
      __str_strip_prefix t2 s2 ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) ->
      eo_interprets M
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2))))) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  have hIte :
      __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
        Term.Stuck := by
    simpa [__str_strip_prefix] using hStrip
  rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
      (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
    hCond | hCond
  · have hTailEq :=
      eo_interprets_str_concat_tails_of_head_eo_eq_true M hM t u t2 s2 hCond hXY
    have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
      simpa [hCond, eo_ite_true] using hIte
    have hTailBool : RuleProofs.eo_has_bool_type
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) := by
      simpa [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond] using hBool
    exact eo_interprets_str_strip_prefix_concat_true_of_tail M t u t2 s2 hCond
      (hTail hTailEq hTailNonStuck hTailBool)
  · exact eo_interprets_str_strip_prefix_concat_false M t u t2 s2 hCond hXY

theorem eo_interprets_str_strip_prefix_result
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y)))) :
    eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    exact eo_interprets_str_strip_prefix_concat_step M hM t u t2 s2
      hXY hStrip
      (eo_interprets_str_strip_prefix_result M hM t2 s2) hBool
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair, pair_second_pair]
      using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

theorem str_strip_prefix_result_types_of_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__pair_first (__str_strip_prefix x y))) =
        SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__pair_second (__str_strip_prefix x y))) =
        SmtType.Seq T := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    have hLeftNN :
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) ≠ SmtType.None := by
      rw [hxTy]
      exact seq_ne_none T
    have hRightNN :
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) ≠ SmtType.None := by
      rw [hyTy]
      exact seq_ne_none T
    rcases str_concat_args_of_non_none t t2 hLeftNN with ⟨U, htTy, ht2TyU⟩
    rcases str_concat_args_of_non_none u s2 hRightNN with ⟨V, huTy, hs2TyV⟩
    have hLeftTyU :
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq U :=
      smt_typeof_str_concat_of_seq t t2 U htTy ht2TyU
    have hRightTyV :
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq V :=
      smt_typeof_str_concat_of_seq u s2 V huTy hs2TyV
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hLeftTyU, hxTy]
      injection hSeq
    have hVT : V = T := by
      have hSeq : SmtType.Seq V = SmtType.Seq T := by
        rw [← hRightTyV, hyTy]
      injection hSeq
    have ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T := by
      simpa [hUT] using ht2TyU
    have hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T := by
      simpa [hVT] using hs2TyV
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      rw [hCond, eo_ite_true]
      exact str_strip_prefix_result_types_of_seq t2 s2 T ht2Ty hs2Ty hTailNonStuck
    · rw [hCond, eo_ite_false]
      simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair,
        pair_second_pair] using And.intro hxTy hyTy
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair, pair_second_pair]
      using And.intro hxTy hyTy
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega


theorem smt_typeof_seq_of_str_concat_list_nil_non_none
    (x : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
        Term.Boolean true)
    (hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  cases x <;>
    try simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
      native_teq] at hNil
  case UOp1 op A =>
    cases op <;> simp at hNil hXNN ⊢
    case seq_empty =>
      change ∃ T,
        __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
          SmtType.Seq T
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None at hXNN
      cases hA : __eo_to_smt_type A <;>
        simp [__eo_to_smt_seq_empty, hA, TranslationProofs.smtx_typeof_none]
          at hXNN ⊢
      rename_i T
      exact ⟨T,
        TranslationProofs.smtx_typeof_seq_empty_of_non_none T hXNN⟩
  case String s =>
    subst s
    exact ⟨SmtType.Char, by
      change __smtx_typeof (SmtTerm.String (native_string_lit "")) =
        SmtType.Seq SmtType.Char
      rw [__smtx_typeof.eq_4]
      simp [native_string_lit, native_string_valid, native_ite]⟩

theorem smt_typeof_seq_of_not_str_concat_intro_eq_self
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hIntroEq : __str_nary_intro x = x)
    (hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  rcases str_nary_intro_not_str_concat_cases_nil x hNotConcat
      hIntro with ⟨_hIntroEq, hNil⟩ | ⟨empty, hIntroConcat, _hEmptyNil⟩
  · exact smt_typeof_seq_of_str_concat_list_nil_non_none x hNil hXNN
  · have hxConcat : x = mkConcat x empty :=
      hIntroEq.symm.trans hIntroConcat
    exact False.elim (hNotConcat ⟨x, empty, hxConcat⟩)


theorem str_nary_intro_not_str_concat_smt_cases
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None) :
    (__smtx_typeof (__eo_to_smt x) ≠ SmtType.None) ∨
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None := by
  rcases str_nary_intro_not_str_concat_cases_typeof_empty x hNotConcat
      hIntro with hIntroEq | ⟨hIntroEq, _hEmptyNil⟩
  · left
    simpa [hIntroEq] using hIntroNN
  · right
    have hConcatNN :
        __smtx_typeof
            (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
          SmtType.None := by
      simpa [hIntroEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x))
        hConcatNN with
      ⟨_T, _hxTy, hEmptyTy⟩
    rw [hEmptyTy]
    exact seq_ne_none _T

theorem str_nary_intro_not_str_concat_eq_or_empty_smt
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None) :
    __str_nary_intro x = x ∨
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None := by
  rcases str_nary_intro_not_str_concat_cases_typeof_empty x hNotConcat
      hIntro with hIntroEq | ⟨hIntroEq, _hEmptyNil⟩
  · exact Or.inl hIntroEq
  · right
    have hConcatNN :
        __smtx_typeof
            (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
          SmtType.None := by
      simpa [hIntroEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x))
        hConcatNN with
      ⟨_T, _hxTy, hEmptyTy⟩
    rw [hEmptyTy]
    exact seq_ne_none _T

theorem eo_list_rev_str_nary_intro_eq_of_not_str_concat
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
      __str_nary_intro x := by
  rcases str_nary_intro_not_str_concat_cases_nil x hNotConcat hIntro with
    ⟨hIntroEq, hXNil⟩ | ⟨empty, hIntroEq, hEmptyNil⟩
  · rw [hIntroEq]
    exact eo_list_rev_str_concat_nil_eq_of_nil_true x hXNil
  · rw [hIntroEq]
    exact eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck x empty
      hEmptyNil (by simpa [hIntroEq] using hRevIntro)

theorem eo_list_rev_list_rev_str_nary_intro_eq_of_not_str_concat
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x)) =
      __str_nary_intro x := by
  have hRevEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat x hNotConcat hIntro
      hRevIntro
  rw [hRevEq]
  exact hRevEq

theorem eo_interprets_double_rev_intro_elim_eq_of_not_str_concat_smt
    (M : SmtModel) (x : Term)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  have hRevRevEq :=
    eo_list_rev_list_rev_str_nary_intro_eq_of_not_str_concat x
      hNotConcat hIntro hRevIntro
  have hElimIntroEq :
      __str_nary_elim (__str_nary_intro x) = x :=
    str_nary_elim_str_nary_intro_eq_of_not_str_concat x hNotConcat
      hIntro
  rw [hRevRevEq]
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__str_nary_intro x))
        (__str_nary_elim (__str_nary_intro x))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · simpa [hElimIntroEq] using hxNN
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim (__str_nary_intro x))
    (__str_nary_elim (__str_nary_intro x)) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M
        (__eo_to_smt (__str_nary_elim (__str_nary_intro x)))))

theorem eo_interprets_double_rev_intro_elim_eq_of_not_str_concat
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  exact eo_interprets_double_rev_intro_elim_eq_of_not_str_concat_smt M x
    hxNN hNotConcat hIntro hRevIntro

theorem eo_interprets_double_rev_intro_elim_eq_of_seq_cases
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, hX⟩
    subst x
    exact eo_interprets_double_rev_intro_elim_eq_of_str_concat M head
      tail T hxTy hRevIntro
  · exact eo_interprets_double_rev_intro_elim_eq_of_not_str_concat M x T
      hxTy hIntroNN hIntro hRevIntro hConcat

theorem eo_interprets_double_rev_intro_elim_eq_of_str_concat_nil
    (M : SmtModel) (head nil : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_nary_intro (mkConcat head nil)) ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro (mkConcat head nil)))))
        (__str_nary_elim (__str_nary_intro (mkConcat head nil)))) true := by
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  exact eo_interprets_double_rev_intro_elim_eq_of_str_concat M head nil T
    hConsTy hRevIntro

theorem eo_interprets_double_rev_intro_self_of_elim_intro
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hElimIntro : __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck)
    (hDoubleToIntro :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro x))))
          (__str_nary_elim (__str_nary_intro x))) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        x) true := by
  exact RuleProofs.eo_interprets_eq_trans M
    (__str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x))))
    (__str_nary_elim (__str_nary_intro x)) x hDoubleToIntro
    (eo_interprets_str_nary_elim_intro_eq_of_seq M hM x T hxTy
      hIntroNN hIntro hElimIntro)

theorem eo_interprets_double_rev_intros_of_elim_intros
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hElimIntroS : __str_nary_elim (__str_nary_intro s) ≠ Term.Stuck)
    (hElimIntroT : __str_nary_elim (__str_nary_intro t) ≠ Term.Stuck)
    (hDoubleS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim (__str_nary_intro s))) true)
    (hDoubleT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim (__str_nary_intro t))) true)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  have hSelfS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          s) true :=
    eo_interprets_double_rev_intro_self_of_elim_intro M hM s T hsTy
      hIntroSNN hIntroS hElimIntroS hDoubleS
  have hSelfT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          t) true :=
    eo_interprets_double_rev_intro_self_of_elim_intro M hM t T htTy
      hIntroTNN hIntroT hElimIntroT hDoubleT
  exact eo_interprets_double_rev_intros_of_self M s t hSelfS hSelfT hST


theorem str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) =
      mkPair (__str_nary_intro s) (__str_nary_intro t) := by
  rcases str_nary_intro_not_str_concat_cases s hSNotConcat hIntroS with
    hIntroSEq | ⟨emptyS, hIntroSEq, hEmptySNil⟩
  · rw [hIntroSEq]
    exact str_strip_prefix_left_not_str_concat s (__str_nary_intro t)
      (str_nary_intro_arg_ne_stuck_of_ne_stuck s hIntroS)
      hIntroT hSNotConcat
  · rcases str_nary_intro_not_str_concat_cases t hTNotConcat hIntroT with
      hIntroTEq | ⟨emptyT, hIntroTEq, hEmptyTNil⟩
    · rw [hIntroSEq, hIntroTEq]
      exact str_strip_prefix_right_not_str_concat (mkConcat s emptyS) t
        (by simp [mkConcat])
        (str_nary_intro_arg_ne_stuck_of_ne_stuck t hIntroT)
        hTNotConcat
    · rw [hIntroSEq, hIntroTEq]
      exact str_strip_prefix_concat_of_eo_eq_false s t emptyS emptyT
        hHead


theorem eo_interprets_str_concat_right_cancel
    (M : SmtModel) (hM : model_wf M) (x y z : Term) :
    eo_interprets M (mkEq (mkConcat y x) (mkConcat z x)) true ->
    eo_interprets M (mkEq y z) true := by
  intro h
  have hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat y x) (mkConcat z x)) :=
    RuleProofs.eo_has_bool_type_of_interprets_true M _ h
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat y x) (mkConcat z x) hBool with ⟨hSame, hLeftNN⟩
  rcases str_concat_args_of_non_none y x hLeftNN with ⟨T, hyTy, hxTy⟩
  have hRightNN : __smtx_typeof (__eo_to_smt (mkConcat z x)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases str_concat_args_of_non_none z x hRightNN with ⟨U, hzTyU, hxTyU⟩
  have hUT : U = T := by
    have hSeq : SmtType.Seq T = SmtType.Seq U := by
      rw [← hxTy, ← hxTyU]
    injection hSeq with hTU
    exact hTU.symm
  have hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    simpa [hUT] using hzTyU
  have hRel := RuleProofs.eo_interprets_eq_rel M (mkConcat y x) (mkConcat z x) h
  have hTailRel := smt_value_rel_str_concat_right_cancel M hM x y z T hxTy hyTy hzTy hRel
  have hYZBool : RuleProofs.eo_has_bool_type (mkEq y z) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hyTy, hzTy]
    · rw [hyTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M y z hYZBool hTailRel

theorem eo_interprets_str_concat_heads_of_tail_eo_eq_true
    (M : SmtModel) (hM : model_wf M) (t u t2 s2 : Term)
    (hTail : __eo_eq t u = Term.Boolean true) :
    eo_interprets M (mkEq (mkConcat t2 t) (mkConcat s2 u)) true ->
    eo_interprets M (mkEq t2 s2) true := by
  intro h
  have hUT : u = t := eq_of_eo_eq_true_local t u hTail
  subst u
  exact eo_interprets_str_concat_right_cancel M hM t t2 s2 h

theorem eo_interprets_rev_tails_of_head_eo_eq_true
    (M : SmtModel) (hM : model_wf M) (t u t2 s2 : Term)
    (hHead : __eo_eq t u = Term.Boolean true) :
    eo_interprets M
      (mkEq
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2)) t)
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) u))
      true ->
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  exact eo_interprets_str_concat_heads_of_tail_eo_eq_true M hM t u
    (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
    (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) hHead

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_snoc
    (M : SmtModel) (hM : model_wf M) (t u t2 s2 : Term)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftSnoc :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            t)) true)
    (hRightSnoc :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2)))
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))
            u)) true)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  let left :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2))
  let right :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))
  let leftSnoc :=
    mkConcat
      (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2)) t
  let rightSnoc :=
    mkConcat
      (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) u
  have hLeftSymm : eo_interprets M (mkEq leftSnoc left) true :=
    eo_interprets_eq_symm_local M left leftSnoc hLeftSnoc
  have hLeftRight : eo_interprets M (mkEq leftSnoc right) true :=
    RuleProofs.eo_interprets_eq_trans M leftSnoc left right hLeftSymm hXY
  have hSnocEq : eo_interprets M (mkEq leftSnoc rightSnoc) true :=
    RuleProofs.eo_interprets_eq_trans M leftSnoc right rightSnoc
      hLeftRight hRightSnoc
  exact eo_interprets_rev_tails_of_head_eo_eq_true M hM t u t2 s2 hHead
    hSnocEq

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_seq
    (M : SmtModel) (hM : model_wf M)
    (t u t2 s2 : Term) (T : SmtType)
    (hHead : __eo_eq t u = Term.Boolean true)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (huTy : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T)
    (ht2List :
      __eo_is_list (Term.UOp UserOp.str_concat) t2 = Term.Boolean true)
    (hs2List :
      __eo_is_list (Term.UOp UserOp.str_concat) s2 = Term.Boolean true)
    (ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T)
    (hRevLeft :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2) ≠
        Term.Stuck)
    (hRevRight :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2) ≠
        Term.Stuck)
    (hRevTailLeft :
      __eo_list_rev (Term.UOp UserOp.str_concat) t2 ≠ Term.Stuck)
    (hRevTailRight :
      __eo_list_rev (Term.UOp UserOp.str_concat) s2 ≠ Term.Stuck)
    (hElimLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)) ≠
        Term.Stuck)
    (hElimRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2)) ≠
        Term.Stuck)
    (hElimTailLeft :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2) ≠
        Term.Stuck)
    (hElimTailRight :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2) ≠
        Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  have hLeftSnoc :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            t)) true :=
    eo_interprets_rev_cons_snoc_of_seq M hM t t2 T htTy ht2List
      ht2Ty hRevLeft hRevTailLeft hElimLeft hElimTailLeft
  have hRightSnoc :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2)))
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))
            u)) true :=
    eo_interprets_rev_cons_snoc_of_seq M hM u s2 T huTy hs2List
      hs2Ty hRevRight hRevTailRight hElimRight hElimTailRight
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_snoc M hM
    t u t2 s2 hHead hLeftSnoc hRightSnoc hXY

theorem rev_elim_cons_operands_ne_stuck_of_interprets
    (M : SmtModel) (t u t2 s2 : Term)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)) ≠
      Term.Stuck ∧
    __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2)) ≠
      Term.Stuck ∧
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2) ≠
      Term.Stuck ∧
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2) ≠
      Term.Stuck := by
  let left :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2))
  let right :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))
  have hBool : RuleProofs.eo_has_bool_type (mkEq left right) := by
    simpa [left, right] using
      RuleProofs.eo_has_bool_type_of_interprets_true M _ hXY
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type left right
      hBool with ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt right) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  have hLeft : left ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation left hLeftNN
  have hRight : right ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation right hRightNN
  have hRevLeft :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2) ≠
        Term.Stuck := by
    simpa [left] using
      str_nary_elim_arg_ne_stuck_of_ne_stuck
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2))
        hLeft
  have hRevRight :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2) ≠
        Term.Stuck := by
    simpa [right] using
      str_nary_elim_arg_ne_stuck_of_ne_stuck
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))
        hRight
  exact ⟨by simpa [left] using hLeft, by simpa [right] using hRight,
    hRevLeft, hRevRight⟩

theorem rev_elim_cons_tail_lists_of_interprets
    (M : SmtModel) (t u t2 s2 : Term)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    __eo_is_list (Term.UOp UserOp.str_concat) t2 = Term.Boolean true ∧
    __eo_is_list (Term.UOp UserOp.str_concat) s2 = Term.Boolean true ∧
    __eo_list_rev (Term.UOp UserOp.str_concat) t2 ≠ Term.Stuck ∧
    __eo_list_rev (Term.UOp UserOp.str_concat) s2 ≠ Term.Stuck := by
  rcases rev_elim_cons_operands_ne_stuck_of_interprets M t u t2 s2 hXY with
    ⟨_, _, hRevLeft, hRevRight⟩
  have ht2List :
      __eo_is_list (Term.UOp UserOp.str_concat) t2 = Term.Boolean true :=
    eo_list_rev_cons_tail_list_of_ne_stuck
      (Term.UOp UserOp.str_concat) t t2 hRevLeft
  have hs2List :
      __eo_is_list (Term.UOp UserOp.str_concat) s2 = Term.Boolean true :=
    eo_list_rev_cons_tail_list_of_ne_stuck
      (Term.UOp UserOp.str_concat) u s2 hRevRight
  exact ⟨ht2List, hs2List,
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat) t2
      ht2List,
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat) s2
      hs2List⟩

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq
    (M : SmtModel) (hM : model_wf M)
    (t u t2 s2 : Term) (T : SmtType)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hElimTailLeft :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2) ≠
        Term.Stuck)
    (hElimTailRight :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2) ≠
        Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  rcases str_concat_args_of_seq_type t t2 T hLeftTy with
    ⟨htTy, ht2Ty⟩
  rcases str_concat_args_of_seq_type u s2 T hRightTy with
    ⟨huTy, hs2Ty⟩
  rcases rev_elim_cons_operands_ne_stuck_of_interprets M t u t2 s2 hXY with
    ⟨hElimLeft, hElimRight, hRevLeft, hRevRight⟩
  rcases rev_elim_cons_tail_lists_of_interprets M t u t2 s2 hXY with
    ⟨ht2List, hs2List, hRevTailLeft, hRevTailRight⟩
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_seq M hM
    t u t2 s2 T hHead htTy huTy ht2List hs2List ht2Ty hs2Ty
    hRevLeft hRevRight hRevTailLeft hRevTailRight hElimLeft hElimRight
    hElimTailLeft hElimTailRight hXY

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip
    (M : SmtModel) (hM : model_wf M)
    (t u t2 s2 : Term) (T : SmtType)
    (_hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hElimTailLeft :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2) ≠
        Term.Stuck)
    (hElimTailRight :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2) ≠
        Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq M hM
    t u t2 s2 T hHead hLeftTy hRightTy hElimTailLeft
    hElimTailRight hXY

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_pair
    (M : SmtModel) (hM : model_wf M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hTailStrip : __str_strip_prefix t2 s2 = mkPair t2 s2)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  have hElimTailLeft :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2) ≠
        Term.Stuck := by
    simpa [hTailStrip, mkPair, pair_first_pair] using hFinalLeft
  have hElimTailRight :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2) ≠
        Term.Stuck := by
    simpa [hTailStrip, mkPair, pair_second_pair] using hFinalRight
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip M hM
    t u t2 s2 T hStrip hHead hLeftTy hRightTy hElimTailLeft
    hElimTailRight hXY

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_false
    (M : SmtModel) (hM : model_wf M)
    (t u a aTail b bTail : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t (mkConcat a aTail))
          (mkConcat u (mkConcat b bTail)) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t (mkConcat a aTail))) =
        SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u (mkConcat b bTail))) =
        SmtType.Seq T)
    (hTailHead : __eo_eq a b = Term.Boolean false)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first
              (__str_strip_prefix (mkConcat a aTail) (mkConcat b bTail)))) ≠
        Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second
              (__str_strip_prefix (mkConcat a aTail) (mkConcat b bTail)))) ≠
        Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat t (mkConcat a aTail))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat u (mkConcat b bTail)))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat a aTail)))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat b bTail))))
      true := by
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_pair
    M hM t u (mkConcat a aTail) (mkConcat b bTail) T hStrip hHead
    hLeftTy hRightTy
    (str_strip_prefix_concat_of_eo_eq_false a b aTail bTail hTailHead)
    hFinalLeft hFinalRight hXY

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_left_not_concat
    (M : SmtModel) (hM : model_wf M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hT2NotConcat : ¬ ∃ head tail : Term, t2 = mkConcat head tail)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  have hTailStrip : __str_strip_prefix t2 s2 ≠ Term.Stuck :=
    str_strip_prefix_tail_ne_stuck_of_concat_eo_eq_true t u t2 s2
      hStrip hHead
  have ht2 : t2 ≠ Term.Stuck :=
    str_strip_prefix_left_ne_stuck_of_ne_stuck t2 s2 hTailStrip
  have hs2 : s2 ≠ Term.Stuck :=
    str_strip_prefix_right_ne_stuck_of_ne_stuck t2 s2 hTailStrip
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_pair
    M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy
    (str_strip_prefix_left_not_str_concat t2 s2 ht2 hs2 hT2NotConcat)
    hFinalLeft hFinalRight hXY

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_right_not_concat
    (M : SmtModel) (hM : model_wf M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hS2NotConcat : ¬ ∃ head tail : Term, s2 = mkConcat head tail)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  have hTailStrip : __str_strip_prefix t2 s2 ≠ Term.Stuck :=
    str_strip_prefix_tail_ne_stuck_of_concat_eo_eq_true t u t2 s2
      hStrip hHead
  have ht2 : t2 ≠ Term.Stuck :=
    str_strip_prefix_left_ne_stuck_of_ne_stuck t2 s2 hTailStrip
  have hs2 : s2 ≠ Term.Stuck :=
    str_strip_prefix_right_ne_stuck_of_ne_stuck t2 s2 hTailStrip
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_pair
    M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy
    (str_strip_prefix_right_not_str_concat t2 s2 ht2 hs2 hS2NotConcat)
    hFinalLeft hFinalRight hXY

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_stop
    (M : SmtModel) (hM : model_wf M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hTailStop :
      (¬ ∃ head tail : Term, t2 = mkConcat head tail) ∨
        (¬ ∃ head tail : Term, s2 = mkConcat head tail) ∨
        ∃ a aTail b bTail : Term,
          t2 = mkConcat a aTail ∧
          s2 = mkConcat b bTail ∧
          __eo_eq a b = Term.Boolean false)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  rcases hTailStop with hT2NotConcat | hTailStop
  · exact
      eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_left_not_concat
        M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy
        hT2NotConcat hFinalLeft hFinalRight hXY
  rcases hTailStop with hS2NotConcat | hTailFalse
  · exact
      eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_right_not_concat
        M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy
        hS2NotConcat hFinalLeft hFinalRight hXY
  rcases hTailFalse with
    ⟨a, aTail, b, bTail, hT2, hS2, hTailHead⟩
  subst t2
  subst s2
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_false
    M hM t u a aTail b bTail T hStrip hHead hLeftTy hRightTy
    hTailHead hFinalLeft hFinalRight hXY

theorem concat_tail_stop_or_head_true_of_seq_type
    (t2 s2 : Term) (T : SmtType)
    (ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T) :
    ((¬ ∃ head tail : Term, t2 = mkConcat head tail) ∨
      (¬ ∃ head tail : Term, s2 = mkConcat head tail) ∨
      ∃ a aTail b bTail : Term,
        t2 = mkConcat a aTail ∧
        s2 = mkConcat b bTail ∧
        __eo_eq a b = Term.Boolean false) ∨
      ∃ a aTail b bTail : Term,
        t2 = mkConcat a aTail ∧
        s2 = mkConcat b bTail ∧
        __eo_eq a b = Term.Boolean true := by
  by_cases hT2Concat : ∃ head tail : Term, t2 = mkConcat head tail
  · rcases hT2Concat with ⟨a, aTail, hT2⟩
    by_cases hS2Concat : ∃ head tail : Term, s2 = mkConcat head tail
    · rcases hS2Concat with ⟨b, bTail, hS2⟩
      subst t2
      subst s2
      rcases str_concat_args_of_seq_type a aTail T ht2Ty with
        ⟨haTy, _haTailTy⟩
      rcases str_concat_args_of_seq_type b bTail T hs2Ty with
        ⟨hbTy, _hbTailTy⟩
      rcases eo_eq_cases_of_ne_stuck a b
          (term_ne_stuck_of_smt_type_seq a T haTy)
          (term_ne_stuck_of_smt_type_seq b T hbTy) with
        hHead | hHead
      · exact Or.inr ⟨a, aTail, b, bTail, rfl, rfl, hHead⟩
      · exact Or.inl (Or.inr (Or.inr
          ⟨a, aTail, b, bTail, rfl, rfl, hHead⟩))
    · exact Or.inl (Or.inr (Or.inl hS2Concat))
  · exact Or.inl (Or.inl hT2Concat)

theorem concat_tail_stop_of_no_head_true_of_seq_type
    (t2 s2 : Term) (T : SmtType)
    (ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T)
    (hNoHeadTrue :
      ¬ ∃ a aTail b bTail : Term,
        t2 = mkConcat a aTail ∧
        s2 = mkConcat b bTail ∧
        __eo_eq a b = Term.Boolean true) :
    (¬ ∃ head tail : Term, t2 = mkConcat head tail) ∨
      (¬ ∃ head tail : Term, s2 = mkConcat head tail) ∨
      ∃ a aTail b bTail : Term,
        t2 = mkConcat a aTail ∧
        s2 = mkConcat b bTail ∧
        __eo_eq a b = Term.Boolean false := by
  rcases concat_tail_stop_or_head_true_of_seq_type t2 s2 T ht2Ty hs2Ty with
    hStop | hHeadTrue
  · exact hStop
  · exact False.elim (hNoHeadTrue hHeadTrue)

theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_with_final
    (M : SmtModel) (hM : model_wf M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  rcases str_concat_args_of_seq_type t t2 T hLeftTy with
    ⟨_htTy, ht2Ty⟩
  rcases str_concat_args_of_seq_type u s2 T hRightTy with
    ⟨_huTy, hs2Ty⟩
  rcases concat_tail_stop_or_head_true_of_seq_type t2 s2 T ht2Ty hs2Ty with
    hTailStop | hTailHeadTrue
  · exact
      eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_stop
        M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy hTailStop
        hFinalLeft hFinalRight hXY
  · rcases hTailHeadTrue with
      ⟨a, aTail, b, bTail, hT2, hS2, _hTailHead⟩
    subst t2
    subst s2
    rcases rev_elim_cons_tail_lists_of_interprets
        M t u (mkConcat a aTail) (mkConcat b bTail) hXY with
      ⟨_hTailLeftList, _hTailRightList, hRevTailLeft,
        hRevTailRight⟩
    have hElimTailLeft :
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat a aTail)) ≠ Term.Stuck :=
      str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq a aTail T
        ht2Ty hRevTailLeft
    have hElimTailRight :
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat b bTail)) ≠ Term.Stuck :=
      str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq b bTail T
        hs2Ty hRevTailRight
    exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip
      M hM t u (mkConcat a aTail) (mkConcat b bTail) T hStrip hHead
      hLeftTy hRightTy hElimTailLeft hElimTailRight hXY


theorem eo_typeof_eq_operands_same_of_bool (x y : Term)
    (hTy : __eo_typeof (mkEq x y) = Term.Bool) :
    __eo_typeof x = __eo_typeof y ∧
      __eo_typeof x ≠ Term.Stuck ∧
      __eo_typeof y ≠ Term.Stuck := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at hTy
  by_cases hx : __eo_typeof x = Term.Stuck
  · simp [hx, __eo_typeof_eq] at hTy
  by_cases hy : __eo_typeof y = Term.Stuck
  · simp [hy, __eo_typeof_eq] at hTy
  have hReq :
      __eo_requires (__eo_eq (__eo_typeof x) (__eo_typeof y))
        (Term.Boolean true) Term.Bool = Term.Bool := by
    simpa [hx, hy, __eo_typeof_eq] using hTy
  have hReqNonStuck :
      __eo_requires (__eo_eq (__eo_typeof x) (__eo_typeof y))
        (Term.Boolean true) Term.Bool ≠ Term.Stuck := by
    rw [hReq]
    intro h
    cases h
  have hEq :
      __eo_eq (__eo_typeof x) (__eo_typeof y) = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_eq (__eo_typeof x) (__eo_typeof y))
      (Term.Boolean true) Term.Bool hReqNonStuck
  have hSame : __eo_typeof x = __eo_typeof y :=
    (eq_of_eo_eq_true_local (__eo_typeof x) (__eo_typeof y) hEq).symm
  exact ⟨hSame, hx, hy⟩

/-- Bridge lemma: a Seq type is well-formed precisely when its element type's
    well-formedness component holds (the Seq inhabitation check is
    unconditional). -/
theorem type_wf_seq_of_component (A : SmtType)
    (h : __smtx_type_wf_component A = true) :
    __smtx_type_wf (SmtType.Seq A) = true := by
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_inhabited_type_seq, SmtEval.native_and] at h ⊢
  exact h
