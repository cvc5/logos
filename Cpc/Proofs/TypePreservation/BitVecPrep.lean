module

public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.SmtModel
import all Cpc.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Lemma about `typeof_concat_eq`. -/
theorem typeof_concat_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.concat t1 t2) =
      __smtx_typeof_concat (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_extract_eq`. -/
theorem typeof_extract_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.extract t1 t2 t3) =
      __smtx_typeof_extract t1 t2 (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_repeat_eq`. -/
theorem typeof_repeat_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.repeat t1 t2) =
      __smtx_typeof_repeat t1 (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_zero_extend_eq`. -/
theorem typeof_zero_extend_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.zero_extend t1 t2) =
      __smtx_typeof_zero_extend t1 (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_sign_extend_eq`. -/
theorem typeof_sign_extend_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.sign_extend t1 t2) =
      __smtx_typeof_sign_extend t1 (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_rotate_left_eq`. -/
theorem typeof_rotate_left_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.rotate_left t1 t2) =
      __smtx_typeof_rotate_left t1 (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_rotate_right_eq`. -/
theorem typeof_rotate_right_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.rotate_right t1 t2) =
      __smtx_typeof_rotate_right t1 (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_int_to_bv_eq`. -/
theorem typeof_int_to_bv_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.int_to_bv t1 t2) =
      __smtx_typeof_int_to_bv t1 (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Derives `bv_concat_args` from `non_none`. -/
theorem bv_concat_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.concat t1 t2)) :
    ∃ w1 w2 : native_Nat,
      __smtx_typeof t1 = SmtType.BitVec w1 ∧
        __smtx_typeof t2 = SmtType.BitVec w2 := by
  have ht' : __smtx_typeof_concat (__smtx_typeof t1) (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_concat_eq t1 t2]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          exact ⟨w1, w2, rfl, rfl⟩
      | _ =>
          simp [__smtx_typeof_concat, h1, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_concat, h1, h2] at ht'

/-- Derives `extract_args` from `non_none`. -/
theorem extract_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type
      (SmtTerm.extract t1 t2 t3)) :
    ∃ i j : native_Int, ∃ w : native_Nat,
      t1 = SmtTerm.Numeral i ∧
        t2 = SmtTerm.Numeral j ∧
        __smtx_typeof t3 = SmtType.BitVec w ∧
        native_zleq 0 j = true ∧
        native_zlt 0 (native_zplus (native_zplus i 1) (native_zneg j)) = true ∧
        native_zlt i (native_nat_to_int w) = true := by
  have ht' : __smtx_typeof_extract t1 t2 (__smtx_typeof t3) ≠ SmtType.None := by
    rw [← typeof_extract_eq t1 t2 t3]
    exact ht
  cases t1 with
  | Numeral i =>
      cases t2 with
      | Numeral j =>
          cases h3 : __smtx_typeof t3 with
          | BitVec w =>
              by_cases hj0 : native_zleq 0 j = true
              · by_cases hiw : native_zlt i (native_nat_to_int w) = true
                · by_cases hwidth :
                    native_zlt 0 (native_zplus (native_zplus i 1) (native_zneg j)) = true
                  · exact ⟨i, j, w, rfl, rfl, rfl, hj0, hwidth, hiw⟩
                  · exfalso
                    exact ht' (by
                      simp [__smtx_typeof_extract, native_ite, h3, hj0, hiw, hwidth])
                · exfalso
                  exact ht' (by
                    simp [__smtx_typeof_extract, native_ite, h3, hj0, hiw])
              · exfalso
                exact ht' (by
                  simp [__smtx_typeof_extract, native_ite, h3, hj0])
          | _ =>
              simp [__smtx_typeof_extract, h3] at ht'
      | _ =>
          simp [__smtx_typeof_extract] at ht'
  | _ =>
      simp [__smtx_typeof_extract] at ht'

/-- Derives `repeat_args` from `non_none`. -/
theorem repeat_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.repeat t1 t2)) :
    ∃ i : native_Int, ∃ w : native_Nat,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        native_zleq 1 i = true := by
  have ht' : __smtx_typeof_repeat t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_repeat_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi1 : native_zleq 1 i = true
          · exact ⟨i, w, rfl, rfl, hi1⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_repeat, native_ite, h2, hi1])
      | _ =>
          simp [__smtx_typeof_repeat, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_repeat] at ht'

/-- Derives `zero_extend_args` from `non_none`. -/
theorem zero_extend_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.zero_extend t1 t2)) :
    ∃ i : native_Int, ∃ w : native_Nat,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        native_zleq 0 i = true := by
  have ht' : __smtx_typeof_zero_extend t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_zero_extend_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi0 : native_zleq 0 i = true
          · exact ⟨i, w, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_zero_extend, native_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_zero_extend, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_zero_extend] at ht'

/-- Derives `sign_extend_args` from `non_none`. -/
theorem sign_extend_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.sign_extend t1 t2)) :
    ∃ i : native_Int, ∃ w : native_Nat,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        native_zleq 0 i = true := by
  have ht' : __smtx_typeof_sign_extend t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_sign_extend_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi0 : native_zleq 0 i = true
          · exact ⟨i, w, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_sign_extend, native_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_sign_extend, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_sign_extend] at ht'

/-- Derives `rotate_left_args` from `non_none`. -/
theorem rotate_left_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.rotate_left t1 t2)) :
    ∃ i : native_Int, ∃ w : native_Nat,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        native_zleq 0 i = true := by
  have ht' : __smtx_typeof_rotate_left t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_rotate_left_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi0 : native_zleq 0 i = true
          · exact ⟨i, w, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_rotate_left, native_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_rotate_left, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_rotate_left] at ht'

/-- Derives `rotate_right_args` from `non_none`. -/
theorem rotate_right_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.rotate_right t1 t2)) :
    ∃ i : native_Int, ∃ w : native_Nat,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        native_zleq 0 i = true := by
  have ht' : __smtx_typeof_rotate_right t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_rotate_right_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi0 : native_zleq 0 i = true
          · exact ⟨i, w, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_rotate_right, native_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_rotate_right, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_rotate_right] at ht'

/-- Derives `int_to_bv_args` from `non_none`. -/
theorem int_to_bv_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.int_to_bv t1 t2)) :
    ∃ i : native_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.Int ∧
        native_zleq 0 i = true := by
  have ht' : __smtx_typeof_int_to_bv t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_int_to_bv_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | Int =>
          by_cases hi0 : native_zleq 0 i = true
          · exact ⟨i, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_int_to_bv, native_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_int_to_bv, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_int_to_bv] at ht'

/-- Derives `bv_unop_arg` from `non_none`. -/
theorem bv_unop_arg_of_non_none
    {op : SmtTerm -> SmtTerm} {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_bv_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t)) :
    ∃ w : native_Nat, __smtx_typeof t = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | BitVec w =>
      exact ⟨w, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_bv_op_1, h] at ht

/-- Derives `bv_unop_ret_arg` from `non_none`. -/
theorem bv_unop_ret_arg_of_non_none
    {op : SmtTerm -> SmtTerm} {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_bv_op_1_ret (__smtx_typeof t) ret)
    (ht : term_has_non_none_type (op t)) :
    ∃ w : native_Nat, __smtx_typeof t = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | BitVec w =>
      exact ⟨w, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_bv_op_1_ret, h] at ht

/-- Derives `bv_binop_args` from `non_none`. -/
theorem bv_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    ∃ w : native_Nat,
      __smtx_typeof t1 = SmtType.BitVec w ∧
        __smtx_typeof t2 = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          by_cases hEq : native_nateq w1 w2 = true
          · have hw : w1 = w2 := by
              simpa [native_nateq, Smtm.native_nateq] using hEq
            cases hw
            exact ⟨w1, rfl, rfl⟩
          · exfalso
            exact ht (by
              simp [hTy, __smtx_typeof_bv_op_2, native_ite, h1, h2, hEq])
      | _ =>
          simp [hTy, __smtx_typeof_bv_op_2, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_bv_op_2, h1, h2] at ht

/-- Derives `bv_binop_ret_args` from `non_none`. -/
theorem bv_binop_ret_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (op t1 t2)) :
    ∃ w : native_Nat,
      __smtx_typeof t1 = SmtType.BitVec w ∧
        __smtx_typeof t2 = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          by_cases hEq : native_nateq w1 w2 = true
          · have hw : w1 = w2 := by
              simpa [native_nateq, Smtm.native_nateq] using hEq
            cases hw
            exact ⟨w1, rfl, rfl⟩
          · exfalso
            exact ht (by
              simp [hTy, __smtx_typeof_bv_op_2_ret, native_ite, h1, h2, hEq])
      | _ =>
          simp [hTy, __smtx_typeof_bv_op_2_ret, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_bv_op_2_ret, h1, h2] at ht


end Smtm
