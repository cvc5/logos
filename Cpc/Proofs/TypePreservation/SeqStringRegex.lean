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

/-- Lemma about `typeof_str_len_eq`. -/
theorem typeof_str_len_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_len t) =
      __smtx_typeof_seq_op_1_ret (__smtx_typeof t) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_concat_eq`. -/
theorem typeof_str_concat_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_concat t1 t2) =
      __smtx_typeof_seq_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_substr_eq`. -/
theorem typeof_str_substr_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_substr t1 t2 t3) =
      __smtx_typeof_str_substr (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_contains_eq`. -/
theorem typeof_str_contains_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_contains t1 t2) =
      __smtx_typeof_seq_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_replace_eq`. -/
theorem typeof_str_replace_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_replace t1 t2 t3) =
      __smtx_typeof_seq_op_3 (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_indexof_eq`. -/
theorem typeof_str_indexof_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_indexof t1 t2 t3) =
      __smtx_typeof_str_indexof (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_at_eq`. -/
theorem typeof_str_at_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_at t1 t2) =
      __smtx_typeof_str_at (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_prefixof_eq`. -/
theorem typeof_str_prefixof_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_prefixof t1 t2) =
      __smtx_typeof_seq_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_suffixof_eq`. -/
theorem typeof_str_suffixof_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_suffixof t1 t2) =
      __smtx_typeof_seq_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_rev_eq`. -/
theorem typeof_str_rev_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_rev t) =
      __smtx_typeof_seq_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_update_eq`. -/
theorem typeof_str_update_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_update t1 t2 t3) =
      __smtx_typeof_str_update (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_to_lower_eq`. -/
theorem typeof_str_to_lower_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_to_lower t) =
      native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char))
        (SmtType.Seq SmtType.Char)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_to_upper_eq`. -/
theorem typeof_str_to_upper_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_to_upper t) =
      native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char))
        (SmtType.Seq SmtType.Char)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_to_code_eq`. -/
theorem typeof_str_to_code_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_to_code t) =
      native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) SmtType.Int
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_from_code_eq`. -/
theorem typeof_str_from_code_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_from_code t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) (SmtType.Seq SmtType.Char)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_is_digit_eq`. -/
theorem typeof_str_is_digit_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_is_digit t) =
      native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) SmtType.Bool
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_to_int_eq`. -/
theorem typeof_str_to_int_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_to_int t) =
      native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) SmtType.Int
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_from_int_eq`. -/
theorem typeof_str_from_int_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_from_int t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) (SmtType.Seq SmtType.Char)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_lt_eq`. -/
theorem typeof_str_lt_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_lt t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char)) SmtType.Bool
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_leq_eq`. -/
theorem typeof_str_leq_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_leq t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char)) SmtType.Bool
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_replace_all_eq`. -/
theorem typeof_str_replace_all_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_replace_all t1 t2 t3) =
      __smtx_typeof_seq_op_3 (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_replace_re_eq`. -/
theorem typeof_str_replace_re_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_replace_re t1 t2 t3) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t3) (SmtType.Seq SmtType.Char))
            (SmtType.Seq SmtType.Char) SmtType.None)
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_replace_re_all_eq`. -/
theorem typeof_str_replace_re_all_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_replace_re_all t1 t2 t3) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t3) (SmtType.Seq SmtType.Char))
            (SmtType.Seq SmtType.Char) SmtType.None)
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_indexof_re_eq`. -/
theorem typeof_str_indexof_re_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_indexof_re t1 t2 t3) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t3) SmtType.Int) SmtType.Int
            SmtType.None)
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_indexof_re_split_eq`. -/
theorem typeof_str_indexof_re_split_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_indexof_re_split t1 t2 t3) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t3) SmtType.RegLan) SmtType.Int
            SmtType.None)
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_to_re_eq`. -/
theorem typeof_str_to_re_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.str_to_re t) =
      native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) SmtType.RegLan
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_mult_eq`. -/
theorem typeof_re_mult_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.re_mult t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_plus_eq`. -/
theorem typeof_re_plus_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.re_plus t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_exp_eq`. -/
theorem typeof_re_exp_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.re_exp t1 t2) =
      __smtx_typeof_re_exp t1 (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_opt_eq`. -/
theorem typeof_re_opt_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.re_opt t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_comp_eq`. -/
theorem typeof_re_comp_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.re_comp t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_range_eq`. -/
theorem typeof_re_range_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.re_range t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char))
          SmtType.RegLan
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_concat_eq`. -/
theorem typeof_re_concat_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.re_concat t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.RegLan)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_inter_eq`. -/
theorem typeof_re_inter_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.re_inter t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.RegLan)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_union_eq`. -/
theorem typeof_re_union_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.re_union t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.RegLan)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_diff_eq`. -/
theorem typeof_re_diff_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.re_diff t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.RegLan)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_re_loop_eq`. -/
theorem typeof_re_loop_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.re_loop t1 t2 t3) =
      __smtx_typeof_re_loop t1 t2 (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_str_in_re_eq`. -/
theorem typeof_str_in_re_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.str_in_re t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) SmtType.Bool
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Lemma about `typeof_seq_nth_eq`. -/
theorem typeof_seq_nth_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_nth t1 t2) =
      __smtx_typeof_seq_nth (__smtx_typeof t1) (__smtx_typeof t2) := by
  rw [__smtx_typeof.eq_def] <;> simp only
/-- Derives `seq_arg` from `non_none`. -/
theorem seq_arg_of_non_none
    {op : SmtTerm -> SmtTerm} {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_seq_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t)) :
    ∃ T : SmtType, __smtx_typeof t = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | Seq T =>
      exact ⟨T, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_seq_op_1, h] at ht

/-- Derives `seq_arg` from `non_none` for `seq_op_1_ret`. -/
theorem seq_arg_of_non_none_ret
    {op : SmtTerm -> SmtTerm} {t : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_seq_op_1_ret (__smtx_typeof t) R)
    (ht : term_has_non_none_type (op t)) :
    ∃ T : SmtType, __smtx_typeof t = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | Seq T =>
      exact ⟨T, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_seq_op_1_ret, h] at ht

/-- Derives `seq_binop_args` from `non_none`. -/
theorem seq_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_seq_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧ __smtx_typeof t2 = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          have hEq : T = U := by
            simpa [hTy, __smtx_typeof_seq_op_2, native_ite, native_Teq, h1, h2] using ht
          subst hEq
          exact ⟨T, rfl, rfl⟩
      | _ =>
          simp [hTy, __smtx_typeof_seq_op_2, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_seq_op_2, h1, h2] at ht

/-- Derives `seq_binop_args` from `non_none` for `seq_op_2_ret`. -/
theorem seq_binop_args_of_non_none_ret
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_seq_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) R)
    (ht : term_has_non_none_type (op t1 t2)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧ __smtx_typeof t2 = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          have hEq : T = U := by
            have hSeqs : T = U ∧ ¬ R = SmtType.None := by
              simpa [hTy, __smtx_typeof_seq_op_2_ret, native_ite, native_Teq, h1, h2] using ht
            exact hSeqs.1
          subst hEq
          exact ⟨T, rfl, rfl⟩
      | _ =>
          simp [hTy, __smtx_typeof_seq_op_2_ret, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_seq_op_2_ret, h1, h2] at ht

/-- Derives `seq_triop_args` from `non_none`. -/
theorem seq_triop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2 t3) =
        __smtx_typeof_seq_op_3 (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3))
    (ht :
      term_has_non_none_type (op t1 t2 t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Seq T ∧
        __smtx_typeof t3 = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          cases h3 : __smtx_typeof t3 with
          | Seq V =>
              have hEq :
                  T = U ∧ U = V := by
                simpa [hTy, __smtx_typeof_seq_op_3, native_ite, native_Teq, h1, h2, h3] using
                  ht
              rcases hEq with ⟨hTU, hUV⟩
              subst hTU
              subst hUV
              exact ⟨T, rfl, rfl, rfl⟩
          | _ =>
              simp [hTy, __smtx_typeof_seq_op_3, h1, h2, h3] at ht
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [hTy, __smtx_typeof_seq_op_3, h1, h2, h3] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [hTy, __smtx_typeof_seq_op_3, h1, h2, h3] at ht

/-- Derives `seq_nth_args` from `non_none`. -/
theorem seq_nth_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧ __smtx_typeof t2 = SmtType.Int := by
  have ht' : __smtx_typeof_seq_nth (__smtx_typeof t1) (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_seq_nth_eq t1 t2]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Int =>
          exact ⟨T, rfl, rfl⟩
      | _ =>
          simp [__smtx_typeof_seq_nth, h1, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_seq_nth, h1, h2] at ht'

/-- Derives `seq_cons_typed` from `typeof_seq_value`. -/
theorem seq_cons_typed_of_typeof_seq_value
    {v : SmtValue} {vs : SmtSeq} {T : SmtType}
    (h : __smtx_typeof_seq_value (SmtSeq.cons v vs) = SmtType.Seq T) :
    __smtx_typeof_value v = T ∧ __smtx_typeof_seq_value vs = SmtType.Seq T := by
  by_cases hEq :
      native_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
  · have hvs : __smtx_typeof_seq_value vs = SmtType.Seq T := by
      simpa [__smtx_typeof_seq_value, native_ite, hEq] using h
    have hEq' : SmtType.Seq (__smtx_typeof_value v) = __smtx_typeof_seq_value vs := by
      simpa [native_Teq] using hEq
    have hv : __smtx_typeof_value v = T := by
      have hSeq : SmtType.Seq (__smtx_typeof_value v) = SmtType.Seq T := hEq'.trans hvs
      cases hSeq
      rfl
    exact ⟨hv, hvs⟩
  · simp [__smtx_typeof_seq_value, native_ite, hEq] at h

/-- A typed sequence over an uninhabited element type must be empty. -/
theorem seq_value_of_uninhabited_elem_empty :
    ∀ {ss : SmtSeq} {T : SmtType},
      __smtx_typeof_seq_value ss = SmtType.Seq T ->
      ¬ type_inhabited T ->
      ss = SmtSeq.empty T
  | SmtSeq.empty U, T, hss, hT => by
      cases hss
      rfl
  | SmtSeq.cons v vs, T, hss, hT => by
      rcases seq_cons_typed_of_typeof_seq_value hss with ⟨hv, _⟩
      exact False.elim (hT ⟨v, hv⟩)

/-- A value of sequence type over an uninhabited element type must be the empty sequence. -/
theorem seq_value_canonical_empty_of_uninhabited
    {v : SmtValue}
    {T : SmtType}
    (hv : __smtx_typeof_value v = SmtType.Seq T)
    (hT : ¬ type_inhabited T) :
    v = SmtValue.Seq (SmtSeq.empty T) := by
  rcases seq_value_canonical hv with ⟨ss, rfl⟩
  simp [seq_value_of_uninhabited_elem_empty hv hT]

/-- Lemma about `ssm_seq_nth_typed`. -/
theorem ssm_seq_nth_typed :
    ∀ {ss : SmtSeq} {n : native_Int} {d : SmtValue} {T : SmtType},
      __smtx_typeof_seq_value ss = SmtType.Seq T ->
        __smtx_typeof_value d = T ->
        __smtx_typeof_value (__smtx_seq_value_nth ss n d) = T
  | SmtSeq.empty U, n, d, T, hss, hd => by
      cases hss
      simpa [__smtx_seq_value_nth] using hd
  | SmtSeq.cons v vs, n, d, T, hss, hd => by
      rcases seq_cons_typed_of_typeof_seq_value hss with ⟨hv, hvs⟩
      by_cases hZero : n = 0
      · subst hZero
        simpa [__smtx_seq_value_nth] using hv
      · simpa [__smtx_seq_value_nth, hZero] using
          ssm_seq_nth_typed (ss := vs) (n := native_zplus n (native_zneg 1))
            (d := d) (T := T) hvs hd

/-- Lemma about `typeof_value_seq_nth_wrong`. -/
theorem typeof_value_seq_nth_wrong
    (M : SmtModel)
    (hM : model_wf M)
    (ss : SmtSeq)
    (n : native_Int)
    (T : SmtType)
    (hTInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true)
    (hss : __smtx_typeof_seq_value ss = SmtType.Seq T) :
    __smtx_typeof_value (__smtx_seq_nth_wrong M ss n (SmtType.Seq T)) = T := by
  change __smtx_typeof_value
      (__smtx_map_select
        (__smtx_map_select
          (native_model_lookup M native_oob_seq_nth_id
            (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T)))
          (SmtValue.Seq ss))
        (SmtValue.Numeral n)) = T
  have hLookup :
      __smtx_typeof_value
        (native_model_lookup M native_oob_seq_nth_id
          (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T))) =
        SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T) :=
    model_total_typed_lookup hM native_oob_seq_nth_id
      (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T))
      (seq_nth_wrong_map_type_wf hTInh hRec)
  rcases map_value_canonical
      (A := SmtType.Seq T) (B := SmtType.Map SmtType.Int T) hLookup with ⟨m0, hm0⟩
  rw [hm0]
  have hssVal : __smtx_typeof_value (SmtValue.Seq ss) = SmtType.Seq T := by
    simpa [__smtx_typeof_value] using hss
  have hInner :
      __smtx_typeof_value (__smtx_map_select (SmtValue.Map m0) (SmtValue.Seq ss)) =
        SmtType.Map SmtType.Int T := by
    simpa [__smtx_map_select] using
      map_lookup_typed (m := m0) (A := SmtType.Seq T) (B := SmtType.Map SmtType.Int T)
        (i := SmtValue.Seq ss)
        (by simpa [hm0, __smtx_typeof_value] using hLookup)
        hssVal
  rcases map_value_canonical (A := SmtType.Int) (B := T) hInner with ⟨m1, hm1⟩
  rw [hm1]
  simpa [__smtx_map_select] using
    map_lookup_typed (m := m1) (A := SmtType.Int) (B := T)
      (i := SmtValue.Numeral n)
          (by simpa [hm1, __smtx_typeof_value] using hInner)
      rfl

/-- Derives `str_substr_args` from `non_none`. -/
theorem str_substr_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.str_substr t1 t2 t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Int ∧
        __smtx_typeof t3 = SmtType.Int := by
  have ht' : __smtx_typeof_str_substr (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) ≠
      SmtType.None := by
    rw [← typeof_str_substr_eq t1 t2 t3]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof_str_substr, h1, h2, h3] at ht'
      exact ⟨T, rfl, rfl, rfl⟩
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof_str_substr, h1, h2, h3] at ht'

/-- Derives `str_indexof_args` from `non_none`. -/
theorem str_indexof_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.str_indexof t1 t2 t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Seq T ∧
        __smtx_typeof t3 = SmtType.Int := by
  have ht' :
      __smtx_typeof_str_indexof (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) ≠
        SmtType.None := by
    rw [← typeof_str_indexof_eq t1 t2 t3]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          cases h3 : __smtx_typeof t3 with
          | Int =>
              have hEq : T = U := by
                simpa [__smtx_typeof_str_indexof, native_ite, native_Teq, h1, h2, h3] using ht'
              subst hEq
              exact ⟨T, rfl, rfl, rfl⟩
          | _ =>
              simp [__smtx_typeof_str_indexof, h1, h2, h3] at ht'
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [__smtx_typeof_str_indexof, h1, h2, h3] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof_str_indexof, h1, h2, h3] at ht'

/-- Derives `str_at_args` from `non_none`. -/
theorem str_at_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_at t1 t2)) :
    ∃ T : SmtType, __smtx_typeof t1 = SmtType.Seq T ∧ __smtx_typeof t2 = SmtType.Int := by
  have ht' : __smtx_typeof_str_at (__smtx_typeof t1) (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_str_at_eq t1 t2]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_str_at, h1, h2] at ht'
      exact ⟨T, rfl, rfl⟩
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_str_at, h1, h2] at ht'

/-- Derives `str_update_args` from `non_none`. -/
theorem str_update_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.str_update t1 t2 t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Int ∧
        __smtx_typeof t3 = SmtType.Seq T := by
  have ht' :
      __smtx_typeof_str_update (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) ≠
        SmtType.None := by
    rw [← typeof_str_update_eq t1 t2 t3]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Int =>
          cases h3 : __smtx_typeof t3 with
          | Seq U =>
              have hEq : T = U := by
                simpa [__smtx_typeof_str_update, native_ite, native_Teq, h1, h2, h3] using ht'
              subst hEq
              exact ⟨T, rfl, rfl, rfl⟩
          | _ =>
              simp [__smtx_typeof_str_update, h1, h2, h3] at ht'
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [__smtx_typeof_str_update, h1, h2, h3] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof_str_update, h1, h2, h3] at ht'

/-- Derives `reglan_arg` from `non_none`. -/
theorem reglan_arg_of_non_none
    {op : SmtTerm -> SmtTerm} {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, native_ite, native_Teq, h] at ht
  simp

/-- Derives `reglan_binop_args` from `non_none`. -/
theorem reglan_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.RegLan ∧ __smtx_typeof t2 = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, native_ite, native_Teq, h1, h2] at ht
  exact ⟨rfl, rfl⟩

/-- Derives `re_exp_arg` from `non_none`. -/
theorem re_exp_arg_of_non_none
    {n : native_Int} {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.re_exp (SmtTerm.Numeral n) t)) :
    native_zleq 0 n ∧ __smtx_typeof t = SmtType.RegLan := by
  have ht' : __smtx_typeof_re_exp (SmtTerm.Numeral n) (__smtx_typeof t) ≠ SmtType.None := by
    rw [← typeof_re_exp_eq (SmtTerm.Numeral n) t]
    exact ht
  cases h : __smtx_typeof t with
  | RegLan =>
      by_cases hn : native_zleq 0 n
      · exact ⟨hn, rfl⟩
      · exfalso
        exact ht' (by simp [__smtx_typeof_re_exp, h, hn, native_ite])
  | _ =>
      simp [__smtx_typeof_re_exp, h] at ht'

/-- Derives `re_loop_arg` from `non_none`. -/
theorem re_loop_arg_of_non_none
    {n1 n2 : native_Int} {t : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t)) :
    native_zleq 0 n1 ∧ native_zleq 0 n2 ∧ __smtx_typeof t = SmtType.RegLan := by
  have ht' :
      __smtx_typeof_re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) (__smtx_typeof t) ≠
        SmtType.None := by
    rw [← typeof_re_loop_eq (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t]
    exact ht
  cases h : __smtx_typeof t with
  | RegLan =>
      by_cases hn1 : native_zleq 0 n1
      · by_cases hn2 : native_zleq 0 n2
        · exact ⟨hn1, hn2, rfl⟩
        · exfalso
          exact ht' (by simp [__smtx_typeof_re_loop, h, hn1, hn2, native_ite])
      · exfalso
        exact ht' (by simp [__smtx_typeof_re_loop, h, hn1, native_ite])
  | _ =>
      simp [__smtx_typeof_re_loop, h] at ht'

/-- Derives `seq_char_arg` from `non_none`. -/
theorem seq_char_arg_of_non_none
    {op : SmtTerm -> SmtTerm} {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) ret
          SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Seq SmtType.Char := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | Seq A =>
      have hSeq : A = SmtType.Char ∧ ¬ ret = SmtType.None := by
        simpa [hTy, native_ite, native_Teq, h] using ht
      have hA : A = SmtType.Char := hSeq.1
      subst hA
      rfl
  | _ =>
      simp [hTy, native_ite, native_Teq, h] at ht

/-- Derives `int_arg` from `non_none` for unary operators. -/
theorem int_arg_of_non_none_ret
    {op : SmtTerm -> SmtTerm} {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Int) ret
          SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, native_ite, native_Teq, h] at ht
  simp

/-- Derives `seq_char_binop_args` from `non_none`. -/
theorem seq_char_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char)) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.Seq SmtType.Char := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | Seq B =>
          have hSeqs : A = SmtType.Char ∧ B = SmtType.Char ∧ ¬ ret = SmtType.None := by
            simpa [hTy, native_ite, native_Teq, h1, h2] using ht
          have hAB : A = SmtType.Char ∧ B = SmtType.Char := ⟨hSeqs.1, hSeqs.2.1⟩
          rcases hAB with ⟨hA, hB⟩
          subst hA
          subst hB
          exact ⟨rfl, rfl⟩
      | _ =>
          simp [hTy, native_ite, native_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, native_ite, native_Teq, h1] at ht

/-- Derives `seq_char_reglan_args` from `non_none`. -/
theorem seq_char_reglan_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧ __smtx_typeof t2 = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | RegLan =>
          have hSeq : A = SmtType.Char ∧ ¬ ret = SmtType.None := by
            simpa [hTy, native_ite, native_Teq, h1, h2] using ht
          have hA : A = SmtType.Char := hSeq.1
          subst hA
          exact ⟨rfl, rfl⟩
      | _ =>
          simp [hTy, native_ite, native_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, native_ite, native_Teq, h1] at ht

/-- Derives `str_replace_re_args` from `non_none`. -/
theorem str_replace_re_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2 t3) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof t3) (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2 t3)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.RegLan ∧
      __smtx_typeof t3 = SmtType.Seq SmtType.Char := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | RegLan =>
          cases h3 : __smtx_typeof t3 with
          | Seq B =>
              have hArgs : A = SmtType.Char ∧ B = SmtType.Char := by
                simpa [hTy, native_ite, native_Teq, h1, h2, h3] using ht
              rcases hArgs with ⟨hA, hB⟩
              subst hA
              subst hB
              exact ⟨rfl, rfl, rfl⟩
          | _ =>
              simp [hTy, native_ite, native_Teq, h1, h2, h3] at ht
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [hTy, native_ite, native_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [hTy, native_ite, native_Teq, h1] at ht

/-- Derives `str_indexof_re_args` from `non_none`. -/
theorem str_indexof_re_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.str_indexof_re t1 t2 t3)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.RegLan ∧
      __smtx_typeof t3 = SmtType.Int := by
  have ht' :
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t3) SmtType.Int) SmtType.Int
            SmtType.None)
          SmtType.None)
        SmtType.None ≠ SmtType.None := by
    rw [← typeof_str_indexof_re_eq t1 t2 t3]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | RegLan =>
          cases h3 : __smtx_typeof t3 with
          | Int =>
              have hA : A = SmtType.Char := by
                simpa [native_ite, native_Teq, h1, h2, h3] using ht'
              subst hA
              exact ⟨rfl, rfl, rfl⟩
          | _ =>
              simp [native_ite, native_Teq, h1, h2, h3] at ht'
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [native_ite, native_Teq, h1, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [native_ite, native_Teq, h1] at ht'

/-- Derives `str_indexof_re_split_args` from `non_none`. -/
theorem str_indexof_re_split_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.str_indexof_re_split t1 t2 t3)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.RegLan ∧
      __smtx_typeof t3 = SmtType.RegLan := by
  have ht' :
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t3) SmtType.RegLan) SmtType.Int
            SmtType.None)
          SmtType.None)
        SmtType.None ≠ SmtType.None := by
    rw [← typeof_str_indexof_re_split_eq t1 t2 t3]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | RegLan =>
          cases h3 : __smtx_typeof t3 with
          | RegLan =>
              have hA : A = SmtType.Char := by
                simpa [native_ite, native_Teq, h1, h2, h3] using ht'
              subst hA
              exact ⟨rfl, rfl, rfl⟩
          | _ =>
              simp [native_ite, native_Teq, h1, h2, h3] at ht'
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [native_ite, native_Teq, h1, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [native_ite, native_Teq, h1] at ht'

/-- Shows that evaluating `str_len` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_len
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_len t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_len t)) =
      __smtx_typeof (SmtTerm.str_len t) := by
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len) (typeof_str_len_eq t) ht with
    ⟨T, hArg⟩
  rw [show __smtx_typeof (SmtTerm.str_len t) = SmtType.Int by
    rw [typeof_str_len_eq]
    simp [__smtx_typeof_seq_op_1_ret, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

/-- Shows that evaluating `str_to_lower` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_to_lower
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_to_lower t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_to_lower t)) =
      __smtx_typeof (SmtTerm.str_to_lower t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_lower) (typeof_str_to_lower_eq t) ht
  rw [show __smtx_typeof (SmtTerm.str_to_lower t) = SmtType.Seq SmtType.Char by
    rw [typeof_str_to_lower_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_to_lower (__smtx_model_eval M t)) =
    SmtType.Seq SmtType.Char
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  have hty : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hss, hArg] using hpres
  have hValid : native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hty
  rw [hss]
  change __smtx_typeof_seq_value
      (native_pack_string (native_str_to_lower (native_unpack_string ss))) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _ (native_str_to_lower_valid hValid)

/-- Shows that evaluating `str_to_upper` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_to_upper
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_to_upper t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_to_upper t)) =
      __smtx_typeof (SmtTerm.str_to_upper t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_upper) (typeof_str_to_upper_eq t) ht
  rw [show __smtx_typeof (SmtTerm.str_to_upper t) = SmtType.Seq SmtType.Char by
    rw [typeof_str_to_upper_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_to_upper (__smtx_model_eval M t)) =
    SmtType.Seq SmtType.Char
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  have hty : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hss, hArg] using hpres
  have hValid : native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hty
  rw [hss]
  change __smtx_typeof_seq_value
      (native_pack_string (native_str_to_upper (native_unpack_string ss))) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _ (native_str_to_upper_valid hValid)

/-- Shows that evaluating `str_concat` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_concat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_concat t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_concat t1 t2)) =
      __smtx_typeof (SmtTerm.str_concat t1 t2) := by
  rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat) (typeof_str_concat_eq t1 t2) ht with ⟨T, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.str_concat t1 t2) = SmtType.Seq T by
    rw [typeof_str_concat_eq]
    simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_concat (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hty2 : __smtx_typeof_seq_value ss2 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss2, h2] using hpres2
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (native_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs2 : list_typed T (native_unpack_seq ss2) :=
    typed_unpack_seq_of_typeof_seq_value hty2
  rw [hss1, hss2]
  simpa [__smtx_model_eval_str_concat, hElem1, __smtx_typeof_value, native_seq_concat] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := native_unpack_seq ss1 ++ native_unpack_seq ss2)
      (list_typed_append hxs1 hxs2))

/-- `__smtx_typeof_seq_diff` agrees with the generic sequence binary-op return type
constructor specialised to `Int`. -/
theorem seq_diff_typeof_fn_eq (A B : SmtType) :
    __smtx_typeof_seq_diff A B =
      __smtx_typeof_seq_op_2_ret A B SmtType.Int := by
  cases A <;> cases B <;> rfl

/-- Rewrites the typing equation for `seq_diff`. Its result type matches the generic
sequence binary-op return type with `Int`, so the existing seq helpers apply. -/
theorem typeof_seq_diff_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_diff t1 t2) =
      __smtx_typeof_seq_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Int := by
  have h : __smtx_typeof (SmtTerm.seq_diff t1 t2) =
      __smtx_typeof_seq_diff (__smtx_typeof t1) (__smtx_typeof t2) := by
    rw [__smtx_typeof.eq_def] <;> simp only
  rw [h, seq_diff_typeof_fn_eq]

/-- Shows that evaluating `seq_diff` terms produces values of the expected (`Int`) type.

`native_eval_seq_diff` is a macro containing a `let rec`, so each textual occurrence
elaborates to a distinct recursion that is not definitionally equal across expansions.  We
therefore unfold `__smtx_model_eval_seq_diff` (which bakes in a single expansion) rather than
restating the macro, and only ever observe that the result is a `Numeral`. -/
theorem typeof_value_model_eval_seq_diff
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.seq_diff t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_diff t1 t2)) =
      __smtx_typeof (SmtTerm.seq_diff t1 t2) := by
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.seq_diff)
      (typeof_seq_diff_eq t1 t2) ht with ⟨T, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.seq_diff t1 t2) = SmtType.Int by
    rw [typeof_seq_diff_eq]
    simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_seq_diff (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Int
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  -- `native_eval_seq_diff` now always returns a `Numeral` (the differing index,
  -- or `-1` as the default), so the result type is unconditionally `Int`.
  simp only [__smtx_model_eval_seq_diff]
  split <;> rfl

/-- Shows that evaluating `str_substr` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_substr
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_substr t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.str_substr t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_substr t1 t2 t3) := by
  rcases str_substr_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.str_substr t1 t2 t3) =
        SmtType.Seq T by
    rw [typeof_str_substr_eq]
    simp [__smtx_typeof_str_substr, h1, h2, h3]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_substr (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hn2⟩
  rcases int_value_canonical (by simpa [h3] using hpres3) with ⟨n3, hn3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (native_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  rw [hss1, hn2, hn3]
  simpa [__smtx_model_eval_str_substr, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := native_seq_extract (native_unpack_seq ss1) n2 n3)
      (list_typed_extract hxs1 n2 n3))

/-- Shows that evaluating `str_contains` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_contains
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_contains t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_contains t1 t2)) =
      __smtx_typeof (SmtTerm.str_contains t1 t2) := by
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
      (typeof_str_contains_eq t1 t2) ht with ⟨T, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.str_contains t1 t2) = SmtType.Bool by
    rw [typeof_str_contains_eq]
    simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_contains (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  rfl

/-- Shows that evaluating `str_indexof` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_indexof
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_indexof t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.str_indexof t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_indexof t1 t2 t3) := by
  rcases str_indexof_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.str_indexof t1 t2 t3) =
        SmtType.Int by
    rw [typeof_str_indexof_eq]
    simp [__smtx_typeof_str_indexof, native_ite, native_Teq, h1, h2, h3]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_indexof (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Int
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rcases int_value_canonical (by simpa [h3] using hpres3) with ⟨n, hn⟩
  rw [hss1, hss2, hn]
  rfl

/-- Shows that evaluating `str_at` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_at
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_at t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_at t1 t2)) =
      __smtx_typeof (SmtTerm.str_at t1 t2) := by
  rcases str_at_args_of_non_none ht with ⟨T, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.str_at t1 t2) = SmtType.Seq T by
    rw [typeof_str_at_eq]
    simp [__smtx_typeof_str_at, h1, h2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_at (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hn2⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (native_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  rw [hss1, hn2]
  simpa [__smtx_model_eval_str_at, __smtx_model_eval_str_substr, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := native_seq_extract (native_unpack_seq ss1) n2 1)
      (list_typed_extract hxs1 n2 1))

/-- Shows that evaluating `str_replace` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_replace
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_replace t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.str_replace t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_replace t1 t2 t3) := by
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace) (typeof_str_replace_eq t1 t2 t3) ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.str_replace t1 t2 t3) =
        SmtType.Seq T by
    rw [typeof_str_replace_eq]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq, h1, h2, h3]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_replace (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rcases seq_value_canonical (by simpa [h3] using hpres3) with ⟨ss3, hss3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hty3 : __smtx_typeof_seq_value ss3 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss3, h3] using hpres3
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (native_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs3 : list_typed T (native_unpack_seq ss3) :=
    typed_unpack_seq_of_typeof_seq_value hty3
  rw [hss1, hss2, hss3]
  simpa [__smtx_model_eval_str_replace, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := native_seq_replace (native_unpack_seq ss1) (native_unpack_seq ss2)
        (native_unpack_seq ss3))
      (list_typed_replace hxs1 hxs3))

/-- Shows that evaluating `str_rev` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_rev
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_rev t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_rev t)) =
      __smtx_typeof (SmtTerm.str_rev t) := by
  rcases seq_arg_of_non_none (op := SmtTerm.str_rev) (typeof_str_rev_eq t) ht with ⟨T, hArg⟩
  rw [show __smtx_typeof (SmtTerm.str_rev t) = SmtType.Seq T by
    rw [typeof_str_rev_eq]
    simp [__smtx_typeof_seq_op_1, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_rev (__smtx_model_eval M t)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  have hty : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss, hArg] using hpres
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty
  have hxs : list_typed T (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hty
  rw [hss]
  simpa [__smtx_model_eval_str_rev, hElem, __smtx_typeof_value, native_seq_rev] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := (native_unpack_seq ss).reverse)
      (list_typed_reverse hxs))

/-- Shows that evaluating `str_update` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_update
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_update t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.str_update t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_update t1 t2 t3) := by
  rcases str_update_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.str_update t1 t2 t3) =
        SmtType.Seq T by
    rw [typeof_str_update_eq]
    simp [__smtx_typeof_str_update, native_ite, native_Teq, h1, h2, h3]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_update (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hn2⟩
  rcases seq_value_canonical (by simpa [h3] using hpres3) with ⟨ss3, hss3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hty3 : __smtx_typeof_seq_value ss3 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss3, h3] using hpres3
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (native_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs3 : list_typed T (native_unpack_seq ss3) :=
    typed_unpack_seq_of_typeof_seq_value hty3
  rw [hss1, hn2, hss3]
  simpa [__smtx_model_eval_str_update, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := native_seq_update (native_unpack_seq ss1) n2 (native_unpack_seq ss3))
      (list_typed_update hxs1 hxs3 n2))

/-- Shows that evaluating `str_replace_all` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_replace_all
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_replace_all t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.str_replace_all t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_replace_all t1 t2 t3) := by
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all) (typeof_str_replace_all_eq t1 t2 t3) ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.str_replace_all t1 t2 t3) =
        SmtType.Seq T by
    rw [typeof_str_replace_all_eq]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq, h1, h2, h3]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_replace_all (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rcases seq_value_canonical (by simpa [h3] using hpres3) with ⟨ss3, hss3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hty3 : __smtx_typeof_seq_value ss3 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss3, h3] using hpres3
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (native_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs3 : list_typed T (native_unpack_seq ss3) :=
    typed_unpack_seq_of_typeof_seq_value hty3
  rw [hss1, hss2, hss3]
  simpa [__smtx_model_eval_str_replace_all, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := native_seq_replace_all (native_unpack_seq ss1) (native_unpack_seq ss2)
        (native_unpack_seq ss3))
      (list_typed_replace_all hxs1 hxs3))

/-- Shows that evaluating `str_replace_re` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_replace_re
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_replace_re t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.str_replace_re t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_replace_re t1 t2 t3) := by
  have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re) (typeof_str_replace_re_eq t1 t2 t3) ht
  rw [show __smtx_typeof
      (SmtTerm.str_replace_re t1 t2 t3) =
        SmtType.Seq SmtType.Char by
    rw [typeof_str_replace_re_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_replace_re (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq SmtType.Char
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.1] using hpres2) with ⟨r, hr⟩
  rcases seq_value_canonical (by simpa [hArgs.2.2] using hpres3) with ⟨ss3, hss3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hss1, hArgs.1] using hpres1
  have hty3 : __smtx_typeof_seq_value ss3 = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hss3, hArgs.2.2] using hpres3
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed SmtType.Char (native_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs3 : list_typed SmtType.Char (native_unpack_seq ss3) :=
    typed_unpack_seq_of_typeof_seq_value hty3
  rw [hss1, hr, hss3]
  simpa [__smtx_model_eval_str_replace_re, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := SmtType.Char)
      (xs := native_str_replace_re (native_unpack_seq ss1) r (native_unpack_seq ss3))
      (list_typed_replace_re r hxs1 hxs3))

/-- Shows that evaluating `str_replace_re_all` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_replace_re_all
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_replace_re_all t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.str_replace_re_all t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_replace_re_all t1 t2 t3) := by
  have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all) (typeof_str_replace_re_all_eq t1 t2 t3) ht
  rw [show __smtx_typeof
      (SmtTerm.str_replace_re_all t1 t2 t3) =
        SmtType.Seq SmtType.Char by
    rw [typeof_str_replace_re_all_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_replace_re_all (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq SmtType.Char
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.1] using hpres2) with ⟨r, hr⟩
  rcases seq_value_canonical (by simpa [hArgs.2.2] using hpres3) with ⟨ss3, hss3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hss1, hArgs.1] using hpres1
  have hty3 : __smtx_typeof_seq_value ss3 = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hss3, hArgs.2.2] using hpres3
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed SmtType.Char (native_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs3 : list_typed SmtType.Char (native_unpack_seq ss3) :=
    typed_unpack_seq_of_typeof_seq_value hty3
  rw [hss1, hr, hss3]
  simpa [__smtx_model_eval_str_replace_re_all, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := SmtType.Char)
      (xs := native_str_replace_re_all (native_unpack_seq ss1) r (native_unpack_seq ss3))
      (list_typed_replace_re_all r hxs1 hxs3))

/-- Shows that evaluating `str_indexof_re` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_indexof_re
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_indexof_re t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.str_indexof_re t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_indexof_re t1 t2 t3) := by
  have hArgs := str_indexof_re_args_of_non_none ht
  rw [show __smtx_typeof
      (SmtTerm.str_indexof_re t1 t2 t3) =
        SmtType.Int by
    rw [typeof_str_indexof_re_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_indexof_re (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Int
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.1] using hpres2) with ⟨r, hr⟩
  rcases int_value_canonical (by simpa [hArgs.2.2] using hpres3) with ⟨n, hn⟩
  rw [hss1, hr, hn]
  rfl

/-- Typing equation for the `@strings_occur_index` skolem operator. -/
theorem typeof_at_strings_occur_index_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm._at_strings_occur_index t1 t2 t3) =
      __smtx_typeof_str_indexof (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Typing equation for the `@strings_occur_index_re` skolem operator. -/
theorem typeof_at_strings_occur_index_re_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm._at_strings_occur_index_re t1 t2 t3) =
      native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t3) SmtType.Int) SmtType.Int
            SmtType.None)
          SmtType.None)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Derives `@strings_occur_index` argument types from `non_none`; the
typing guard coincides with `str_indexof`. -/
theorem at_strings_occur_index_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm._at_strings_occur_index t1 t2 t3)) :
    ∃ T,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Seq T ∧
        __smtx_typeof t3 = SmtType.Int := by
  apply str_indexof_args_of_non_none (t1 := t1) (t2 := t2) (t3 := t3)
  unfold term_has_non_none_type at ht ⊢
  rw [typeof_str_indexof_eq]
  rw [typeof_at_strings_occur_index_eq] at ht
  exact ht

/-- Derives `@strings_occur_index_re` argument types from `non_none`; the
typing guard coincides with `str_indexof_re`. -/
theorem at_strings_occur_index_re_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm._at_strings_occur_index_re t1 t2 t3)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.RegLan ∧
      __smtx_typeof t3 = SmtType.Int := by
  apply str_indexof_re_args_of_non_none (t1 := t1) (t2 := t2) (t3 := t3)
  unfold term_has_non_none_type at ht ⊢
  rw [typeof_str_indexof_re_eq]
  rw [typeof_at_strings_occur_index_re_eq] at ht
  exact ht

/-- Shows that evaluating `@strings_occur_index` terms produces values of
the expected type. -/
theorem typeof_value_model_eval_at_strings_occur_index
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm._at_strings_occur_index t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm._at_strings_occur_index t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm._at_strings_occur_index t1 t2 t3) := by
  rcases at_strings_occur_index_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm._at_strings_occur_index t1 t2 t3) =
        SmtType.Int by
    rw [typeof_at_strings_occur_index_eq]
    simp [__smtx_typeof_str_indexof, native_ite, native_Teq, h1, h2, h3]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval__at_strings_occur_index (__smtx_model_eval M t1)
        (__smtx_model_eval M t2) (__smtx_model_eval M t3)) = SmtType.Int
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rcases int_value_canonical (by simpa [h3] using hpres3) with ⟨n, hn⟩
  rw [hss1, hss2, hn]
  rfl

/-- Shows that evaluating `@strings_occur_index_re` terms produces values of
the expected type. -/
theorem typeof_value_model_eval_at_strings_occur_index_re
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm._at_strings_occur_index_re t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm._at_strings_occur_index_re t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm._at_strings_occur_index_re t1 t2 t3) := by
  have hArgs := at_strings_occur_index_re_args_of_non_none ht
  rw [show __smtx_typeof
      (SmtTerm._at_strings_occur_index_re t1 t2 t3) =
        SmtType.Int by
    rw [typeof_at_strings_occur_index_re_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval__at_strings_occur_index_re (__smtx_model_eval M t1)
        (__smtx_model_eval M t2) (__smtx_model_eval M t3)) = SmtType.Int
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.1] using hpres2) with ⟨r, hr⟩
  rcases int_value_canonical (by simpa [hArgs.2.2] using hpres3) with ⟨n, hn⟩
  rw [hss1, hr, hn]
  rfl

/-- Shows that evaluating `str_indexof_re_split` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_indexof_re_split
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.str_indexof_re_split t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.str_indexof_re_split t1 t2 t3)) =
      __smtx_typeof
        (SmtTerm.str_indexof_re_split t1 t2 t3) := by
  have hArgs := str_indexof_re_split_args_of_non_none ht
  rw [show __smtx_typeof
      (SmtTerm.str_indexof_re_split t1 t2 t3) =
        SmtType.Int by
    rw [typeof_str_indexof_re_split_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value
      (__smtx_model_eval_str_indexof_re_split (__smtx_model_eval M t1)
        (__smtx_model_eval M t2) (__smtx_model_eval M t3)) = SmtType.Int
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.1] using hpres2) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.2] using hpres3) with ⟨r2, hr2⟩
  rw [hss1, hr1, hr2]
  rfl

/-- Shows that evaluating `str_to_code` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_to_code
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_to_code t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_to_code t)) =
      __smtx_typeof (SmtTerm.str_to_code t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_code) (typeof_str_to_code_eq t) ht
  rw [show __smtx_typeof (SmtTerm.str_to_code t) = SmtType.Int by
    rw [typeof_str_to_code_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_to_code (__smtx_model_eval M t)) =
    SmtType.Int
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

/-- Shows that evaluating `str_to_int` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_to_int t)) =
      __smtx_typeof (SmtTerm.str_to_int t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int) (typeof_str_to_int_eq t) ht
  rw [show __smtx_typeof (SmtTerm.str_to_int t) = SmtType.Int by
    rw [typeof_str_to_int_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_to_int (__smtx_model_eval M t)) =
    SmtType.Int
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

/-- Shows that evaluating `str_from_code` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_from_code
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_from_code t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_from_code t)) =
      __smtx_typeof (SmtTerm.str_from_code t) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_code) (typeof_str_from_code_eq t) ht
  rw [show __smtx_typeof (SmtTerm.str_from_code t) = SmtType.Seq SmtType.Char by
    rw [typeof_str_from_code_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_from_code (__smtx_model_eval M t)) =
    SmtType.Seq SmtType.Char
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  change __smtx_typeof_seq_value (native_pack_string (native_str_from_code n)) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _ (native_str_from_code_valid n)

/-- Shows that evaluating `str_from_int` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_from_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_from_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_from_int t)) =
      __smtx_typeof (SmtTerm.str_from_int t) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int) (typeof_str_from_int_eq t) ht
  rw [show __smtx_typeof (SmtTerm.str_from_int t) = SmtType.Seq SmtType.Char by
    rw [typeof_str_from_int_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_from_int (__smtx_model_eval M t)) =
    SmtType.Seq SmtType.Char
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  change __smtx_typeof_seq_value (native_pack_string (native_str_from_int n)) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _ (native_str_from_int_valid n)

/-- Shows that evaluating `str_to_re` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_to_re
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_to_re t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_to_re t)) =
      __smtx_typeof (SmtTerm.str_to_re t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_re) (typeof_str_to_re_eq t) ht
  rw [show __smtx_typeof (SmtTerm.str_to_re t) = SmtType.RegLan by
    rw [typeof_str_to_re_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_to_re (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

/-- Shows that evaluating `re_mult` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_mult
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_mult t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_mult t)) =
      __smtx_typeof (SmtTerm.re_mult t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_mult) (typeof_re_mult_eq t) ht
  rw [show __smtx_typeof (SmtTerm.re_mult t) = SmtType.RegLan by
    rw [typeof_re_mult_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_mult (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

/-- Shows that evaluating `re_plus` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_plus
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_plus t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_plus t)) =
      __smtx_typeof (SmtTerm.re_plus t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_plus) (typeof_re_plus_eq t) ht
  rw [show __smtx_typeof (SmtTerm.re_plus t) = SmtType.RegLan by
    rw [typeof_re_plus_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_plus (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

/-- Lemma about `model_eval_re_exp_rec_reglan`. -/
theorem model_eval_re_exp_rec_reglan :
    ∀ (n : native_Nat) (r : SmtRegLan),
      ∃ r' : SmtRegLan,
        __smtx_re_exp_rec n (SmtValue.RegLan r) = SmtValue.RegLan r'
  | native_nat_zero, r =>
      ⟨native_str_to_re (native_unpack_seq (SmtSeq.empty SmtType.Char)), by
        simp [__smtx_re_exp_rec]⟩
  | native_nat_succ n, r => by
      rcases model_eval_re_exp_rec_reglan n r with ⟨r', hr'⟩
      refine ⟨native_re_concat r' r, ?_⟩
      simp [__smtx_re_exp_rec, hr', __smtx_model_eval_re_concat]

/-- Lemma about `model_eval_re_exp_reglan`. -/
theorem model_eval_re_exp_reglan
    (n : native_Int)
    (r : SmtRegLan) :
    ∃ r' : SmtRegLan,
      __smtx_model_eval_re_exp (SmtValue.Numeral n) (SmtValue.RegLan r) = SmtValue.RegLan r' := by
  rcases model_eval_re_exp_rec_reglan (native_int_to_nat n) r with ⟨r', hr'⟩
  exact ⟨r', by simpa [__smtx_model_eval_re_exp] using hr'⟩

/-- Shows that evaluating `re_exp` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_exp
    (M : SmtModel)
    (n : native_Int)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_exp (SmtTerm.Numeral n) t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.re_exp (SmtTerm.Numeral n) t)) =
      __smtx_typeof (SmtTerm.re_exp (SmtTerm.Numeral n) t) := by
  rcases re_exp_arg_of_non_none ht with ⟨hn, hArg⟩
  rw [show __smtx_typeof (SmtTerm.re_exp (SmtTerm.Numeral n) t) =
      SmtType.RegLan by
    rw [typeof_re_exp_eq]
    simp [__smtx_typeof_re_exp, hArg, hn, native_ite]]
  rw [__smtx_model_eval.eq_110, __smtx_model_eval.eq_2]
  change __smtx_typeof_value (__smtx_model_eval_re_exp (SmtValue.Numeral n) (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rcases model_eval_re_exp_reglan n r with ⟨r', hr'⟩
  rw [hr']
  rfl

/-- Shows that evaluating `re_opt` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_opt
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_opt t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_opt t)) =
      __smtx_typeof (SmtTerm.re_opt t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_opt) (typeof_re_opt_eq t) ht
  rw [show __smtx_typeof (SmtTerm.re_opt t) = SmtType.RegLan by
    rw [typeof_re_opt_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_opt (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

/-- Shows that evaluating `re_comp` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_comp
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_comp t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_comp t)) =
      __smtx_typeof (SmtTerm.re_comp t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_comp) (typeof_re_comp_eq t) ht
  rw [show __smtx_typeof (SmtTerm.re_comp t) = SmtType.RegLan by
    rw [typeof_re_comp_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_comp (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

/-- Shows that evaluating `re_range` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_range
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_range t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_range t1 t2)) =
      __smtx_typeof (SmtTerm.re_range t1 t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.re_range) (typeof_re_range_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.re_range t1 t2) =
      SmtType.RegLan by
    rw [typeof_re_range_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_range (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  rfl

/-- Shows that evaluating `re_concat` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_concat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_concat t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_concat t1 t2)) =
      __smtx_typeof (SmtTerm.re_concat t1 t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_concat) (typeof_re_concat_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.re_concat t1 t2) =
      SmtType.RegLan by
    rw [typeof_re_concat_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_concat (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

/-- Shows that evaluating `re_inter` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_inter
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_inter t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_inter t1 t2)) =
      __smtx_typeof (SmtTerm.re_inter t1 t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_inter) (typeof_re_inter_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.re_inter t1 t2) =
      SmtType.RegLan by
    rw [typeof_re_inter_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_inter (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

/-- Shows that evaluating `re_union` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_union
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_union t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_union t1 t2)) =
      __smtx_typeof (SmtTerm.re_union t1 t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_union) (typeof_re_union_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.re_union t1 t2) =
      SmtType.RegLan by
    rw [typeof_re_union_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_union (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

/-- Shows that evaluating `re_diff` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_diff
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.re_diff t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.re_diff t1 t2)) =
      __smtx_typeof (SmtTerm.re_diff t1 t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_diff) (typeof_re_diff_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.re_diff t1 t2) =
      SmtType.RegLan by
    rw [typeof_re_diff_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_re_diff (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

/-- Lemma about `model_eval_re_loop_rec_reglan`. -/
theorem model_eval_re_loop_rec_reglan :
    ∀ (n : native_Nat) (n1 n2 : native_Int) (r : SmtRegLan),
      ∃ r' : SmtRegLan,
        __smtx_re_loop_rec n (SmtValue.Numeral n1) (SmtValue.Numeral n2)
          (SmtValue.RegLan r) = SmtValue.RegLan r'
  | native_nat_zero, n1, n2, r => by
      rcases model_eval_re_exp_reglan n1 r with ⟨r', hr'⟩
      exact ⟨r', by simpa [__smtx_re_loop_rec] using hr'⟩
  | native_nat_succ n, n1, n2, r => by
      rcases model_eval_re_loop_rec_reglan n n1 (native_zplus n2 (native_zneg 1)) r with
        ⟨r1, hr1⟩
      rcases model_eval_re_exp_reglan n2 r with ⟨r2, hr2⟩
      refine ⟨native_re_union r1 r2, ?_⟩
      simp [__smtx_re_loop_rec, hr1, hr2, __smtx_model_eval_re_union]

/-- Shows that evaluating `re_loop` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_loop
    (M : SmtModel)
    (n1 n2 : native_Int)
    (t : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t)) =
      __smtx_typeof
        (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t) := by
  rcases re_loop_arg_of_non_none ht with ⟨hn1, hn2, hArg⟩
  rw [show __smtx_typeof
      (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t) = SmtType.RegLan by
    rw [typeof_re_loop_eq]
    simp [__smtx_typeof_re_loop, hArg, hn1, hn2, native_ite]]
  rw [__smtx_model_eval.eq_118, __smtx_model_eval.eq_2, __smtx_model_eval.eq_2]
  change __smtx_typeof_value
      (__smtx_model_eval_re_loop (SmtValue.Numeral n1) (SmtValue.Numeral n2)
        (__smtx_model_eval M t)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  by_cases hlt : native_zlt n2 n1
  · simp [__smtx_model_eval_re_loop, __smtx_model_eval_gt, __smtx_model_eval_lt,
      __smtx_model_eval_ite, hlt, __smtx_typeof_value]
  · rcases model_eval_re_loop_rec_reglan (native_int_to_nat (native_zplus n2 (native_zneg n1)))
        n1 n2 r with ⟨r', hr'⟩
    simp [__smtx_model_eval_re_loop, __smtx_model_eval_gt, __smtx_model_eval_lt,
      __smtx_model_eval_ite, hlt, hr', __smtx_typeof_value]

/-- Shows that evaluating `str_in_re` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_in_re
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_in_re t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_in_re t1 t2)) =
      __smtx_typeof (SmtTerm.str_in_re t1 t2) := by
  have hArgs := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re) (typeof_str_in_re_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.str_in_re t1 t2) =
      SmtType.Bool by
    rw [typeof_str_in_re_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_in_re (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss, hss⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r, hr⟩
  rw [hss, hr]
  rfl

/-- Shows that evaluating `str_lt` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_lt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_lt t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_lt t1 t2)) =
      __smtx_typeof (SmtTerm.str_lt t1 t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_lt) (typeof_str_lt_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.str_lt t1 t2) =
      SmtType.Bool by
    rw [typeof_str_lt_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_lt (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  rfl

/-- Shows that evaluating `str_leq` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_leq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_leq t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_leq t1 t2)) =
      __smtx_typeof (SmtTerm.str_leq t1 t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_leq) (typeof_str_leq_eq t1 t2) ht
  rw [show __smtx_typeof (SmtTerm.str_leq t1 t2) =
      SmtType.Bool by
    rw [typeof_str_leq_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_leq (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_leq
  rcases bool_value_canonical
      (typeof_value_model_eval_eq_value (SmtValue.Seq ss1) (SmtValue.Seq ss2)) with
    ⟨bEq, hbEq⟩
  rw [hbEq]
  rfl

/-- Shows that evaluating `str_prefixof` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_prefixof
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_prefixof t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.str_prefixof t1 t2)) =
      __smtx_typeof (SmtTerm.str_prefixof t1 t2) := by
  have hArgs := seq_binop_args_of_non_none_ret (op := SmtTerm.str_prefixof)
    (typeof_str_prefixof_eq t1 t2) ht
  rcases hArgs with ⟨T, hT1, hT2⟩
  rw [show __smtx_typeof (SmtTerm.str_prefixof t1 t2) =
      SmtType.Bool by
    rw [typeof_str_prefixof_eq]
    simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, hT1, hT2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_prefixof (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hT1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hT2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_prefixof
  simpa using
    typeof_value_model_eval_eq_value
      (SmtValue.Seq ss1)
      (__smtx_model_eval_str_substr (SmtValue.Seq ss2) (SmtValue.Numeral 0)
        (__smtx_model_eval_str_len (SmtValue.Seq ss1)))

/-- Shows that evaluating `str_suffixof` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_suffixof
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_suffixof t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.str_suffixof t1 t2)) =
      __smtx_typeof (SmtTerm.str_suffixof t1 t2) := by
  have hArgs := seq_binop_args_of_non_none_ret (op := SmtTerm.str_suffixof)
    (typeof_str_suffixof_eq t1 t2) ht
  rcases hArgs with ⟨T, hT1, hT2⟩
  rw [show __smtx_typeof (SmtTerm.str_suffixof t1 t2) =
      SmtType.Bool by
    rw [typeof_str_suffixof_eq]
    simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, hT1, hT2]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_suffixof (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hT1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hT2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_suffixof
  simpa using
    typeof_value_model_eval_eq_value
      (SmtValue.Seq ss1)
      (__smtx_model_eval_str_substr (SmtValue.Seq ss2)
        (__smtx_model_eval__ (__smtx_model_eval_str_len (SmtValue.Seq ss2))
          (__smtx_model_eval_str_len (SmtValue.Seq ss1)))
        (__smtx_model_eval_str_len (SmtValue.Seq ss1)))

/-- Shows that evaluating `str_is_digit` terms produces values of the expected type. -/
theorem typeof_value_model_eval_str_is_digit
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.str_is_digit t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.str_is_digit t)) =
      __smtx_typeof (SmtTerm.str_is_digit t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_is_digit) (typeof_str_is_digit_eq t) ht
  rw [show __smtx_typeof (SmtTerm.str_is_digit t) = SmtType.Bool by
    rw [typeof_str_is_digit_eq]
    simp [native_ite, native_Teq, hArg]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_model_eval_str_is_digit (__smtx_model_eval M t)) =
    SmtType.Bool
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  simp [__smtx_model_eval_str_is_digit, __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
    __smtx_model_eval_and, __smtx_typeof_value]

/-- Shows that evaluating `seq_nth` terms produces values of the expected type. -/
theorem typeof_value_model_eval_seq_nth
    (M : SmtModel)
    (hM : model_wf M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2))
    (hElemRec :
      ∀ {T : SmtType},
        __smtx_typeof t1 = SmtType.Seq T ->
          __smtx_type_wf_rec T = true)
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.seq_nth t1 t2)) =
      __smtx_typeof (SmtTerm.seq_nth t1 t2) := by
  rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_seq_nth_eq t1 t2] at ht
    simpa [__smtx_typeof_seq_nth, h1, h2] using ht
  have hTy :
      __smtx_typeof (SmtTerm.seq_nth t1 t2) = T := by
    have hTy' : __smtx_typeof_guard_wf T T = T :=
      smtx_typeof_guard_wf_of_non_none T T hGuardNN
    rw [typeof_seq_nth_eq t1 t2]
    simpa [__smtx_typeof_seq_nth, h1, h2] using hTy'
  rw [hTy]
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_typeof_value (__smtx_seq_nth M (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss, hss⟩
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n, hn⟩
  rw [hss, hn]
  unfold __smtx_seq_nth
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hss, h1, __smtx_typeof_value] using hpres1
  have hRec : __smtx_type_wf_rec T = true := by
    exact hElemRec h1
  have hTWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hTInh : native_inhabited_type T = true := by
    cases T <;>
      simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
        native_and] at hTWf hRec ⊢
    all_goals first | exact hTWf | exact hTWf.1 | exact hTWf.1.1 | contradiction
  have hd :
      __smtx_typeof_value
        (__smtx_seq_nth_wrong M ss n (__smtx_typeof_seq_value ss)) = T := by
    rw [hssTy]
    exact typeof_value_seq_nth_wrong M hM ss n T hTInh hRec hssTy
  simpa using ssm_seq_nth_typed (ss := ss) (n := n)
    (d := __smtx_seq_nth_wrong M ss n (__smtx_typeof_seq_value ss)) (T := T) hssTy hd

end Smtm
