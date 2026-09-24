module

public import Cpc.Proofs.RuleSupport.Cong.Binders
import all Cpc.Proofs.RuleSupport.Cong.Binders

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

theorem congTypeSpine_eq_has_bool_type (t rhs : Term) :
  RuleProofs.eo_has_smt_translation t ->
  CongTypeSpine t rhs ->
  RuleProofs.eo_has_bool_type (mkEq t rhs) := by
  intro hTrans hSpine
  match t with
  | Term.Apply (Term.UOp UserOp.not) x =>
      exact congTypeSpine_not_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.ite) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.ite) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.or) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.or) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.and) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.and) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.imp) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.imp) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.xor) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.xor) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.eq) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.eq) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.Int) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.Int x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.Real) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.Real x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.BitVec) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.BitVec x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.Char) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.Char x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.Seq) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.Seq x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.Array) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.Array x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.RegLan) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.RegLan x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.UnitTuple) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.UnitTuple x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.Tuple) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.Tuple x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.Set) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.Set x rhs (by rfl) hTrans
  | Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂ =>
      exact congTypeSpine_eq_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e =>
      exact congTypeSpine_ite_eq_has_bool_type c t e rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e =>
      exact congTypeSpine_bvite_eq_has_bool_type c t e rhs hTrans hSpine
  | Term.Apply (Term.Var (Term.String s) T) x =>
      exact congTypeSpine_var_apply_eq_has_bool_type s T x rhs hTrans hSpine
  | Term.Apply (Term.UConst i T) x =>
      exact congTypeSpine_uconst_apply_eq_has_bool_type i T x rhs hTrans hSpine
  | Term.Apply (Term.DtSel s d i j) x =>
      exact congTypeSpine_dt_sel_eq_has_bool_type
        s d i j x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂ =>
      exact congTypeSpine_var_apply_apply_eq_has_bool_type
        s T x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂ =>
      exact congTypeSpine_uconst_apply_apply_eq_has_bool_type
        i T x₁ x₂ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃ =>
      exact congTypeSpine_var_apply_apply_apply_eq_has_bool_type
        s T x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃ =>
      exact congTypeSpine_uconst_apply_apply_apply_eq_has_bool_type
        i T x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
      x₄ =>
      exact congTypeSpine_var_apply_apply_apply_apply_eq_has_bool_type
        s T x₁ x₂ x₃ x₄ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
      x₄ =>
      exact congTypeSpine_uconst_apply_apply_apply_apply_eq_has_bool_type
        i T x₁ x₂ x₃ x₄ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
        x₄) x₅ =>
      exact congTypeSpine_var_apply_apply_apply_apply_apply_eq_has_bool_type
        s T x₁ x₂ x₃ x₄ x₅ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        x₄) x₅ =>
      exact congTypeSpine_uconst_apply_apply_apply_apply_apply_eq_has_bool_type
        i T x₁ x₂ x₃ x₄ x₅ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
          x₄) x₅) x₆ =>
      exact congTypeSpine_var_apply_apply_apply_apply_apply_apply_eq_has_bool_type
        s T x₁ x₂ x₃ x₄ x₅ x₆ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
          x₄) x₅) x₆ =>
      exact congTypeSpine_uconst_apply_apply_apply_apply_apply_apply_eq_has_bool_type
        i T x₁ x₂ x₃ x₄ x₅ x₆ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂ =>
      exact congTypeSpine_and_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂ =>
      exact congTypeSpine_or_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂ =>
      exact congTypeSpine_imp_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂ =>
      exact congTypeSpine_xor_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.plus) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.plus) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.neg) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.neg) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.mult) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.mult) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.lt) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.lt) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.leq) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.leq) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.gt) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.gt) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.geq) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.geq) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂ =>
      exact congTypeSpine_plus_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂ =>
      exact congTypeSpine_neg_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂ =>
      exact congTypeSpine_mult_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂ =>
      exact congTypeSpine_lt_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂ =>
      exact congTypeSpine_leq_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂ =>
      exact congTypeSpine_gt_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂ =>
      exact congTypeSpine_geq_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.to_real) x =>
      exact congTypeSpine_to_real_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.to_int) x =>
      exact congTypeSpine_to_int_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.is_int) x =>
      exact congTypeSpine_is_int_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.abs) x =>
      exact congTypeSpine_abs_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.__eoo_neg_2) x =>
      exact congTypeSpine_uneg_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.div) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.div) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.mod) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.mod) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.div_total) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.div_total) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.mod_total) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.mod_total) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.UOp UserOp.divisible) x =>
      exact False.elim
        (no_translation_of_eo_apply_none_head
          (f := Term.UOp UserOp.divisible) (x := x) (by rfl) hTrans)
  | Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂ =>
      exact congTypeSpine_div_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂ =>
      exact congTypeSpine_mod_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂ =>
      exact congTypeSpine_div_total_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂ =>
      exact congTypeSpine_mod_total_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂ =>
      exact congTypeSpine_divisible_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.int_pow2) x =>
      exact congTypeSpine_int_pow2_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.int_log2) x =>
      exact congTypeSpine_int_log2_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.int_ispow2) x =>
      exact congTypeSpine_int_ispow2_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x =>
      exact congTypeSpine_int_div_by_zero_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp._at_mod_by_zero) x =>
      exact congTypeSpine_mod_by_zero_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.select) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.select x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.store) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.store x rhs (by rfl) hTrans
  | Term.Apply (Term.Apply (Term.UOp UserOp.select) x₁) x₂ =>
      exact congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.select
        SmtTerm.select
        (by intro a b; rfl)
        (by
          intro a b a' b' ha hb
          rw [typeof_select_eq, typeof_select_eq, ha, hb])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.store
        SmtTerm.store
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_store_eq, typeof_store_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp._at_bvsize) x =>
      exact congTypeSpine_bvsize_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.qdiv) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.qdiv x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.qdiv_total) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.qdiv_total x rhs (by rfl) hTrans
  | Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂ =>
      exact congTypeSpine_qdiv_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂ =>
      exact congTypeSpine_qdiv_total_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp._at_div_by_zero) x =>
      exact congTypeSpine_qdiv_by_zero_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_len) x =>
      exact congTypeSpine_seq_unop_ret_eq_has_bool_type UserOp.str_len
        SmtTerm.str_len SmtType.Int
        (by intro a; rfl)
        (by intro a; exact typeof_str_len_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_rev) x =>
      exact congTypeSpine_seq_unop_eq_has_bool_type UserOp.str_rev
        SmtTerm.str_rev
        (by intro a; rfl)
        (by intro a; exact typeof_str_rev_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_lower) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_lower SmtTerm.str_to_lower (SmtType.Seq SmtType.Char)
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_lower_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_upper) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_upper SmtTerm.str_to_upper (SmtType.Seq SmtType.Char)
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_upper_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_code) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_code SmtTerm.str_to_code SmtType.Int
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_code_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_from_code) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type
        UserOp.str_from_code SmtTerm.str_from_code
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_str_from_code_eq, typeof_str_from_code_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_is_digit) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_is_digit SmtTerm.str_is_digit SmtType.Bool
        (by intro a; rfl)
        (by intro a; exact typeof_str_is_digit_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_int) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_int SmtTerm.str_to_int SmtType.Int
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_int_eq a)
        x rhs hTrans hSpine
  | Term._at_strings_stoi_non_digit x =>
      exact congTypeSpine_strings_stoi_non_digit_eq_has_bool_type
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_from_int) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type
        UserOp.str_from_int SmtTerm.str_from_int
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_str_from_int_eq, typeof_str_from_int_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_re) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_re SmtTerm.str_to_re SmtType.RegLan
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_re_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.re_range) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.re_range x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.re_concat) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.re_concat x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.re_inter) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.re_inter x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.re_union) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.re_union x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.re_diff) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.re_diff x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_in_re) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_in_re x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.re_mult) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.re_mult
        SmtTerm.re_mult
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_re_mult_eq, typeof_re_mult_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.re_plus) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.re_plus
        SmtTerm.re_plus
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_re_plus_eq, typeof_re_plus_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.re_exp n) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.re_exp n
        (fun a => SmtTerm.re_exp (__eo_to_smt n) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_re_exp_eq, typeof_re_exp_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.re_opt) x =>
      exact congTypeSpine_re_opt_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.re_comp) x =>
      exact congTypeSpine_re_comp_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x₁) x₂ =>
      exact congTypeSpine_seq_char_binop_eq_has_bool_type
        UserOp.re_range SmtTerm.re_range SmtType.RegLan
        (by intro a b; rfl)
        (by intro a b; exact typeof_re_range_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂ =>
      exact congTypeSpine_re_concat_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂ =>
      exact congTypeSpine_re_union_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂ =>
      exact congTypeSpine_re_inter_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂ =>
      exact congTypeSpine_re_diff_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x =>
      exact congTypeSpine_typecongr_indexed2_unop_eq_has_bool_type
        UserOp2.re_loop lo hi
        (fun a => SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_re_loop_eq, typeof_re_loop_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂ =>
      exact congTypeSpine_str_in_re_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_concat) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_concat x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_substr) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_substr x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_contains) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_contains x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_replace) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_replace x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_indexof) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_indexof x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_at) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_at x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_prefixof) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_prefixof x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_suffixof) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_suffixof x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_update) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_update x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_lt) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_lt x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_leq) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_leq x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_replace_all) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_replace_all x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_replace_re) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_replace_re x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_replace_re_all) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_replace_re_all x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.str_indexof_re) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.str_indexof_re x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp.seq_nth) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp.seq_nth x rhs (by rfl) hTrans
  | Term.Apply (Term.UOp UserOp._at_strings_num_occur) x =>
      exact congTypeSpine_uop_apply_none_head_eq_has_bool_type
        UserOp._at_strings_num_occur x rhs (by rfl) hTrans
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x₁) x₂ =>
      exact congTypeSpine_seq_binop_eq_has_bool_type UserOp.str_concat
        SmtTerm.str_concat
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_concat_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x₁) x₂ =>
      exact congTypeSpine_seq_binop_ret_eq_has_bool_type UserOp.str_contains
        SmtTerm.str_contains SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_contains_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x₁) x₂ =>
      exact congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.str_at
        SmtTerm.str_at
        (by intro a b; rfl)
        (by
          intro a b a' b' ha hb
          rw [typeof_str_at_eq, typeof_str_at_eq, ha, hb])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x₁) x₂ =>
      exact congTypeSpine_seq_binop_ret_eq_has_bool_type
        UserOp.str_prefixof SmtTerm.str_prefixof SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_prefixof_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x₁) x₂ =>
      exact congTypeSpine_seq_binop_ret_eq_has_bool_type
        UserOp.str_suffixof SmtTerm.str_suffixof SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_suffixof_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x₁) x₂ =>
      exact congTypeSpine_seq_char_binop_eq_has_bool_type
        UserOp.str_lt SmtTerm.str_lt SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_lt_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x₁) x₂ =>
      exact congTypeSpine_seq_char_binop_eq_has_bool_type
        UserOp.str_leq SmtTerm.str_leq SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_leq_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x₁) x₂ =>
      exact congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.seq_nth
        SmtTerm.seq_nth
        (by intro a b; rfl)
        (by
          intro a b a' b' ha hb
          rw [typeof_seq_nth_eq, typeof_seq_nth_eq, ha, hb])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term._at_strings_stoi_result x₁) x₂ =>
      exact congTypeSpine_strings_stoi_result_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term._at_strings_itos_result x₁) x₂ =>
      exact congTypeSpine_strings_itos_result_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂ =>
      exact congTypeSpine_strings_num_occur_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.str_substr
        SmtTerm.str_substr
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_substr_eq, typeof_str_substr_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.str_replace
        SmtTerm.str_replace
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_replace_eq, typeof_str_replace_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.str_indexof
        SmtTerm.str_indexof
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_indexof_eq, typeof_str_indexof_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.str_update
        SmtTerm.str_update
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_update_eq, typeof_str_update_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type
        UserOp.str_replace_all SmtTerm.str_replace_all
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_replace_all_eq, typeof_str_replace_all_eq, ha, hb,
            hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type
        UserOp.str_replace_re SmtTerm.str_replace_re
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_replace_re_eq, typeof_str_replace_re_eq, ha, hb,
            hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type
        UserOp.str_replace_re_all SmtTerm.str_replace_re_all
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_replace_re_all_eq, typeof_str_replace_re_all_eq,
            ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type
        UserOp.str_indexof_re SmtTerm.str_indexof_re
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_indexof_re_eq, typeof_str_indexof_re_eq, ha, hb,
            hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.seq_unit) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.seq_unit
        SmtTerm.seq_unit
        (by intro a; rfl)
        (by
          intro a b h
          rw [smtx_typeof_seq_unit_term_eq, smtx_typeof_seq_unit_term_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.set_is_empty) x =>
      exact congTypeSpine_set_is_empty_eq_has_bool_type
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.set_singleton) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.set_singleton
        SmtTerm.set_singleton
        (by intro a; rfl)
        (by
          intro a b h
          rw [smtx_typeof_set_singleton_term_eq, smtx_typeof_set_singleton_term_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.set_choose) x =>
      exact congTypeSpine_typecongr_eotype_unop_eq_has_bool_type
        UserOp.set_choose
        (by
          intro a b hSmt hEo
          have hChooseTy :
              __eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) a) =
                __eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) b) := by
            change __eo_typeof_set_choose (__eo_typeof a) =
              __eo_typeof_set_choose (__eo_typeof b)
            rw [hEo]
          change
            __smtx_typeof
                (SmtTerm.map_diff (__eo_to_smt a)
                  (SmtTerm.set_empty
                    (__eo_to_smt_set_elem_type
                      (__smtx_typeof (__eo_to_smt a))))) =
              __smtx_typeof
                (SmtTerm.map_diff (__eo_to_smt b)
                  (SmtTerm.set_empty
                    (__eo_to_smt_set_elem_type
                      (__smtx_typeof (__eo_to_smt b)))))
          rw [typeof_map_diff_eq, typeof_map_diff_eq, hSmt])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.set_is_singleton) x =>
      exact congTypeSpine_typecongr_eotype_unop_eq_has_bool_type
        UserOp.set_is_singleton
        (by
          intro a b hSmt hEo
          have hChooseTy :
              __eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) a) =
                __eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) b) := by
            change __eo_typeof_set_choose (__eo_typeof a) =
              __eo_typeof_set_choose (__eo_typeof b)
            rw [hEo]
          let T₁ :=
            __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt a))
          let T₂ :=
            __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt b))
          have hT : T₁ = T₂ := by
            dsimp [T₁, T₂]
            rw [hSmt]
          change
            __smtx_typeof
                (SmtTerm.eq (__eo_to_smt a)
                  (SmtTerm.set_singleton
                    (SmtTerm.map_diff (__eo_to_smt a)
                      (SmtTerm.set_empty T₁)))) =
              __smtx_typeof
                (SmtTerm.eq (__eo_to_smt b)
                  (SmtTerm.set_singleton
                    (SmtTerm.map_diff (__eo_to_smt b)
                      (SmtTerm.set_empty T₂))))
          rw [hT, typeof_eq_eq, typeof_eq_eq, smtx_typeof_set_singleton_term_eq,
            smtx_typeof_set_singleton_term_eq, typeof_map_diff_eq, typeof_map_diff_eq,
            hSmt])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x₁) x₂ =>
      exact congTypeSpine_set_binop_eq_has_bool_type UserOp.set_union
        SmtTerm.set_union
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_union_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x₁) x₂ =>
      exact congTypeSpine_set_binop_eq_has_bool_type UserOp.set_inter
        SmtTerm.set_inter
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_inter_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x₁) x₂ =>
      exact congTypeSpine_set_binop_eq_has_bool_type UserOp.set_minus
        SmtTerm.set_minus
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_minus_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x₁) x₂ =>
      exact congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.set_member
        SmtTerm.set_member
        (by intro a b; rfl)
        (by
          intro a b a' b' ha hb
          rw [typeof_set_member_eq, typeof_set_member_eq, ha, hb])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x₁) x₂ =>
      exact congTypeSpine_set_binop_ret_eq_has_bool_type UserOp.set_subset
        SmtTerm.set_subset SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_subset_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂ =>
      exact congTypeSpine_bv_concat_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp2 UserOp2.extract i j) x =>
      exact congTypeSpine_typecongr_indexed2_unop_eq_has_bool_type
        UserOp2.extract i j
        (fun a => SmtTerm.extract (__eo_to_smt i) (__eo_to_smt j) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_extract_eq, typeof_extract_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.repeat i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.repeat i
        (fun a => SmtTerm.repeat (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_repeat_eq, typeof_repeat_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x =>
      exact congTypeSpine_tuple_select_eq_has_bool_type
        idx x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂ =>
      exact congTypeSpine_bv_from_bools_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvredand) x =>
      exact congTypeSpine_bvredand_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvredor) x =>
      exact congTypeSpine_bvredor_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvnot) x =>
      exact congTypeSpine_bv_unop_eq_has_bool_type UserOp.bvnot SmtTerm.bvnot
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_39])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvneg) x =>
      exact congTypeSpine_bv_unop_eq_has_bool_type UserOp.bvneg SmtTerm.bvneg
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_47])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvnego) x =>
      exact congTypeSpine_bv_unop_ret_eq_has_bool_type UserOp.bvnego
        SmtTerm.bvnego SmtType.Bool
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_72])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.ubv_to_int) x =>
      exact congTypeSpine_bv_unop_ret_eq_has_bool_type UserOp.ubv_to_int
        SmtTerm.ubv_to_int SmtType.Int
        (by intro a; rfl)
        (by intro a; rw [smtx_typeof_ubv_to_int_term_eq])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.sbv_to_int) x =>
      exact congTypeSpine_bv_unop_ret_eq_has_bool_type UserOp.sbv_to_int
        SmtTerm.sbv_to_int SmtType.Int
        (by intro a; rfl)
        (by intro a; rw [smtx_typeof_sbv_to_int_term_eq])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvand SmtTerm.bvand
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_40])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvor SmtTerm.bvor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_41])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvnand) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvnand SmtTerm.bvnand
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_42])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvnor) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvnor SmtTerm.bvnor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_43])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvxor SmtTerm.bvxor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_44])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvxnor SmtTerm.bvxnor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_45])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvcomp
        SmtTerm.bvcomp (SmtType.BitVec 1)
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_46])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvadd SmtTerm.bvadd
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_48])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvmul SmtTerm.bvmul
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_49])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvudiv SmtTerm.bvudiv
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_50])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvurem SmtTerm.bvurem
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_51])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvsub SmtTerm.bvsub
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_52])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvsdiv SmtTerm.bvsdiv
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_53])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvsrem SmtTerm.bvsrem
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_54])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvsmod SmtTerm.bvsmod
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_55])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvult
        SmtTerm.bvult SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_56])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvule) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvule
        SmtTerm.bvule SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_57])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvugt
        SmtTerm.bvugt SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_58])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvuge
        SmtTerm.bvuge SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_59])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvslt
        SmtTerm.bvslt SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_60])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsle
        SmtTerm.bvsle SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_61])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsgt
        SmtTerm.bvsgt SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_62])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsge
        SmtTerm.bvsge SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_63])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvshl SmtTerm.bvshl
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_64])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvlshr SmtTerm.bvlshr
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_65])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvashr SmtTerm.bvashr
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_66])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.zero_extend i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.zero_extend i
        (fun a => SmtTerm.zero_extend (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_zero_extend_eq, typeof_zero_extend_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.sign_extend i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.sign_extend i
        (fun a => SmtTerm.sign_extend (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_sign_extend_eq, typeof_sign_extend_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.rotate_left i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.rotate_left i
        (fun a => SmtTerm.rotate_left (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_rotate_left_eq, typeof_rotate_left_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.rotate_right i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.rotate_right i
        (fun a => SmtTerm.rotate_right (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_rotate_right_eq, typeof_rotate_right_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvuaddo
        SmtTerm.bvuaddo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_71])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsaddo
        SmtTerm.bvsaddo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_73])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvumulo
        SmtTerm.bvumulo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_74])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsmulo
        SmtTerm.bvsmulo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_75])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvusubo
        SmtTerm.bvusubo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_76])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvssubo
        SmtTerm.bvssubo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_77])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsdivo
        SmtTerm.bvsdivo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_78])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x₁) x₂ =>
      exact congTypeSpine_bv_pred_to_bv_eq_has_bool_type UserOp.bvultbv
        SmtTerm.bvult
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_56])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x₁) x₂ =>
      exact congTypeSpine_bv_pred_to_bv_eq_has_bool_type UserOp.bvsltbv
        SmtTerm.bvslt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_60])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1._at_bit i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1._at_bit i
        (bvBitTerm (__eo_to_smt i))
        (by intro a; rfl)
        (by
          intro a b h
          rw [bvBitTerm, bvBitTerm, typeof_eq_eq, typeof_eq_eq,
            typeof_extract_eq,
            typeof_extract_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.int_to_bv w) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.int_to_bv w
        (fun a => SmtTerm.int_to_bv (__eo_to_smt w) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_int_to_bv_eq, typeof_int_to_bv_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.is c) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.is c
        (fun a => SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c)) a)
        (by intro a; rfl)
        (by
          intro a b h
          cases __eo_to_smt_tester (__eo_to_smt c) <;>
            simp [__smtx_typeof, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.forall) Term.__eo_List_nil) x =>
      exact False.elim
        (no_translation_of_eo_to_smt_none (t := Term.Apply
          (Term.Apply (Term.UOp UserOp.forall) Term.__eo_List_nil) x)
          (by rfl) hTrans)
  | Term.Apply (Term.Apply (Term.UOp UserOp.exists) Term.__eo_List_nil) x =>
      exact False.elim
        (no_translation_of_eo_to_smt_none (t := Term.Apply
          (Term.Apply (Term.UOp UserOp.exists) Term.__eo_List_nil) x)
          (by rfl) hTrans)
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) Term.__eo_List_nil) x =>
      exact False.elim
        (no_translation_of_eo_to_smt_none (t := Term.Apply
          (Term.Apply (Term.UOp UserOp.set_insert) Term.__eo_List_nil) x)
          (by rfl) hTrans)
  | lhs =>
      match hHead : (appSpineRev lhs).1 with
      | Term.Var (Term.String s) T =>
          exact congTypeSpine_appSpineRev_var_eq_has_bool_type
            s T lhs rhs hHead hTrans hSpine
      | Term.UConst i T =>
          exact congTypeSpine_appSpineRev_uconst_eq_has_bool_type
            i T lhs rhs hHead hTrans hSpine
      | Term.DtCons s d i =>
          exact congTypeSpine_appSpineRev_dtcons_eq_has_bool_type
            s d i lhs rhs hHead hTrans hSpine
      | Term.DtSel s d i j =>
          exact congTypeSpine_appSpineRev_dt_sel_eq_has_bool_type
            s d i j lhs rhs hHead hTrans hSpine
      | _ =>
          cases hSpine with
          | refl _ =>
              exact congTypeSpine_refl_eq_has_bool_type rhs hTrans
          | @app f g x y hFn hArg =>
              have hApp :
                  CongTypeSpine (Term.Apply f x) (Term.Apply g y) :=
                CongTypeSpine.app hFn hArg
              match f with
              | Term.Var (Term.String s) T =>
                  exact congTypeSpine_var_apply_eq_has_bool_type
                    s T x (Term.Apply g y) hTrans hApp
              | Term.Var name T =>
                  by_cases hName : ∃ s : native_String, name = Term.String s
                  · rcases hName with ⟨s, rfl⟩
                    exact congTypeSpine_var_apply_eq_has_bool_type
                      s T x (Term.Apply g y) hTrans hApp
                  ·
                    exact False.elim
                      (no_translation_of_eo_apply_none_head
                        (f := Term.Var name T) (x := x)
                        (eo_to_smt_apply_var_non_string_none_head
                          (by
                            intro s hs
                            exact hName ⟨s, hs⟩))
                        hTrans)
              | Term.UConst i T =>
                  exact congTypeSpine_uconst_apply_eq_has_bool_type
                    i T x (Term.Apply g y) hTrans hApp
              | Term.DtCons s d i =>
                  exact congTypeSpine_appSpineRev_dtcons_eq_has_bool_type
                    s d i (Term.Apply (Term.DtCons s d i) x)
                    (Term.Apply g y) (by rfl) hTrans hApp
              | Term.DtSel s d i j =>
                  exact congTypeSpine_dt_sel_eq_has_bool_type
                    s d i j x (Term.Apply g y) hTrans hApp
              | Term.UOp op =>
                  match hUnary : uopHasUnarySmtTranslation op with
                  | false =>
                      exact
                        congTypeSpine_uop_apply_not_unary_eq_has_bool_type
                          op x (Term.Apply g y) hUnary hTrans
                  | true =>
                      cases op <;> simp [uopHasUnarySmtTranslation] at hUnary
                      case not =>
                        exact congTypeSpine_not_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case _at_purify =>
                        exact congTypeSpine_purify_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case to_real =>
                        exact congTypeSpine_to_real_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case to_int =>
                        exact congTypeSpine_to_int_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case is_int =>
                        exact congTypeSpine_is_int_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case abs =>
                        exact congTypeSpine_abs_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case __eoo_neg_2 =>
                        exact congTypeSpine_uneg_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case int_pow2 =>
                        exact congTypeSpine_int_pow2_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case int_log2 =>
                        exact congTypeSpine_int_log2_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case int_ispow2 =>
                        exact congTypeSpine_int_ispow2_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case _at_int_div_by_zero =>
                        exact congTypeSpine_int_div_by_zero_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case _at_mod_by_zero =>
                        exact congTypeSpine_mod_by_zero_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case _at_bvsize =>
                        exact congTypeSpine_bvsize_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case str_len =>
                        exact congTypeSpine_seq_unop_ret_eq_has_bool_type
                          UserOp.str_len SmtTerm.str_len SmtType.Int
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_len_eq a)
                          x (Term.Apply g y) hTrans hApp
                      case str_rev =>
                        exact congTypeSpine_seq_unop_eq_has_bool_type
                          UserOp.str_rev SmtTerm.str_rev
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_rev_eq a)
                          x (Term.Apply g y) hTrans hApp
                      case str_to_lower =>
                        exact congTypeSpine_seq_char_unop_eq_has_bool_type
                          UserOp.str_to_lower SmtTerm.str_to_lower
                          (SmtType.Seq SmtType.Char)
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_lower_eq a)
                          x (Term.Apply g y) hTrans hApp
                      case str_to_upper =>
                        exact congTypeSpine_seq_char_unop_eq_has_bool_type
                          UserOp.str_to_upper SmtTerm.str_to_upper
                          (SmtType.Seq SmtType.Char)
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_upper_eq a)
                          x (Term.Apply g y) hTrans hApp
                      case str_to_code =>
                        exact congTypeSpine_seq_char_unop_eq_has_bool_type
                          UserOp.str_to_code SmtTerm.str_to_code SmtType.Int
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_code_eq a)
                          x (Term.Apply g y) hTrans hApp
                      case str_from_code =>
                        exact congTypeSpine_typecongr_unop_eq_has_bool_type
                          UserOp.str_from_code SmtTerm.str_from_code
                          (by intro a; rfl)
                          (by
                            intro a b h
                            rw [typeof_str_from_code_eq,
                              typeof_str_from_code_eq, h])
                          x (Term.Apply g y) hTrans hApp
                      case str_is_digit =>
                        exact congTypeSpine_seq_char_unop_eq_has_bool_type
                          UserOp.str_is_digit SmtTerm.str_is_digit
                          SmtType.Bool
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_is_digit_eq a)
                          x (Term.Apply g y) hTrans hApp
                      case str_to_int =>
                        exact congTypeSpine_seq_char_unop_eq_has_bool_type
                          UserOp.str_to_int SmtTerm.str_to_int SmtType.Int
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_int_eq a)
                          x (Term.Apply g y) hTrans hApp
                      case str_from_int =>
                        exact congTypeSpine_typecongr_unop_eq_has_bool_type
                          UserOp.str_from_int SmtTerm.str_from_int
                          (by intro a; rfl)
                          (by
                            intro a b h
                            rw [typeof_str_from_int_eq,
                              typeof_str_from_int_eq, h])
                          x (Term.Apply g y) hTrans hApp
                      case str_to_re =>
                        exact congTypeSpine_seq_char_unop_eq_has_bool_type
                          UserOp.str_to_re SmtTerm.str_to_re SmtType.RegLan
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_re_eq a)
                          x (Term.Apply g y) hTrans hApp
                      case _at_strings_stoi_non_digit =>
                        exact
                          congTypeSpine_strings_stoi_non_digit_eq_has_bool_type
                            x (Term.Apply g y) hTrans hApp
                      case re_mult =>
                        exact congTypeSpine_typecongr_unop_eq_has_bool_type
                          UserOp.re_mult SmtTerm.re_mult
                          (by intro a; rfl)
                          (by
                            intro a b h
                            rw [typeof_re_mult_eq, typeof_re_mult_eq, h])
                          x (Term.Apply g y) hTrans hApp
                      case re_plus =>
                        exact congTypeSpine_typecongr_unop_eq_has_bool_type
                          UserOp.re_plus SmtTerm.re_plus
                          (by intro a; rfl)
                          (by
                            intro a b h
                            rw [typeof_re_plus_eq, typeof_re_plus_eq, h])
                          x (Term.Apply g y) hTrans hApp
                      case re_opt =>
                        exact congTypeSpine_re_opt_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case re_comp =>
                        exact congTypeSpine_re_comp_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case seq_unit =>
                        exact congTypeSpine_typecongr_unop_eq_has_bool_type
                          UserOp.seq_unit SmtTerm.seq_unit
                          (by intro a; rfl)
                          (by
                            intro a b h
                            rw [smtx_typeof_seq_unit_term_eq,
                              smtx_typeof_seq_unit_term_eq, h])
                          x (Term.Apply g y) hTrans hApp
                      case set_is_empty =>
                        exact congTypeSpine_set_is_empty_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case set_singleton =>
                        exact congTypeSpine_typecongr_unop_eq_has_bool_type
                          UserOp.set_singleton SmtTerm.set_singleton
                          (by intro a; rfl)
                          (by
                            intro a b h
                            rw [smtx_typeof_set_singleton_term_eq,
                              smtx_typeof_set_singleton_term_eq, h])
                          x (Term.Apply g y) hTrans hApp
                      case set_choose =>
                        exact
                          congTypeSpine_typecongr_eotype_unop_eq_has_bool_type
                            UserOp.set_choose
                            (by
                              intro a b hSmt hEo
                              have hChooseTy :
                                  __eo_typeof
                                      (Term.Apply
                                        (Term.UOp UserOp.set_choose) a) =
                                    __eo_typeof
                                      (Term.Apply
                                        (Term.UOp UserOp.set_choose) b) := by
                                change __eo_typeof_set_choose (__eo_typeof a) =
                                  __eo_typeof_set_choose (__eo_typeof b)
                                rw [hEo]
                              change
                                __smtx_typeof
                                    (SmtTerm.map_diff (__eo_to_smt a)
                                      (SmtTerm.set_empty
                                        (__eo_to_smt_set_elem_type
                                          (__smtx_typeof (__eo_to_smt a))))) =
                                  __smtx_typeof
                                    (SmtTerm.map_diff (__eo_to_smt b)
                                      (SmtTerm.set_empty
                                        (__eo_to_smt_set_elem_type
                                          (__smtx_typeof (__eo_to_smt b)))))
                              rw [typeof_map_diff_eq, typeof_map_diff_eq,
                                hSmt])
                            x (Term.Apply g y) hTrans hApp
                      case set_is_singleton =>
                        exact
                          congTypeSpine_typecongr_eotype_unop_eq_has_bool_type
                            UserOp.set_is_singleton
                            (by
                              intro a b hSmt hEo
                              have hChooseTy :
                                  __eo_typeof
                                      (Term.Apply
                                        (Term.UOp UserOp.set_choose) a) =
                                    __eo_typeof
                                      (Term.Apply
                                        (Term.UOp UserOp.set_choose) b) := by
                                change __eo_typeof_set_choose (__eo_typeof a) =
                                  __eo_typeof_set_choose (__eo_typeof b)
                                rw [hEo]
                              let T₁ :=
                                __eo_to_smt_set_elem_type
                                  (__smtx_typeof (__eo_to_smt a))
                              let T₂ :=
                                __eo_to_smt_set_elem_type
                                  (__smtx_typeof (__eo_to_smt b))
                              have hT : T₁ = T₂ := by
                                dsimp [T₁, T₂]
                                rw [hSmt]
                              change
                                __smtx_typeof
                                    (SmtTerm.eq (__eo_to_smt a)
                                      (SmtTerm.set_singleton
                                        (SmtTerm.map_diff (__eo_to_smt a)
                                          (SmtTerm.set_empty T₁)))) =
                                  __smtx_typeof
                                    (SmtTerm.eq (__eo_to_smt b)
                                      (SmtTerm.set_singleton
                                        (SmtTerm.map_diff (__eo_to_smt b)
                                          (SmtTerm.set_empty T₂))))
                              rw [hT, typeof_eq_eq, typeof_eq_eq,
                                smtx_typeof_set_singleton_term_eq, smtx_typeof_set_singleton_term_eq,
                                typeof_map_diff_eq, typeof_map_diff_eq,
                                hSmt])
                            x (Term.Apply g y) hTrans hApp
                      case _at_div_by_zero =>
                        exact congTypeSpine_qdiv_by_zero_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case bvredand =>
                        exact congTypeSpine_bvredand_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case bvredor =>
                        exact congTypeSpine_bvredor_eq_has_bool_type
                          x (Term.Apply g y) hTrans hApp
                      case bvnot =>
                        exact congTypeSpine_bv_unop_eq_has_bool_type
                          UserOp.bvnot SmtTerm.bvnot
                          (by intro a; rfl)
                          (by intro a; rw [__smtx_typeof.eq_39])
                          x (Term.Apply g y) hTrans hApp
                      case bvneg =>
                        exact congTypeSpine_bv_unop_eq_has_bool_type
                          UserOp.bvneg SmtTerm.bvneg
                          (by intro a; rfl)
                          (by intro a; rw [__smtx_typeof.eq_47])
                          x (Term.Apply g y) hTrans hApp
                      case bvnego =>
                        exact congTypeSpine_bv_unop_ret_eq_has_bool_type
                          UserOp.bvnego SmtTerm.bvnego SmtType.Bool
                          (by intro a; rfl)
                          (by intro a; rw [__smtx_typeof.eq_72])
                          x (Term.Apply g y) hTrans hApp
                      case ubv_to_int =>
                        exact congTypeSpine_bv_unop_ret_eq_has_bool_type
                          UserOp.ubv_to_int SmtTerm.ubv_to_int SmtType.Int
                          (by intro a; rfl)
                          (by intro a; rw [smtx_typeof_ubv_to_int_term_eq])
                          x (Term.Apply g y) hTrans hApp
                      case sbv_to_int =>
                        exact congTypeSpine_bv_unop_ret_eq_has_bool_type
                          UserOp.sbv_to_int SmtTerm.sbv_to_int SmtType.Int
                          (by intro a; rfl)
                          (by intro a; rw [smtx_typeof_sbv_to_int_term_eq])
                          x (Term.Apply g y) hTrans hApp
                      case distinct =>
                        exact False.elim
                          (no_bool_eq_arg_of_distinct_translation
                            x y hTrans hArg)
              | Term.__eo_List =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.__eo_List) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.__eo_List_nil =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.__eo_List_nil) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.__eo_List_cons =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.__eo_List_cons) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.Bool =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.Bool) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.Boolean b =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.Boolean b) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply (SmtTerm.Boolean b)
                              (__eo_to_smt x)) = SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.Numeral n =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.Numeral n) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply (SmtTerm.Numeral n)
                              (__eo_to_smt x)) = SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.Rational q =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.Rational q) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply (SmtTerm.Rational q)
                              (__eo_to_smt x)) = SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.String s =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.String s) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply (SmtTerm.String s)
                              (__eo_to_smt x)) = SmtType.None
                        cases hValid : native_string_valid s <;>
                          cases __smtx_typeof (__eo_to_smt x) <;>
                            simp [__smtx_typeof, __smtx_typeof_apply,
                              hValid])
                      hTrans)
              | Term.Binary w n =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.Binary w n) (x := x) (by rfl)
                      (smt_apply_binary_typeof_none w n (__eo_to_smt x))
                      hTrans)
              | Term.Type =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.Type) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.Stuck =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.Stuck) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.FunType =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.FunType) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.DatatypeType s d =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.DatatypeType s d) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.DatatypeTypeRef s =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.DatatypeTypeRef s) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.DtcAppType A B =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.DtcAppType A B) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.USort i =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.USort i) (x := x) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hTrans)
              | Term.UOp1 UserOp1.zero_extend i =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1.zero_extend i
                    (fun a => SmtTerm.zero_extend (__eo_to_smt i) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_zero_extend_eq, typeof_zero_extend_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.sign_extend i =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1.sign_extend i
                    (fun a => SmtTerm.sign_extend (__eo_to_smt i) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_sign_extend_eq, typeof_sign_extend_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.rotate_left i =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1.rotate_left i
                    (fun a => SmtTerm.rotate_left (__eo_to_smt i) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_rotate_left_eq, typeof_rotate_left_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.rotate_right i =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1.rotate_right i
                    (fun a => SmtTerm.rotate_right (__eo_to_smt i) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_rotate_right_eq, typeof_rotate_right_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.repeat i =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1.repeat i
                    (fun a => SmtTerm.repeat (__eo_to_smt i) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_repeat_eq, typeof_repeat_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.re_exp n =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1.re_exp n
                    (fun a => SmtTerm.re_exp (__eo_to_smt n) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_re_exp_eq, typeof_re_exp_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1._at_bit i =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1._at_bit i
                    (bvBitTerm (__eo_to_smt i))
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [bvBitTerm, bvBitTerm, typeof_eq_eq,
                        typeof_eq_eq, typeof_extract_eq,
                        typeof_extract_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.int_to_bv w =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1.int_to_bv w
                    (fun a => SmtTerm.int_to_bv (__eo_to_smt w) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_int_to_bv_eq, typeof_int_to_bv_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.seq_empty T =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.UOp1 UserOp1.seq_empty T) (x := x)
                      (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply
                              (__eo_to_smt_seq_empty (__eo_to_smt_type T))
                              (__eo_to_smt x)) = SmtType.None
                        exact typeof_apply_eo_to_smt_seq_empty_eq_none
                          (__eo_to_smt_type T) (__eo_to_smt x))
                      hTrans)
              | Term.UOp1 UserOp1.set_empty T =>
                  exact False.elim
                    (no_translation_of_eo_apply_type_none
                      (f := Term.UOp1 UserOp1.set_empty T) (x := x)
                      (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply
                              (__eo_to_smt_set_empty (__eo_to_smt_type T))
                              (__eo_to_smt x)) = SmtType.None
                        exact typeof_apply_eo_to_smt_set_empty_eq_none
                          (__eo_to_smt_type T) (__eo_to_smt x))
                      hTrans)
              | Term.UOp1 UserOp1.is c =>
                  exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
                    UserOp1.is c
                    (fun a => SmtTerm.Apply
                      (__eo_to_smt_tester (__eo_to_smt c)) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      cases __eo_to_smt_tester (__eo_to_smt c) <;>
                        simp [__smtx_typeof, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x₁ =>
                  exact congTypeSpine_strings_stoi_result_eq_has_bool_type
                    x₁ x (Term.Apply g y) hTrans hApp
              | Term.Apply (Term.UOp UserOp._at_strings_itos_result) x₁ =>
                  exact congTypeSpine_strings_itos_result_eq_has_bool_type
                    x₁ x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.tuple_select idx =>
                  exact congTypeSpine_tuple_select_eq_has_bool_type
                    idx x (Term.Apply g y) hTrans hApp
              | Term.UOp2 UserOp2.extract i j =>
                  exact congTypeSpine_typecongr_indexed2_unop_eq_has_bool_type
                    UserOp2.extract i j
                    (fun a => SmtTerm.extract (__eo_to_smt i) (__eo_to_smt j) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_extract_eq, typeof_extract_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp2 UserOp2.re_loop lo hi =>
                  exact congTypeSpine_typecongr_indexed2_unop_eq_has_bool_type
                    UserOp2.re_loop lo hi
                    (fun a =>
                      SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi) a)
                    (by intro a; rfl)
                    (by
                      intro a b h
                      rw [typeof_re_loop_eq, typeof_re_loop_eq, h])
                    x (Term.Apply g y) hTrans hApp
              | Term.UOp1 UserOp1.update i =>
                  exact False.elim
                    (no_translation_of_eo_apply_none_head
                      (f := Term.UOp1 UserOp1.update i) (x := x)
                      (by rfl) hTrans)
              | Term.UOp1 UserOp1.tuple_update i =>
                  exact False.elim
                    (no_translation_of_eo_apply_none_head
                      (f := Term.UOp1 UserOp1.tuple_update i) (x := x)
                      (by rfl) hTrans)
              | Term.UOp2 UserOp2._at_const i j =>
                  cases hFn with
                  | refl _ =>
                      exact
                        congTypeSpine_same_generic_head_apply_eq_has_bool_type
                          (Term.UOp2 UserOp2._at_const i j)
                          x y
                          (by intro a; rfl)
                          (generic_apply_type_of_non_datatype_head
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_sel i j)
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_tester i j))
                          (generic_apply_type_of_non_datatype_head
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_sel i j)
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_tester i j))
                          hTrans hArg
              | Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n =>
                  cases hFn with
                  | refl _ =>
                      exact
                        congTypeSpine_same_generic_head_apply_eq_has_bool_type
                          (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n) x y
                          (by intro a; rfl)
                          (generic_apply_type_of_non_datatype_head
                            (eo_to_smt_at_bv_ne_dt_sel
                              (__eo_to_smt n) (__eo_to_smt w))
                            (eo_to_smt_at_bv_ne_dt_tester
                              (__eo_to_smt n) (__eo_to_smt w)))
                          (generic_apply_type_of_non_datatype_head
                            (eo_to_smt_at_bv_ne_dt_sel
                              (__eo_to_smt n) (__eo_to_smt w))
                            (eo_to_smt_at_bv_ne_dt_tester
                              (__eo_to_smt n) (__eo_to_smt w)))
                          hTrans hArg
                  | @app f₂ g₂ n₂ n₂' hFn₂ hHeadArg₂ =>
                      cases hFn₂ with
                      | refl _ =>
                          exact
                            congTypeSpine_int_to_bv_head_congr_eq_has_bool_type
                              w n n₂' x y hTrans hHeadArg₂ hArg
              | Term.UOp2 UserOp2._at_quantifiers_skolemize q idx =>
                  cases hFn with
                  | refl _ =>
                      exact
                        congTypeSpine_same_generic_head_apply_eq_has_bool_type
                          (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx)
                          x y
                          (by intro a; rfl)
                          (generic_apply_type_of_non_datatype_head
                            (eo_to_smt_quant_skolemize_top_ne_dt_sel q idx)
                            (eo_to_smt_quant_skolemize_top_ne_dt_tester q idx))
                          (generic_apply_type_of_non_datatype_head
                            (eo_to_smt_quant_skolemize_top_ne_dt_sel q idx)
                            (eo_to_smt_quant_skolemize_top_ne_dt_tester q idx))
                          hTrans hArg
              | Term.UOp3 UserOp3._at_re_unfold_pos_component str re idx =>
                  exact False.elim (hTrans (by
                    change
                      __smtx_typeof
                          (SmtTerm.Apply
                            (__eo_to_smt
                              (Term._at_re_unfold_pos_component str re idx))
                            (__eo_to_smt x)) =
                        SmtType.None
                    exact typeof_apply_re_unfold_top_eq_none str re idx x))
              | Term.UOp3 UserOp3._at_witness_string_length T len id =>
                  cases hFn with
                  | refl _ =>
                      exact
                        congTypeSpine_same_generic_head_apply_eq_has_bool_type
                          (Term.UOp3 UserOp3._at_witness_string_length
                            T len id)
                          x y
                          (by intro a; rfl)
                          (generic_apply_type_of_non_datatype_head
                            (eo_to_smt_witness_string_length_ne_dt_sel T len id)
                            (eo_to_smt_witness_string_length_ne_dt_tester T len id))
                            (generic_apply_type_of_non_datatype_head
                              (eo_to_smt_witness_string_length_ne_dt_sel T len id)
                              (eo_to_smt_witness_string_length_ne_dt_tester T len id))
                            hTrans hArg
              | Term.Apply f' z =>
                  match hHead' :
                    (appSpineRev ((Term.Apply f' z).Apply x)).1 with
                  | Term.Var (Term.String s) T =>
                      exact congTypeSpine_appSpineRev_var_eq_has_bool_type
                        s T ((Term.Apply f' z).Apply x) (Term.Apply g y)
                        hHead' hTrans hApp
                  | Term.UConst i T =>
                      exact congTypeSpine_appSpineRev_uconst_eq_has_bool_type
                        i T ((Term.Apply f' z).Apply x) (Term.Apply g y)
                        hHead' hTrans hApp
                  | Term.DtCons s d i =>
                      exact congTypeSpine_appSpineRev_dtcons_eq_has_bool_type
                        s d i ((Term.Apply f' z).Apply x) (Term.Apply g y)
                        hHead' hTrans hApp
                  | Term.DtSel s d i j =>
                      exact congTypeSpine_appSpineRev_dt_sel_eq_has_bool_type
                        s d i j ((Term.Apply f' z).Apply x)
                        (Term.Apply g y) hHead' hTrans hApp
                  | _ =>
                      by_cases hHeadTrans :
                          RuleProofs.eo_has_smt_translation
                            (Term.Apply f' z)
                      · have hFnBool :
                            RuleProofs.eo_has_bool_type
                              (mkEq (Term.Apply f' z) g) :=
                          congTypeSpine_eq_has_bool_type
                            (Term.Apply f' z) g hHeadTrans hFn
                        have hGTrans :
                            RuleProofs.eo_has_smt_translation g :=
                          by
                            have hFnTypes :=
                              RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                (Term.Apply f' z) g hFnBool
                            intro hNone
                            exact hFnTypes.2 (hFnTypes.1.trans hNone)
                        exact
                          congTypeSpine_generic_apply_eq_has_bool_type
                            (Term.Apply f' z) g x y hTrans
                            (eo_to_smt_apply_generic_of_has_smt_translation
                              (Term.Apply f' z) x hHeadTrans)
                            (eo_to_smt_apply_generic_of_has_smt_translation
                              g y hGTrans)
                            (generic_apply_type_of_non_datatype_head
                              (TranslationProofs.eo_to_smt_apply_ne_dt_sel f' z)
                              (TranslationProofs.eo_to_smt_apply_ne_dt_tester f' z))
                            (generic_apply_type_of_non_datatype_head
                              (by
                                intro s d i j hSel
                                cases hFn with
                                | refl _ =>
                                    exact
                                      TranslationProofs.eo_to_smt_apply_ne_dt_sel
                                        f' z s d i j hSel
                                | app hHead hArg =>
                                    exact
                                      TranslationProofs.eo_to_smt_apply_ne_dt_sel
                                        _ _ s d i j hSel)
                              (by
                                intro s d i hTester
                                cases hFn with
                                | refl _ =>
                                    exact
                                      TranslationProofs.eo_to_smt_apply_ne_dt_tester
                                        f' z s d i hTester
                                | app hHead hArg =>
                                    exact
                                      TranslationProofs.eo_to_smt_apply_ne_dt_tester
                                        _ _ s d i hTester))
                            hFnBool hArg
                      · match f' with
                        | Term.UOp op =>
                            cases op <;>
                              try
                                exact False.elim
                                  (hHeadTrans
                                    (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                      _ z x (by rfl) hTrans))
                            case eq =>
                              exact congTypeSpine_eq_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case and =>
                              exact congTypeSpine_and_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case or =>
                              exact congTypeSpine_or_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case imp =>
                              exact congTypeSpine_imp_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case xor =>
                              exact congTypeSpine_xor_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case plus =>
                              exact congTypeSpine_plus_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case neg =>
                              exact congTypeSpine_neg_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case mult =>
                              exact congTypeSpine_mult_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case lt =>
                              exact congTypeSpine_lt_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case leq =>
                              exact congTypeSpine_leq_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case gt =>
                              exact congTypeSpine_gt_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case geq =>
                              exact congTypeSpine_geq_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case div =>
                              exact congTypeSpine_div_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case mod =>
                              exact congTypeSpine_mod_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case div_total =>
                              exact congTypeSpine_div_total_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case mod_total =>
                              exact congTypeSpine_mod_total_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case divisible =>
                              exact congTypeSpine_divisible_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case select =>
                              exact
                                congTypeSpine_typecongr_binop_eq_has_bool_type
                                  UserOp.select SmtTerm.select
                                  (by intro a b; rfl)
                                  (by
                                    intro a b a' b' ha hb
                                    rw [typeof_select_eq, typeof_select_eq,
                                      ha, hb])
                                  z x (Term.Apply g y) hTrans hApp
                            case concat =>
                              exact congTypeSpine_bv_concat_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case qdiv =>
                              exact congTypeSpine_qdiv_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case qdiv_total =>
                              exact congTypeSpine_qdiv_total_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case str_concat =>
                              exact
                                congTypeSpine_seq_binop_eq_has_bool_type
                                  UserOp.str_concat SmtTerm.str_concat
                                  (by intro a b; rfl)
                                  (by intro a b; exact typeof_str_concat_eq a b)
                                  z x (Term.Apply g y) hTrans hApp
                            case str_contains =>
                              exact
                                congTypeSpine_seq_binop_ret_eq_has_bool_type
                                  UserOp.str_contains SmtTerm.str_contains
                                  SmtType.Bool
                                  (by intro a b; rfl)
                                  (by intro a b; exact typeof_str_contains_eq a b)
                                  z x (Term.Apply g y) hTrans hApp
                            case str_at =>
                              exact
                                congTypeSpine_typecongr_binop_eq_has_bool_type
                                  UserOp.str_at SmtTerm.str_at
                                  (by intro a b; rfl)
                                  (by
                                    intro a b a' b' ha hb
                                    rw [typeof_str_at_eq, typeof_str_at_eq,
                                      ha, hb])
                                  z x (Term.Apply g y) hTrans hApp
                            case str_prefixof =>
                              exact
                                congTypeSpine_seq_binop_ret_eq_has_bool_type
                                  UserOp.str_prefixof SmtTerm.str_prefixof
                                  SmtType.Bool
                                  (by intro a b; rfl)
                                  (by intro a b; exact typeof_str_prefixof_eq a b)
                                  z x (Term.Apply g y) hTrans hApp
                            case str_suffixof =>
                              exact
                                congTypeSpine_seq_binop_ret_eq_has_bool_type
                                  UserOp.str_suffixof SmtTerm.str_suffixof
                                  SmtType.Bool
                                  (by intro a b; rfl)
                                  (by intro a b; exact typeof_str_suffixof_eq a b)
                                  z x (Term.Apply g y) hTrans hApp
                            case str_lt =>
                              exact
                                congTypeSpine_seq_char_binop_eq_has_bool_type
                                  UserOp.str_lt SmtTerm.str_lt SmtType.Bool
                                  (by intro a b; rfl)
                                  (by intro a b; exact typeof_str_lt_eq a b)
                                  z x (Term.Apply g y) hTrans hApp
                            case str_leq =>
                              exact
                                congTypeSpine_seq_char_binop_eq_has_bool_type
                                  UserOp.str_leq SmtTerm.str_leq SmtType.Bool
                                  (by intro a b; rfl)
                                  (by intro a b; exact typeof_str_leq_eq a b)
                                  z x (Term.Apply g y) hTrans hApp
                            case seq_nth =>
                              exact
                                congTypeSpine_typecongr_binop_eq_has_bool_type
                                  UserOp.seq_nth SmtTerm.seq_nth
                                  (by intro a b; rfl)
                                  (by
                                    intro a b a' b' ha hb
                                    rw [typeof_seq_nth_eq, typeof_seq_nth_eq,
                                      ha, hb])
                                  z x (Term.Apply g y) hTrans hApp
                            case _at_array_deq_diff =>
                              exact
                                congTypeSpine_array_deq_diff_eq_has_bool_type
                                  z x (Term.Apply g y) hTrans hApp
                            case _at_strings_deq_diff =>
                              exact
                                congTypeSpine_strings_deq_diff_eq_has_bool_type
                                  z x (Term.Apply g y) hTrans hApp
                            case _at_strings_num_occur =>
                              exact congTypeSpine_strings_num_occur_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case _at_strings_num_occur_re =>
                              exact
                                congTypeSpine_strings_num_occur_re_eq_has_bool_type
                                  z x (Term.Apply g y) hTrans hApp
                            case _at_strings_stoi_result =>
                              exact
                                congTypeSpine_strings_stoi_result_eq_has_bool_type
                                  z x (Term.Apply g y) hTrans hApp
                            case _at_strings_itos_result =>
                              exact
                                congTypeSpine_strings_itos_result_eq_has_bool_type
                                  z x (Term.Apply g y) hTrans hApp
                            case re_range =>
                              exact
                                congTypeSpine_seq_char_binop_eq_has_bool_type
                                  UserOp.re_range SmtTerm.re_range
                                  SmtType.RegLan
                                  (by intro a b; rfl)
                                  (by intro a b; exact typeof_re_range_eq a b)
                                  z x (Term.Apply g y) hTrans hApp
                            case re_concat =>
                              exact congTypeSpine_re_concat_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case re_union =>
                              exact congTypeSpine_re_union_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case re_inter =>
                              exact congTypeSpine_re_inter_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case re_diff =>
                              exact congTypeSpine_re_diff_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case str_in_re =>
                              exact congTypeSpine_str_in_re_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case set_union =>
                              exact congTypeSpine_set_binop_eq_has_bool_type
                                UserOp.set_union SmtTerm.set_union
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_set_union_eq a b)
                                z x (Term.Apply g y) hTrans hApp
                            case set_inter =>
                              exact congTypeSpine_set_binop_eq_has_bool_type
                                UserOp.set_inter SmtTerm.set_inter
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_set_inter_eq a b)
                                z x (Term.Apply g y) hTrans hApp
                            case set_minus =>
                              exact congTypeSpine_set_binop_eq_has_bool_type
                                UserOp.set_minus SmtTerm.set_minus
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_set_minus_eq a b)
                                z x (Term.Apply g y) hTrans hApp
                            case set_member =>
                              exact
                                congTypeSpine_typecongr_binop_eq_has_bool_type
                                  UserOp.set_member SmtTerm.set_member
                                  (by intro a b; rfl)
                                  (by
                                    intro a b a' b' ha hb
                                    rw [typeof_set_member_eq,
                                      typeof_set_member_eq, ha, hb])
                                  z x (Term.Apply g y) hTrans hApp
                            case set_subset =>
                              exact congTypeSpine_set_binop_ret_eq_has_bool_type
                                UserOp.set_subset SmtTerm.set_subset
                                SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_set_subset_eq a b)
                                z x (Term.Apply g y) hTrans hApp
                            case _at_sets_deq_diff =>
                              exact
                                congTypeSpine_sets_deq_diff_eq_has_bool_type
                                  z x (Term.Apply g y) hTrans hApp
                            case _at_from_bools =>
                              exact congTypeSpine_bv_from_bools_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case bvand =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvand SmtTerm.bvand
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_40])
                                z x (Term.Apply g y) hTrans hApp
                            case bvor =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvor SmtTerm.bvor
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_41])
                                z x (Term.Apply g y) hTrans hApp
                            case bvnand =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvnand SmtTerm.bvnand
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_42])
                                z x (Term.Apply g y) hTrans hApp
                            case bvnor =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvnor SmtTerm.bvnor
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_43])
                                z x (Term.Apply g y) hTrans hApp
                            case bvxor =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvxor SmtTerm.bvxor
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_44])
                                z x (Term.Apply g y) hTrans hApp
                            case bvxnor =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvxnor SmtTerm.bvxnor
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_45])
                                z x (Term.Apply g y) hTrans hApp
                            case bvcomp =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvcomp SmtTerm.bvcomp
                                (SmtType.BitVec 1)
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_46])
                                z x (Term.Apply g y) hTrans hApp
                            case bvadd =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvadd SmtTerm.bvadd
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_48])
                                z x (Term.Apply g y) hTrans hApp
                            case bvmul =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvmul SmtTerm.bvmul
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_49])
                                z x (Term.Apply g y) hTrans hApp
                            case bvudiv =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvudiv SmtTerm.bvudiv
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_50])
                                z x (Term.Apply g y) hTrans hApp
                            case bvurem =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvurem SmtTerm.bvurem
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_51])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsub =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvsub SmtTerm.bvsub
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_52])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsdiv =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvsdiv SmtTerm.bvsdiv
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_53])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsrem =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvsrem SmtTerm.bvsrem
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_54])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsmod =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvsmod SmtTerm.bvsmod
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_55])
                                z x (Term.Apply g y) hTrans hApp
                            case bvult =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvult SmtTerm.bvult SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_56])
                                z x (Term.Apply g y) hTrans hApp
                            case bvule =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvule SmtTerm.bvule SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_57])
                                z x (Term.Apply g y) hTrans hApp
                            case bvugt =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvugt SmtTerm.bvugt SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_58])
                                z x (Term.Apply g y) hTrans hApp
                            case bvuge =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvuge SmtTerm.bvuge SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_59])
                                z x (Term.Apply g y) hTrans hApp
                            case bvslt =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvslt SmtTerm.bvslt SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_60])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsle =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvsle SmtTerm.bvsle SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_61])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsgt =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvsgt SmtTerm.bvsgt SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_62])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsge =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvsge SmtTerm.bvsge SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_63])
                                z x (Term.Apply g y) hTrans hApp
                            case bvshl =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvshl SmtTerm.bvshl
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_64])
                                z x (Term.Apply g y) hTrans hApp
                            case bvlshr =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvlshr SmtTerm.bvlshr
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_65])
                                z x (Term.Apply g y) hTrans hApp
                            case bvashr =>
                              exact congTypeSpine_bv_binop_eq_has_bool_type
                                UserOp.bvashr SmtTerm.bvashr
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_66])
                                z x (Term.Apply g y) hTrans hApp
                            case bvuaddo =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvuaddo SmtTerm.bvuaddo SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_71])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsaddo =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvsaddo SmtTerm.bvsaddo SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_73])
                                z x (Term.Apply g y) hTrans hApp
                            case bvumulo =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvumulo SmtTerm.bvumulo SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_74])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsmulo =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvsmulo SmtTerm.bvsmulo SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_75])
                                z x (Term.Apply g y) hTrans hApp
                            case bvusubo =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvusubo SmtTerm.bvusubo SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_76])
                                z x (Term.Apply g y) hTrans hApp
                            case bvssubo =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvssubo SmtTerm.bvssubo SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_77])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsdivo =>
                              exact congTypeSpine_bv_binop_ret_eq_has_bool_type
                                UserOp.bvsdivo SmtTerm.bvsdivo SmtType.Bool
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_78])
                                z x (Term.Apply g y) hTrans hApp
                            case bvultbv =>
                              exact congTypeSpine_bv_pred_to_bv_eq_has_bool_type
                                UserOp.bvultbv SmtTerm.bvult
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_56])
                                z x (Term.Apply g y) hTrans hApp
                            case bvsltbv =>
                              exact congTypeSpine_bv_pred_to_bv_eq_has_bool_type
                                UserOp.bvsltbv SmtTerm.bvslt
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_60])
                                z x (Term.Apply g y) hTrans hApp
                            case tuple =>
                              exact congTypeSpine_tuple_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case set_insert =>
                              exact congTypeSpine_set_insert_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case «forall» =>
                              exact congTypeSpine_forall_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                            case «exists» =>
                              exact congTypeSpine_exists_eq_has_bool_type
                                z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.ite) c =>
                            exact congTypeSpine_ite_eq_has_bool_type
                              c z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.bvite) c =>
                            exact congTypeSpine_bvite_eq_has_bool_type
                              c z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.store) a =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.store SmtTerm.store
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_store_eq, typeof_store_eq,
                                    ha, hb, hc])
                                a z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.str_substr) s =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.str_substr SmtTerm.str_substr
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_str_substr_eq,
                                    typeof_str_substr_eq, ha, hb, hc])
                                s z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.str_replace) s =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.str_replace SmtTerm.str_replace
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_str_replace_eq,
                                    typeof_str_replace_eq, ha, hb, hc])
                                s z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.str_indexof) s =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.str_indexof SmtTerm.str_indexof
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_str_indexof_eq,
                                    typeof_str_indexof_eq, ha, hb, hc])
                                s z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.str_update) s =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.str_update SmtTerm.str_update
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_str_update_eq,
                                    typeof_str_update_eq, ha, hb, hc])
                                s z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.str_replace_all) s =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.str_replace_all SmtTerm.str_replace_all
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_str_replace_all_eq,
                                    typeof_str_replace_all_eq, ha, hb, hc])
                                s z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.str_replace_re) s =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.str_replace_re SmtTerm.str_replace_re
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_str_replace_re_eq,
                                    typeof_str_replace_re_eq, ha, hb, hc])
                                s z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.str_replace_re_all) s =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.str_replace_re_all
                                SmtTerm.str_replace_re_all
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_str_replace_re_all_eq,
                                    typeof_str_replace_re_all_eq, ha, hb, hc])
                                s z x (Term.Apply g y) hTrans hApp
                        | Term.Apply (Term.UOp UserOp.str_indexof_re) s =>
                            exact
                              congTypeSpine_typecongr_ternop_eq_has_bool_type
                                UserOp.str_indexof_re SmtTerm.str_indexof_re
                                (by intro a b c; rfl)
                                (by
                                  intro a b c a' b' c' ha hb hc
                                  rw [typeof_str_indexof_re_eq,
                                    typeof_str_indexof_re_eq, ha, hb, hc])
                                s z x (Term.Apply g y) hTrans hApp
                        | Term.UOp1 UserOp1.update i =>
                            exact
                              congTypeSpine_typecongr_indexed_binary_uop1_eq_has_bool_type
                                UserOp1.update i
                                (fun a b =>
                                  __eo_to_smt_updater (__eo_to_smt i) a b)
                                (by intro a b; rfl)
                                (by
                                  intro a b a' b' ha hb
                                  exact eo_to_smt_updater_type_congr
                                    (__eo_to_smt i) a b a' b' ha hb)
                                z x (Term.Apply g y) hTrans hApp
                        | Term.UOp1 UserOp1.tuple_update i =>
                            exact congTypeSpine_tuple_update_eq_has_bool_type
                              i z x (Term.Apply g y) hTrans hApp
                        | Term.UOp1 op i =>
                            cases op <;>
                              try
                                exact False.elim
                                  (hHeadTrans
                                    (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                      _ z x (by rfl) hTrans))
                            case update =>
                              exact
                                congTypeSpine_typecongr_indexed_binary_uop1_eq_has_bool_type
                                  UserOp1.update i
                                  (fun a b =>
                                    __eo_to_smt_updater (__eo_to_smt i) a b)
                                  (by intro a b; rfl)
                                  (by
                                    intro a b a' b' ha hb
                                    exact eo_to_smt_updater_type_congr
                                      (__eo_to_smt i) a b a' b' ha hb)
                                  z x (Term.Apply g y) hTrans hApp
                            case tuple_update =>
                              exact congTypeSpine_tuple_update_eq_has_bool_type
                                i z x (Term.Apply g y) hTrans hApp
                        | Term.UOp2 op i j =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.UOp2 op i j) z x (by rfl) hTrans))
                        | Term.UOp3 op i j k =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.UOp3 op i j k) z x (by rfl) hTrans))
                        | Term.__eo_List =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.__eo_List z x (by rfl) hTrans))
                        | Term.__eo_List_nil =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.__eo_List_nil z x (by rfl) hTrans))
                        | Term.__eo_List_cons =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.__eo_List_cons z x (by rfl) hTrans))
                        | Term.Bool =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.Bool z x (by rfl) hTrans))
                        | Term.Boolean b =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Boolean b) z x (by rfl) hTrans))
                        | Term.Numeral n =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Numeral n) z x (by rfl) hTrans))
                        | Term.Rational r =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Rational r) z x (by rfl) hTrans))
                        | Term.String s =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.String s) z x (by rfl) hTrans))
                        | Term.Binary w n =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Binary w n) z x (by rfl) hTrans))
                        | Term.Type =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.Type z x (by rfl) hTrans))
                        | Term.Stuck =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.Stuck z x (by rfl) hTrans))
                        | Term.Apply f0 a =>
                            cases f0 <;>
                              try
                                exact False.elim
                                  (hHeadTrans
                                    (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                      _ z x (by rfl) hTrans))
                            case UOp op =>
                              cases op <;>
                                try
                                  exact False.elim
                                    (hHeadTrans
                                      (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                        _ z x (by rfl) hTrans))
                              case ite =>
                                exact congTypeSpine_ite_eq_has_bool_type
                                  a z x (Term.Apply g y) hTrans hApp
                              case bvite =>
                                exact congTypeSpine_bvite_eq_has_bool_type
                                  a z x (Term.Apply g y) hTrans hApp
                              case store =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.store SmtTerm.store
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_store_eq, typeof_store_eq,
                                        ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case str_substr =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.str_substr SmtTerm.str_substr
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_str_substr_eq,
                                        typeof_str_substr_eq, ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case _at_strings_occur_index =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp._at_strings_occur_index
                                    SmtTerm._at_strings_occur_index
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_at_strings_occur_index_eq,
                                        typeof_at_strings_occur_index_eq,
                                        ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case _at_strings_occur_index_re =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp._at_strings_occur_index_re
                                    SmtTerm._at_strings_occur_index_re
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_at_strings_occur_index_re_eq,
                                        typeof_at_strings_occur_index_re_eq,
                                        ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case str_replace =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.str_replace SmtTerm.str_replace
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_str_replace_eq,
                                        typeof_str_replace_eq, ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case str_indexof =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.str_indexof SmtTerm.str_indexof
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_str_indexof_eq,
                                        typeof_str_indexof_eq, ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case str_update =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.str_update SmtTerm.str_update
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_str_update_eq,
                                        typeof_str_update_eq, ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case str_replace_all =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.str_replace_all SmtTerm.str_replace_all
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_str_replace_all_eq,
                                        typeof_str_replace_all_eq, ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case str_replace_re =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.str_replace_re SmtTerm.str_replace_re
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_str_replace_re_eq,
                                        typeof_str_replace_re_eq, ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case str_replace_re_all =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.str_replace_re_all
                                    SmtTerm.str_replace_re_all
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_str_replace_re_all_eq,
                                        typeof_str_replace_re_all_eq, ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                              case str_indexof_re =>
                                exact
                                  congTypeSpine_typecongr_ternop_eq_has_bool_type
                                    UserOp.str_indexof_re SmtTerm.str_indexof_re
                                    (by intro a b c; rfl)
                                    (by
                                      intro a b c a' b' c' ha hb hc
                                      rw [typeof_str_indexof_re_eq,
                                        typeof_str_indexof_re_eq, ha, hb, hc])
                                    a z x (Term.Apply g y) hTrans hApp
                            case Apply f1 b =>
                              cases f1 <;>
                                try
                                  exact False.elim
                                    (hHeadTrans
                                      (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                        _ z x (by rfl) hTrans))
                              case UOp op =>
                                cases op <;>
                                  try
                                    exact False.elim
                                      (hHeadTrans
                                        (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                          _ z x (by rfl) hTrans))
                                case _at_strings_replace_all_result =>
                                  exact
                                    congTypeSpine_typecongr_quadop_eq_has_bool_type
                                      UserOp._at_strings_replace_all_result
                                      (fun a b c d =>
                                        SmtTerm.str_replace_all
                                          (SmtTerm.str_substr a
                                            (SmtTerm._at_strings_occur_index
                                              a b d)
                                            (SmtTerm.str_len a))
                                          b c)
                                      (by intro a b c d; rfl)
                                      (by
                                        intro a b c d a' b' c' d' ha hb hc hd
                                        rw [typeof_str_replace_all_eq,
                                          typeof_str_replace_all_eq,
                                          typeof_str_substr_eq,
                                          typeof_str_substr_eq,
                                          typeof_str_len_eq,
                                          typeof_str_len_eq,
                                          typeof_at_strings_occur_index_eq,
                                          typeof_at_strings_occur_index_eq,
                                          ha, hb, hc, hd])
                                      b a z x (Term.Apply g y) hTrans hApp
                                case _at_strings_replace_re_all_result =>
                                  exact
                                    congTypeSpine_typecongr_quadop_eq_has_bool_type
                                      UserOp._at_strings_replace_re_all_result
                                      (fun a b c d =>
                                        SmtTerm.str_replace_re_all
                                          (SmtTerm.str_substr a
                                            (SmtTerm._at_strings_occur_index_re
                                              a b d)
                                            (SmtTerm.str_len a))
                                          b c)
                                      (by intro a b c d; rfl)
                                      (by
                                        intro a b c d a' b' c' d' ha hb hc hd
                                        rw [typeof_str_replace_re_all_eq,
                                          typeof_str_replace_re_all_eq,
                                          typeof_str_substr_eq,
                                          typeof_str_substr_eq,
                                          typeof_str_len_eq,
                                          typeof_str_len_eq,
                                          typeof_at_strings_occur_index_re_eq,
                                          typeof_at_strings_occur_index_re_eq,
                                          ha, hb, hc, hd])
                                      b a z x (Term.Apply g y) hTrans hApp
                        | Term.FunType =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.FunType z x (by rfl) hTrans))
                        | Term.Var name T =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Var name T) z x (by rfl) hTrans))
                        | Term.DatatypeType s d =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DatatypeType s d) z x (by rfl) hTrans))
                        | Term.DatatypeTypeRef s =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DatatypeTypeRef s) z x (by rfl) hTrans))
                        | Term.DtcAppType T U =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DtcAppType T U) z x (by rfl) hTrans))
                        | Term.DtCons s d i =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DtCons s d i) z x (by rfl) hTrans))
                        | Term.DtSel s d i j =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DtSel s d i j) z x (by rfl) hTrans))
                        | Term.USort u =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.USort u) z x (by rfl) hTrans))
                        | Term.UConst u T =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.UConst u T) z x (by rfl) hTrans))

/--
The remaining semantic core for congruence: a syntactic congruence spine
preserves SMT equality in a total typed model.
-/
theorem congTrueSpine_refl_eq_true
    (M : SmtModel) (t : Term) :
    RuleProofs.eo_has_bool_type (mkEq t t) ->
    eo_interprets M (mkEq t t) true := by
  intro hEqBool
  exact RuleProofs.eo_interprets_eq_of_rel M t t hEqBool
    (RuleProofs.smt_value_rel_refl _)


end CongSupport
