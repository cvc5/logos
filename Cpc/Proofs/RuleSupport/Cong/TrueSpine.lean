module

public import Cpc.Proofs.RuleSupport.Cong.TypeSpine
import all Cpc.Proofs.RuleSupport.Cong.TypeSpine

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

theorem congTrueSpine_eq_true
    (M : SmtModel) (hM : model_wf M) (t rhs : Term) :
    NotTopLevelQuantifier t ->
    RuleProofs.eo_has_bool_type (mkEq t rhs) ->
    CongTrueSpine M t rhs ->
    eo_interprets M (mkEq t rhs) true := by
  intro hNotQuant hEqBool hSpine
  match t with
  | Term.Apply (Term.UOp UserOp.not) x =>
      exact congTrueSpine_not_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.ite) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.ite) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.or) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.or) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.and) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.and) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.imp) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.imp) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.xor) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.xor) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.eq) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.eq) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.Int) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.Int x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.Real) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.Real x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.BitVec) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.BitVec x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.Char) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.Char x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.Seq) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.Seq x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.Array) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.Array x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.RegLan) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.RegLan x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.UnitTuple) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.UnitTuple x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.Tuple) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.Tuple x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.Set) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.Set x rhs (by rfl) hEqBool
  | Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂ =>
      exact congTrueSpine_eq_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e =>
      exact congTrueSpine_ite_eq_true M hM c t e rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e =>
      exact congTrueSpine_bvite_eq_true M hM c t e rhs hEqBool hSpine
  | Term.Apply (Term.Var (Term.String s) T) x =>
      exact congTrueSpine_var_apply_eq_true M hM s T x rhs hEqBool hSpine
  | Term.Apply (Term.UConst i T) x =>
      exact congTrueSpine_uconst_apply_eq_true M hM i T x rhs hEqBool hSpine
  | Term.Apply (Term.DtSel s d i j) x =>
      exact congTrueSpine_dt_sel_eq_true M hM
        s d i j x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂ =>
      exact congTrueSpine_var_apply_apply_eq_true M hM
        s T x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂ =>
      exact congTrueSpine_uconst_apply_apply_eq_true M hM
        i T x₁ x₂ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃ =>
      exact congTrueSpine_var_apply_apply_apply_eq_true M hM
        s T x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃ =>
      exact congTrueSpine_uconst_apply_apply_apply_eq_true M hM
        i T x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
      x₄ =>
      exact congTrueSpine_var_apply_apply_apply_apply_eq_true M hM
        s T x₁ x₂ x₃ x₄ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
      x₄ =>
      exact congTrueSpine_uconst_apply_apply_apply_apply_eq_true M hM
        i T x₁ x₂ x₃ x₄ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
        x₄) x₅ =>
      exact congTrueSpine_var_apply_apply_apply_apply_apply_eq_true M hM
        s T x₁ x₂ x₃ x₄ x₅ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        x₄) x₅ =>
      exact congTrueSpine_uconst_apply_apply_apply_apply_apply_eq_true M hM
        i T x₁ x₂ x₃ x₄ x₅ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
          x₄) x₅) x₆ =>
      exact congTrueSpine_var_apply_apply_apply_apply_apply_apply_eq_true M hM
        s T x₁ x₂ x₃ x₄ x₅ x₆ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
          x₄) x₅) x₆ =>
      exact congTrueSpine_uconst_apply_apply_apply_apply_apply_apply_eq_true M hM
        i T x₁ x₂ x₃ x₄ x₅ x₆ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂ =>
      exact congTrueSpine_and_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂ =>
      exact congTrueSpine_or_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂ =>
      exact congTrueSpine_imp_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂ =>
      exact congTrueSpine_xor_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.plus) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.plus) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.neg) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.neg) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.mult) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.mult) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.lt) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.lt) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.leq) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.leq) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.gt) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.gt) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.geq) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.geq) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂ =>
      exact congTrueSpine_plus_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂ =>
      exact congTrueSpine_neg_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂ =>
      exact congTrueSpine_mult_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂ =>
      exact congTrueSpine_lt_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂ =>
      exact congTrueSpine_leq_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂ =>
      exact congTrueSpine_gt_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂ =>
      exact congTrueSpine_geq_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.to_real) x =>
      exact congTrueSpine_to_real_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.to_int) x =>
      exact congTrueSpine_to_int_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.is_int) x =>
      exact congTrueSpine_is_int_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.abs) x =>
      exact congTrueSpine_abs_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.__eoo_neg_2) x =>
      exact congTrueSpine_uneg_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.div) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.div) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.mod) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.mod) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.div_total) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.div_total) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.mod_total) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.mod_total) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.UOp UserOp.divisible) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_apply_none_head
          (f := Term.UOp UserOp.divisible) (x := x) (rhs := rhs) (by rfl)
          hEqBool)
  | Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂ =>
      exact congTrueSpine_div_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂ =>
      exact congTrueSpine_mod_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂ =>
      exact congTrueSpine_div_total_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂ =>
      exact congTrueSpine_mod_total_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂ =>
      exact congTrueSpine_divisible_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.int_pow2) x =>
      exact congTrueSpine_int_pow2_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.int_log2) x =>
      exact congTrueSpine_int_log2_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.int_ispow2) x =>
      exact congTrueSpine_int_ispow2_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x =>
      exact congTrueSpine_int_div_by_zero_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp._at_mod_by_zero) x =>
      exact congTrueSpine_mod_by_zero_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.select) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.select x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.store) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.store x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp._at_bvsize) x =>
      exact congTrueSpine_bvsize_eq_true M x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.qdiv) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.qdiv x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.qdiv_total) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.qdiv_total x rhs (by rfl) hEqBool
  | Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂ =>
      exact congTrueSpine_qdiv_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂ =>
      exact congTrueSpine_qdiv_total_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp._at_div_by_zero) x =>
      exact congTrueSpine_qdiv_by_zero_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_len) x =>
      exact congTrueSpine_seq_unop_ret_eq_true M hM UserOp.str_len
        SmtTerm.str_len SmtType.Int __smtx_model_eval_str_len
        (by intro a; rfl)
        (by intro a; exact typeof_str_len_eq a)
        (by intro a; rw [smtx_eval_str_len_term_eq])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_rev) x =>
      exact congTrueSpine_seq_unop_eq_true M hM UserOp.str_rev
        SmtTerm.str_rev __smtx_model_eval_str_rev
        (by intro a; rfl)
        (by intro a; exact typeof_str_rev_eq a)
        (by intro a; rw [__smtx_model_eval.eq_89])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_lower) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_lower SmtTerm.str_to_lower (SmtType.Seq SmtType.Char)
        __smtx_model_eval_str_to_lower
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_lower_eq a)
        (by intro a; rw [__smtx_model_eval.eq_91])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_upper) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_upper SmtTerm.str_to_upper (SmtType.Seq SmtType.Char)
        __smtx_model_eval_str_to_upper
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_upper_eq a)
        (by intro a; rw [__smtx_model_eval.eq_92])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_code) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_code SmtTerm.str_to_code SmtType.Int
        __smtx_model_eval_str_to_code
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_code_eq a)
        (by intro a; rw [smtx_eval_str_to_code_term_eq])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_from_code) x =>
      exact congTrueSpine_non_reg_unop_eq_true M hM
        UserOp.str_from_code SmtTerm.str_from_code
        __smtx_model_eval_str_from_code
        (by intro a; rfl)
        (int_ret_unop_args_non_reg_of_non_none SmtTerm.str_from_code
          (SmtType.Seq SmtType.Char)
          (by intro a; exact typeof_str_from_code_eq a))
        (by intro a; rw [__smtx_model_eval.eq_94])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_is_digit) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_is_digit SmtTerm.str_is_digit SmtType.Bool
        __smtx_model_eval_str_is_digit
        (by intro a; rfl)
        (by intro a; exact typeof_str_is_digit_eq a)
        (by intro a; rw [__smtx_model_eval.eq_95])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_int) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_int SmtTerm.str_to_int SmtType.Int
        __smtx_model_eval_str_to_int
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_int_eq a)
        (by intro a; rw [__smtx_model_eval.eq_96])
        x rhs hEqBool hSpine
  | Term._at_strings_stoi_non_digit x =>
      exact congTrueSpine_strings_stoi_non_digit_eq_true M hM
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_from_int) x =>
      exact congTrueSpine_non_reg_unop_eq_true M hM
        UserOp.str_from_int SmtTerm.str_from_int
        __smtx_model_eval_str_from_int
        (by intro a; rfl)
        (int_ret_unop_args_non_reg_of_non_none SmtTerm.str_from_int
          (SmtType.Seq SmtType.Char)
          (by intro a; exact typeof_str_from_int_eq a))
        (by intro a; rw [__smtx_model_eval.eq_97])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_re) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_re SmtTerm.str_to_re SmtType.RegLan
        __smtx_model_eval_str_to_re
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_re_eq a)
        (by intro a; rw [__smtx_model_eval.eq_107])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.re_range) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.re_range x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.re_concat) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.re_concat x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.re_inter) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.re_inter x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.re_union) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.re_union x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.re_diff) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.re_diff x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_in_re) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_in_re x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp1 UserOp1.re_exp n) x =>
      exact congTrueSpine_re_exp_eq_true M hM n x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.re_mult) x =>
      exact congTrueSpine_re_mult_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.re_plus) x =>
      exact congTrueSpine_re_plus_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.re_opt) x =>
      exact congTrueSpine_re_opt_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.re_comp) x =>
      exact congTrueSpine_re_comp_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x₁) x₂ =>
      exact congTrueSpine_seq_char_binop_eq_true M hM UserOp.re_range
        SmtTerm.re_range SmtType.RegLan __smtx_model_eval_re_range
        (by intro a b; rfl)
        (by intro a b; exact typeof_re_range_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_113])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂ =>
      exact congTrueSpine_re_concat_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂ =>
      exact congTrueSpine_re_union_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂ =>
      exact congTrueSpine_re_inter_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂ =>
      exact congTrueSpine_re_diff_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x =>
      exact congTrueSpine_re_loop_eq_true M hM lo hi x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂ =>
      exact congTrueSpine_str_in_re_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.seq_unit) x =>
      exact congTrueSpine_non_reg_unop_eq_true M hM UserOp.seq_unit
        SmtTerm.seq_unit
        (fun a =>
          SmtValue.Seq
            (SmtSeq.cons a (SmtSeq.empty (__smtx_typeof_value a))))
        (by intro a; rfl)
        seq_unit_arg_non_reg_of_non_none
        (by intro a; rw [smtx_model_eval_seq_unit_term_eq])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_concat) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_concat x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_substr) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_substr x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_contains) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_contains x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_replace) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_replace x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_indexof) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_indexof x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_at) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_at x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_prefixof) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_prefixof x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_suffixof) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_suffixof x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_update) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_update x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_lt) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_lt x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_leq) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_leq x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_replace_all) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_replace_all x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_replace_re) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_replace_re x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_replace_re_all) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_replace_re_all x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.str_indexof_re) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.str_indexof_re x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp.seq_nth) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp.seq_nth x rhs (by rfl) hEqBool
  | Term.Apply (Term.UOp UserOp._at_strings_num_occur) x =>
      exact congTrueSpine_uop_apply_none_head_eq_true
        M UserOp._at_strings_num_occur x rhs (by rfl) hEqBool
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x₁) x₂ =>
      exact congTrueSpine_seq_binop_eq_true M hM UserOp.str_concat
        SmtTerm.str_concat __smtx_model_eval_str_concat
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_concat_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_81])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x₁) x₂ =>
      exact congTrueSpine_seq_binop_ret_eq_true M hM UserOp.str_contains
        SmtTerm.str_contains SmtType.Bool __smtx_model_eval_str_contains
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_contains_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_83])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x₁) x₂ =>
      exact congTrueSpine_non_reg_binop_eq_true M hM UserOp.str_at
        SmtTerm.str_at __smtx_model_eval_str_at
        (by intro a b; rfl)
        str_at_args_non_reg_of_non_none
        (by intro a b; rw [__smtx_model_eval.eq_86])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x₁) x₂ =>
      exact congTrueSpine_seq_binop_ret_eq_true M hM UserOp.str_prefixof
        SmtTerm.str_prefixof SmtType.Bool __smtx_model_eval_str_prefixof
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_prefixof_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_87])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x₁) x₂ =>
      exact congTrueSpine_seq_binop_ret_eq_true M hM UserOp.str_suffixof
        SmtTerm.str_suffixof SmtType.Bool __smtx_model_eval_str_suffixof
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_suffixof_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_88])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x₁) x₂ =>
      exact congTrueSpine_seq_char_binop_eq_true M hM UserOp.str_lt
        SmtTerm.str_lt SmtType.Bool __smtx_model_eval_str_lt
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_lt_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_98])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x₁) x₂ =>
      exact congTrueSpine_seq_char_binop_eq_true M hM UserOp.str_leq
        SmtTerm.str_leq SmtType.Bool __smtx_model_eval_str_leq
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_leq_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_99])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x₁) x₂ =>
      exact congTrueSpine_non_reg_binop_eq_true M hM UserOp.seq_nth
        SmtTerm.seq_nth (fun a b => __smtx_seq_nth M a b)
        (by intro a b; rfl)
        seq_nth_args_non_reg_of_non_none
        (by intro a b; rw [smtx_model_eval_seq_nth_term_eq])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term._at_strings_stoi_result x₁) x₂ =>
      exact congTrueSpine_strings_stoi_result_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term._at_strings_itos_result x₁) x₂ =>
      exact congTrueSpine_strings_itos_result_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂ =>
      exact congTrueSpine_strings_num_occur_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM UserOp.str_substr
        SmtTerm.str_substr __smtx_model_eval_str_substr
        (by intro a b c; rfl)
        str_substr_args_non_reg_of_non_none
        (by intro a b c; rw [__smtx_model_eval.eq_82])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM UserOp.str_replace
        SmtTerm.str_replace __smtx_model_eval_str_replace
        (by intro a b c; rfl)
        (seq_triop_args_non_reg_of_non_none SmtTerm.str_replace
          (by intro a b c; exact typeof_str_replace_eq a b c))
        (by intro a b c; rw [__smtx_model_eval.eq_84])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM UserOp.str_indexof
        SmtTerm.str_indexof __smtx_model_eval_str_indexof
        (by intro a b c; rfl)
        str_indexof_args_non_reg_of_non_none
        (by intro a b c; rw [__smtx_model_eval.eq_85])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM UserOp.str_update
        SmtTerm.str_update __smtx_model_eval_str_update
        (by intro a b c; rfl)
        str_update_args_non_reg_of_non_none
        (by intro a b c; rw [__smtx_model_eval.eq_90])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM
        UserOp.str_replace_all SmtTerm.str_replace_all
        __smtx_model_eval_str_replace_all
        (by intro a b c; rfl)
        (seq_triop_args_non_reg_of_non_none SmtTerm.str_replace_all
          (by intro a b c; exact typeof_str_replace_all_eq a b c))
        (by intro a b c; rw [__smtx_model_eval.eq_100])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂) x₃ =>
      exact congTrueSpine_str_replace_re_eq_true M hM
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂) x₃ =>
      exact congTrueSpine_str_replace_re_all_eq_true M hM
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂) x₃ =>
      exact congTrueSpine_str_indexof_re_eq_true M hM
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.set_is_empty) x =>
      exact congTrueSpine_set_is_empty_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.set_choose) x =>
      exact congTrueSpine_set_choose_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.set_singleton) x =>
      exact congTrueSpine_non_reg_unop_eq_true M hM UserOp.set_singleton
        SmtTerm.set_singleton __smtx_model_eval_set_singleton
        (by intro a; rfl)
        set_singleton_arg_non_reg_of_non_none
        (by intro a; rw [smtx_model_eval_set_singleton_term_eq])
        x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x₁) x₂ =>
      exact congTrueSpine_set_binop_eq_true M hM UserOp.set_union
        SmtTerm.set_union __smtx_model_eval_set_union
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_union_eq a b)
        (by intro a b; rw [smtx_model_eval_set_union_term_eq])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x₁) x₂ =>
      exact congTrueSpine_set_binop_eq_true M hM UserOp.set_inter
        SmtTerm.set_inter __smtx_model_eval_set_inter
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_inter_eq a b)
        (by intro a b; rw [smtx_model_eval_set_inter_term_eq])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x₁) x₂ =>
      exact congTrueSpine_set_binop_eq_true M hM UserOp.set_minus
        SmtTerm.set_minus __smtx_model_eval_set_minus
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_minus_eq a b)
        (by intro a b; rw [smtx_model_eval_set_minus_term_eq])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x₁) x₂ =>
      exact congTrueSpine_set_binop_ret_eq_true M hM UserOp.set_subset
        SmtTerm.set_subset SmtType.Bool __smtx_model_eval_set_subset
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_subset_eq a b)
        (by intro a b; rw [smtx_model_eval_set_subset_term_eq])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂ =>
      exact congTrueSpine_bv_concat_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp2 UserOp2.extract i j) x =>
      exact congTrueSpine_non_reg_indexed2_unop_eq_true M hM
        UserOp2.extract i j
        (fun a => SmtTerm.extract (__eo_to_smt i) (__eo_to_smt j) a)
        (fun a =>
          __smtx_model_eval_extract
            (__smtx_model_eval M (__eo_to_smt i))
            (__smtx_model_eval M (__eo_to_smt j)) a)
        (by intro a; rfl)
        (extract_arg_non_reg_of_non_none (__eo_to_smt i) (__eo_to_smt j))
        (by intro a; rw [__smtx_model_eval.eq_37])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.repeat i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.repeat i
        (fun a => SmtTerm.repeat (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_repeat
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (repeat_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_38])
        x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂ =>
      exact congTrueSpine_bv_from_bools_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvredand) x =>
      exact congTrueSpine_bvredand_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvredor) x =>
      exact congTrueSpine_bvredor_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1._at_bit i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1._at_bit i
        (bvBitTerm (__eo_to_smt i))
        (fun a =>
          __smtx_model_eval_eq
            (__smtx_model_eval_extract
              (__smtx_model_eval M (__eo_to_smt i))
              (__smtx_model_eval M (__eo_to_smt i)) a)
            (SmtValue.Binary 1 1))
        (by intro a; rfl)
        (bv_bit_arg_non_reg_of_non_none (__eo_to_smt i))
        (by
          intro a
          rw [bvBitTerm, smtx_model_eval_eq_term_eq,
            __smtx_model_eval.eq_37, __smtx_model_eval.eq_5])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvnot) x =>
      exact congTrueSpine_bv_unop_eq_true M hM UserOp.bvnot SmtTerm.bvnot
        __smtx_model_eval_bvnot
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_39])
        (by intro a; rw [__smtx_model_eval.eq_39])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvneg) x =>
      exact congTrueSpine_bv_unop_eq_true M hM UserOp.bvneg SmtTerm.bvneg
        __smtx_model_eval_bvneg
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_47])
        (by intro a; rw [__smtx_model_eval.eq_47])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvnego) x =>
      exact congTrueSpine_bv_unop_ret_eq_true M hM UserOp.bvnego
        SmtTerm.bvnego SmtType.Bool __smtx_model_eval_bvnego
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_72])
        (by intro a; rw [__smtx_model_eval.eq_72])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.ubv_to_int) x =>
      exact congTrueSpine_bv_unop_ret_eq_true M hM UserOp.ubv_to_int
        SmtTerm.ubv_to_int SmtType.Int __smtx_model_eval_ubv_to_int
        (by intro a; rfl)
        (by intro a; rw [smtx_typeof_ubv_to_int_term_eq])
        (by intro a; rw [smtx_model_eval_ubv_to_int_term_eq])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.sbv_to_int) x =>
      exact congTrueSpine_bv_unop_ret_eq_true M hM UserOp.sbv_to_int
        SmtTerm.sbv_to_int SmtType.Int __smtx_model_eval_sbv_to_int
        (by intro a; rfl)
        (by intro a; rw [smtx_typeof_sbv_to_int_term_eq])
        (by intro a; rw [smtx_model_eval_sbv_to_int_term_eq])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.int_to_bv w) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.int_to_bv w
        (fun a => SmtTerm.int_to_bv (__eo_to_smt w) a)
        (fun a =>
          __smtx_model_eval_int_to_bv
            (__smtx_model_eval M (__eo_to_smt w)) a)
        (by intro a; rfl)
        (int_to_bv_arg_non_reg_of_non_none (__eo_to_smt w))
        (by intro a; rw [smtx_model_eval_int_to_bv_term_eq])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.is c) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.is c
        (fun a => SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c)) a)
        (fun a =>
          match __eo_to_smt_tester (__eo_to_smt c) with
          | SmtTerm.DtTester s d i => __smtx_model_eval_dt_tester s d i a
          | tester => __smtx_model_eval_apply M (__smtx_model_eval M tester) a)
        (by intro a; rfl)
        (is_arg_non_reg_of_non_none c)
        (by
          intro a
          cases __eo_to_smt c <;>
            simp [__eo_to_smt_tester, __smtx_model_eval])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x =>
      exact congTrueSpine_tuple_select_eq_true M hM
        idx x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvand SmtTerm.bvand
        __smtx_model_eval_bvand
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_40])
        (by intro a b; rw [__smtx_model_eval.eq_40])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvor SmtTerm.bvor
        __smtx_model_eval_bvor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_41])
        (by intro a b; rw [__smtx_model_eval.eq_41])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvnand) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvnand SmtTerm.bvnand
        __smtx_model_eval_bvnand
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_42])
        (by intro a b; rw [__smtx_model_eval.eq_42])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvnor) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvnor SmtTerm.bvnor
        __smtx_model_eval_bvnor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_43])
        (by intro a b; rw [__smtx_model_eval.eq_43])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvxor SmtTerm.bvxor
        __smtx_model_eval_bvxor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_44])
        (by intro a b; rw [__smtx_model_eval.eq_44])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvxnor SmtTerm.bvxnor
        __smtx_model_eval_bvxnor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_45])
        (by intro a b; rw [__smtx_model_eval.eq_45])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvcomp
        SmtTerm.bvcomp (SmtType.BitVec 1) __smtx_model_eval_bvcomp
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_46])
        (by intro a b; rw [__smtx_model_eval.eq_46])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvadd SmtTerm.bvadd
        __smtx_model_eval_bvadd
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_48])
        (by intro a b; rw [__smtx_model_eval.eq_48])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvmul SmtTerm.bvmul
        __smtx_model_eval_bvmul
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_49])
        (by intro a b; rw [__smtx_model_eval.eq_49])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvudiv SmtTerm.bvudiv
        __smtx_model_eval_bvudiv
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_50])
        (by intro a b; rw [__smtx_model_eval.eq_50])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvurem SmtTerm.bvurem
        __smtx_model_eval_bvurem
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_51])
        (by intro a b; rw [__smtx_model_eval.eq_51])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvsub SmtTerm.bvsub
        __smtx_model_eval_bvsub
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_52])
        (by intro a b; rw [__smtx_model_eval.eq_52])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvsdiv SmtTerm.bvsdiv
        __smtx_model_eval_bvsdiv
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_53])
        (by intro a b; rw [__smtx_model_eval.eq_53])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvsrem SmtTerm.bvsrem
        __smtx_model_eval_bvsrem
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_54])
        (by intro a b; rw [__smtx_model_eval.eq_54])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvsmod SmtTerm.bvsmod
        __smtx_model_eval_bvsmod
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_55])
        (by intro a b; rw [__smtx_model_eval.eq_55])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvult
        SmtTerm.bvult SmtType.Bool __smtx_model_eval_bvult
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_56])
        (by intro a b; rw [__smtx_model_eval.eq_56])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvule) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvule
        SmtTerm.bvule SmtType.Bool __smtx_model_eval_bvule
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_57])
        (by intro a b; rw [__smtx_model_eval.eq_57])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvugt
        SmtTerm.bvugt SmtType.Bool __smtx_model_eval_bvugt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_58])
        (by intro a b; rw [__smtx_model_eval.eq_58])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvuge
        SmtTerm.bvuge SmtType.Bool __smtx_model_eval_bvuge
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_59])
        (by intro a b; rw [__smtx_model_eval.eq_59])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvslt
        SmtTerm.bvslt SmtType.Bool __smtx_model_eval_bvslt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_60])
        (by intro a b; rw [__smtx_model_eval.eq_60])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsle
        SmtTerm.bvsle SmtType.Bool __smtx_model_eval_bvsle
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_61])
        (by intro a b; rw [__smtx_model_eval.eq_61])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsgt
        SmtTerm.bvsgt SmtType.Bool __smtx_model_eval_bvsgt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_62])
        (by intro a b; rw [__smtx_model_eval.eq_62])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsge
        SmtTerm.bvsge SmtType.Bool __smtx_model_eval_bvsge
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_63])
        (by intro a b; rw [__smtx_model_eval.eq_63])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvshl SmtTerm.bvshl
        __smtx_model_eval_bvshl
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_64])
        (by intro a b; rw [__smtx_model_eval.eq_64])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvlshr SmtTerm.bvlshr
        __smtx_model_eval_bvlshr
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_65])
        (by intro a b; rw [__smtx_model_eval.eq_65])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvashr SmtTerm.bvashr
        __smtx_model_eval_bvashr
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_66])
        (by intro a b; rw [__smtx_model_eval.eq_66])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.zero_extend i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.zero_extend i
        (fun a => SmtTerm.zero_extend (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_zero_extend
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (zero_extend_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_67])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.sign_extend i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.sign_extend i
        (fun a => SmtTerm.sign_extend (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_sign_extend
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (sign_extend_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_68])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.rotate_left i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.rotate_left i
        (fun a => SmtTerm.rotate_left (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_rotate_left
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (rotate_left_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_69])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.rotate_right i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.rotate_right i
        (fun a => SmtTerm.rotate_right (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_rotate_right
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (rotate_right_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_70])
        x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvuaddo
        SmtTerm.bvuaddo SmtType.Bool __smtx_model_eval_bvuaddo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_71])
        (by intro a b; rw [__smtx_model_eval.eq_71])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsaddo
        SmtTerm.bvsaddo SmtType.Bool __smtx_model_eval_bvsaddo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_73])
        (by intro a b; rw [__smtx_model_eval.eq_73])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvumulo
        SmtTerm.bvumulo SmtType.Bool __smtx_model_eval_bvumulo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_74])
        (by intro a b; rw [__smtx_model_eval.eq_74])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsmulo
        SmtTerm.bvsmulo SmtType.Bool __smtx_model_eval_bvsmulo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_75])
        (by intro a b; rw [__smtx_model_eval.eq_75])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvusubo
        SmtTerm.bvusubo SmtType.Bool __smtx_model_eval_bvusubo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_76])
        (by intro a b; rw [__smtx_model_eval.eq_76])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvssubo
        SmtTerm.bvssubo SmtType.Bool __smtx_model_eval_bvssubo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_77])
        (by intro a b; rw [__smtx_model_eval.eq_77])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsdivo
        SmtTerm.bvsdivo SmtType.Bool __smtx_model_eval_bvsdivo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_78])
        (by intro a b; rw [__smtx_model_eval.eq_78])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x₁) x₂ =>
      exact congTrueSpine_bv_pred_to_bv_eq_true M hM UserOp.bvultbv
        SmtTerm.bvult __smtx_model_eval_bvult
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_56])
        (by
          intro a b
          rw [bvPredToBv, bvPredToBvEval, smtx_model_eval_ite_term_eq,
            __smtx_model_eval.eq_56, __smtx_model_eval.eq_5,
            __smtx_model_eval.eq_5])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x₁) x₂ =>
      exact congTrueSpine_bv_pred_to_bv_eq_true M hM UserOp.bvsltbv
        SmtTerm.bvslt __smtx_model_eval_bvslt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_60])
        (by
          intro a b
          rw [bvPredToBv, bvPredToBvEval, smtx_model_eval_ite_term_eq,
            __smtx_model_eval.eq_60, __smtx_model_eval.eq_5,
            __smtx_model_eval.eq_5])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.forall) Term.__eo_List_nil) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_to_smt_none (t := Term.Apply
          (Term.Apply (Term.UOp UserOp.forall) Term.__eo_List_nil) x)
          (rhs := rhs) (by rfl) hEqBool)
  | Term.Apply (Term.Apply (Term.UOp UserOp.exists) Term.__eo_List_nil) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_to_smt_none (t := Term.Apply
          (Term.Apply (Term.UOp UserOp.exists) Term.__eo_List_nil) x)
          (rhs := rhs) (by rfl) hEqBool)
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) Term.__eo_List_nil) x =>
      exact False.elim
        (no_bool_eq_left_of_eo_to_smt_none (t := Term.Apply
          (Term.Apply (Term.UOp UserOp.set_insert) Term.__eo_List_nil) x)
          (rhs := rhs) (by rfl) hEqBool)
  | lhs =>
      match hHead : (appSpineRev lhs).1 with
      | Term.Var (Term.String s) T =>
          exact congTrueSpine_appSpineRev_var_eq_true
            M hM s T lhs rhs hHead hEqBool hSpine
      | Term.UConst i T =>
          exact congTrueSpine_appSpineRev_uconst_eq_true
            M hM i T lhs rhs hHead hEqBool hSpine
      | Term.DtCons s d i =>
          exact congTrueSpine_appSpineRev_dtcons_eq_true
            M hM s d i lhs rhs hHead hEqBool hSpine
      | Term.DtSel s d i j =>
          exact congTrueSpine_appSpineRev_dt_sel_eq_true
            M hM s d i j lhs rhs hHead hEqBool hSpine
      | _ =>
          cases hSpine with
          | refl _ =>
              exact congTrueSpine_refl_eq_true M rhs hEqBool
          | @app f g x y hFn hArg hArgStable =>
              have hApp :
                  CongTrueSpine M (Term.Apply f x) (Term.Apply g y) :=
                CongTrueSpine.app hFn hArg hArgStable
              match f with
              | Term.Var (Term.String s) T =>
                  exact congTrueSpine_var_apply_eq_true
                    M hM s T x (Term.Apply g y) hEqBool hApp
              | Term.Var name T =>
                  by_cases hName : ∃ s : native_String, name = Term.String s
                  · rcases hName with ⟨s, rfl⟩
                    exact congTrueSpine_var_apply_eq_true
                      M hM s T x (Term.Apply g y) hEqBool hApp
                  ·
                    exact False.elim
                      (no_bool_eq_left_of_eo_apply_none_head
                        (f := Term.Var name T) (x := x)
                        (rhs := Term.Apply g y)
                        (eo_to_smt_apply_var_non_string_none_head
                          (by
                            intro s hs
                            exact hName ⟨s, hs⟩))
                        hEqBool)
              | Term.UConst i T =>
                  exact congTrueSpine_uconst_apply_eq_true
                    M hM i T x (Term.Apply g y) hEqBool hApp
              | Term.DtCons s d i =>
                  exact congTrueSpine_appSpineRev_dtcons_eq_true
                    M hM s d i (Term.Apply (Term.DtCons s d i) x)
                    (Term.Apply g y) (by rfl) hEqBool hApp
              | Term.DtSel s d i j =>
                  exact congTrueSpine_dt_sel_eq_true
                    M hM s d i j x (Term.Apply g y) hEqBool hApp
              | Term.UOp op =>
                  match hUnary : uopHasUnarySmtTranslation op with
                  | false =>
                      exact
                        congTrueSpine_uop_apply_not_unary_eq_true
                          M op x (Term.Apply g y) hUnary hEqBool
                  | true =>
                      cases op <;> simp [uopHasUnarySmtTranslation] at hUnary
                      case not =>
                        exact congTrueSpine_not_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case _at_purify =>
                        exact congTrueSpine_purify_eq_true M
                          x (Term.Apply g y) hEqBool hApp
                      case to_real =>
                        exact congTrueSpine_to_real_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case to_int =>
                        exact congTrueSpine_to_int_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case is_int =>
                        exact congTrueSpine_is_int_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case abs =>
                        exact congTrueSpine_abs_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case __eoo_neg_2 =>
                        exact congTrueSpine_uneg_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case int_pow2 =>
                        exact congTrueSpine_int_pow2_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case int_log2 =>
                        exact congTrueSpine_int_log2_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case int_ispow2 =>
                        exact congTrueSpine_int_ispow2_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case _at_int_div_by_zero =>
                        exact congTrueSpine_int_div_by_zero_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case _at_mod_by_zero =>
                        exact congTrueSpine_mod_by_zero_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case _at_bvsize =>
                        exact congTrueSpine_bvsize_eq_true M
                          x (Term.Apply g y) hEqBool hApp
                      case str_len =>
                        exact congTrueSpine_seq_unop_ret_eq_true M hM
                          UserOp.str_len SmtTerm.str_len SmtType.Int
                          __smtx_model_eval_str_len
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_len_eq a)
                          (by intro a; rw [smtx_eval_str_len_term_eq])
                          x (Term.Apply g y) hEqBool hApp
                      case str_rev =>
                        exact congTrueSpine_seq_unop_eq_true M hM
                          UserOp.str_rev SmtTerm.str_rev
                          __smtx_model_eval_str_rev
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_rev_eq a)
                          (by intro a; rw [__smtx_model_eval.eq_89])
                          x (Term.Apply g y) hEqBool hApp
                      case str_to_lower =>
                        exact congTrueSpine_seq_char_unop_eq_true M hM
                          UserOp.str_to_lower SmtTerm.str_to_lower
                          (SmtType.Seq SmtType.Char)
                          __smtx_model_eval_str_to_lower
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_lower_eq a)
                          (by intro a; rw [__smtx_model_eval.eq_91])
                          x (Term.Apply g y) hEqBool hApp
                      case str_to_upper =>
                        exact congTrueSpine_seq_char_unop_eq_true M hM
                          UserOp.str_to_upper SmtTerm.str_to_upper
                          (SmtType.Seq SmtType.Char)
                          __smtx_model_eval_str_to_upper
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_upper_eq a)
                          (by intro a; rw [__smtx_model_eval.eq_92])
                          x (Term.Apply g y) hEqBool hApp
                      case str_to_code =>
                        exact congTrueSpine_seq_char_unop_eq_true M hM
                          UserOp.str_to_code SmtTerm.str_to_code SmtType.Int
                          __smtx_model_eval_str_to_code
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_code_eq a)
                          (by intro a; rw [smtx_eval_str_to_code_term_eq])
                          x (Term.Apply g y) hEqBool hApp
                      case str_from_code =>
                        exact congTrueSpine_non_reg_unop_eq_true M hM
                          UserOp.str_from_code SmtTerm.str_from_code
                          __smtx_model_eval_str_from_code
                          (by intro a; rfl)
                          (int_ret_unop_args_non_reg_of_non_none
                            SmtTerm.str_from_code (SmtType.Seq SmtType.Char)
                            (by intro a; exact typeof_str_from_code_eq a))
                          (by intro a; rw [__smtx_model_eval.eq_94])
                          x (Term.Apply g y) hEqBool hApp
                      case str_is_digit =>
                        exact congTrueSpine_seq_char_unop_eq_true M hM
                          UserOp.str_is_digit SmtTerm.str_is_digit
                          SmtType.Bool __smtx_model_eval_str_is_digit
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_is_digit_eq a)
                          (by intro a; rw [__smtx_model_eval.eq_95])
                          x (Term.Apply g y) hEqBool hApp
                      case str_to_int =>
                        exact congTrueSpine_seq_char_unop_eq_true M hM
                          UserOp.str_to_int SmtTerm.str_to_int SmtType.Int
                          __smtx_model_eval_str_to_int
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_int_eq a)
                          (by intro a; rw [__smtx_model_eval.eq_96])
                          x (Term.Apply g y) hEqBool hApp
                      case str_from_int =>
                        exact congTrueSpine_non_reg_unop_eq_true M hM
                          UserOp.str_from_int SmtTerm.str_from_int
                          __smtx_model_eval_str_from_int
                          (by intro a; rfl)
                          (int_ret_unop_args_non_reg_of_non_none
                            SmtTerm.str_from_int (SmtType.Seq SmtType.Char)
                            (by intro a; exact typeof_str_from_int_eq a))
                          (by intro a; rw [__smtx_model_eval.eq_97])
                          x (Term.Apply g y) hEqBool hApp
                      case str_to_re =>
                        exact congTrueSpine_seq_char_unop_eq_true M hM
                          UserOp.str_to_re SmtTerm.str_to_re SmtType.RegLan
                          __smtx_model_eval_str_to_re
                          (by intro a; rfl)
                          (by intro a; exact typeof_str_to_re_eq a)
                          (by intro a; rw [__smtx_model_eval.eq_107])
                          x (Term.Apply g y) hEqBool hApp
                      case _at_strings_stoi_non_digit =>
                        exact
                          congTrueSpine_strings_stoi_non_digit_eq_true M hM
                            x (Term.Apply g y) hEqBool hApp
                      case re_opt =>
                        exact congTrueSpine_re_opt_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case re_comp =>
                        exact congTrueSpine_re_comp_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case re_mult =>
                        exact congTrueSpine_re_mult_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case re_plus =>
                        exact congTrueSpine_re_plus_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case seq_unit =>
                        exact congTrueSpine_non_reg_unop_eq_true M hM
                          UserOp.seq_unit SmtTerm.seq_unit
                          (fun a =>
                            SmtValue.Seq
                              (SmtSeq.cons a
                                (SmtSeq.empty (__smtx_typeof_value a))))
                          (by intro a; rfl)
                          seq_unit_arg_non_reg_of_non_none
                          (by intro a; rw [smtx_model_eval_seq_unit_term_eq])
                          x (Term.Apply g y) hEqBool hApp
                      case set_is_empty =>
                        exact congTrueSpine_set_is_empty_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case set_singleton =>
                        exact congTrueSpine_non_reg_unop_eq_true M hM
                          UserOp.set_singleton SmtTerm.set_singleton
                          __smtx_model_eval_set_singleton
                          (by intro a; rfl)
                          set_singleton_arg_non_reg_of_non_none
                          (by intro a; rw [smtx_model_eval_set_singleton_term_eq])
                          x (Term.Apply g y) hEqBool hApp
                      case set_choose =>
                        exact congTrueSpine_set_choose_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case set_is_singleton =>
                        cases hFn with
                        | refl _ =>
                            exact
                              congTrueSpine_set_is_singleton_eq_true M hM
                                x
                                (Term.Apply
                                  (Term.UOp UserOp.set_is_singleton) y)
                                hEqBool hApp
                      case _at_div_by_zero =>
                        exact congTrueSpine_qdiv_by_zero_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case bvredand =>
                        exact congTrueSpine_bvredand_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case bvredor =>
                        exact congTrueSpine_bvredor_eq_true M hM
                          x (Term.Apply g y) hEqBool hApp
                      case bvnot =>
                        exact congTrueSpine_bv_unop_eq_true M hM
                          UserOp.bvnot SmtTerm.bvnot
                          __smtx_model_eval_bvnot
                          (by intro a; rfl)
                          (by intro a; rw [__smtx_typeof.eq_39])
                          (by intro a; rw [__smtx_model_eval.eq_39])
                          x (Term.Apply g y) hEqBool hApp
                      case bvneg =>
                        exact congTrueSpine_bv_unop_eq_true M hM
                          UserOp.bvneg SmtTerm.bvneg
                          __smtx_model_eval_bvneg
                          (by intro a; rfl)
                          (by intro a; rw [__smtx_typeof.eq_47])
                          (by intro a; rw [__smtx_model_eval.eq_47])
                          x (Term.Apply g y) hEqBool hApp
                      case bvnego =>
                        exact congTrueSpine_bv_unop_ret_eq_true M hM
                          UserOp.bvnego SmtTerm.bvnego SmtType.Bool
                          __smtx_model_eval_bvnego
                          (by intro a; rfl)
                          (by intro a; rw [__smtx_typeof.eq_72])
                          (by intro a; rw [__smtx_model_eval.eq_72])
                          x (Term.Apply g y) hEqBool hApp
                      case ubv_to_int =>
                        exact congTrueSpine_bv_unop_ret_eq_true M hM
                          UserOp.ubv_to_int SmtTerm.ubv_to_int SmtType.Int
                          __smtx_model_eval_ubv_to_int
                          (by intro a; rfl)
                          (by intro a; rw [smtx_typeof_ubv_to_int_term_eq])
                          (by intro a; rw [smtx_model_eval_ubv_to_int_term_eq])
                          x (Term.Apply g y) hEqBool hApp
                      case sbv_to_int =>
                        exact congTrueSpine_bv_unop_ret_eq_true M hM
                          UserOp.sbv_to_int SmtTerm.sbv_to_int SmtType.Int
                          __smtx_model_eval_sbv_to_int
                          (by intro a; rfl)
                          (by intro a; rw [smtx_typeof_sbv_to_int_term_eq])
                          (by intro a; rw [smtx_model_eval_sbv_to_int_term_eq])
                          x (Term.Apply g y) hEqBool hApp
                      case distinct =>
                        have hLeftTrans :
                            RuleProofs.eo_has_smt_translation
                              (Term.Apply (Term.UOp UserOp.distinct) x) :=
                          (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                            (Term.Apply (Term.UOp UserOp.distinct) x)
                            (Term.Apply g y) hEqBool).2
                        have hArgBool :
                            RuleProofs.eo_has_bool_type (mkEq x y) :=
                          RuleProofs.eo_has_bool_type_of_interprets_true
                            M (mkEq x y) hArg
                        exact False.elim
                          (no_bool_eq_arg_of_distinct_translation
                            x y hLeftTrans hArgBool)
              | Term.__eo_List =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.__eo_List) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.__eo_List_nil =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.__eo_List_nil) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.__eo_List_cons =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.__eo_List_cons) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.Bool =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.Bool) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.Boolean b =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.Boolean b) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply (SmtTerm.Boolean b)
                              (__eo_to_smt x)) = SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.Numeral n =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.Numeral n) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply (SmtTerm.Numeral n)
                              (__eo_to_smt x)) = SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.Rational q =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.Rational q) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply (SmtTerm.Rational q)
                              (__eo_to_smt x)) = SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.String s =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.String s) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply (SmtTerm.String s)
                              (__eo_to_smt x)) = SmtType.None
                        cases hValid : native_string_valid s <;>
                          cases __smtx_typeof (__eo_to_smt x) <;>
                            simp [__smtx_typeof, __smtx_typeof_apply,
                              hValid])
                      hEqBool)
              | Term.Binary w n =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.Binary w n) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (smt_apply_binary_typeof_none w n (__eo_to_smt x))
                      hEqBool)
              | Term.Type =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.Type) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.Stuck =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.Stuck) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.FunType =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.FunType) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.DatatypeType s d =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.DatatypeType s d) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.DatatypeTypeRef s =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.DatatypeTypeRef s) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.DtcAppType A B =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.DtcAppType A B) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.USort i =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.USort i) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                              SmtType.None
                        simp [__smtx_typeof, __smtx_typeof_apply])
                      hEqBool)
              | Term.UOp1 UserOp1.zero_extend i =>
                  exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
                    UserOp1.zero_extend i
                    (fun a => SmtTerm.zero_extend (__eo_to_smt i) a)
                    (fun a =>
                      __smtx_model_eval_zero_extend
                        (__smtx_model_eval M (__eo_to_smt i)) a)
                    (by intro a; rfl)
                    (zero_extend_arg_non_reg_of_non_none (__eo_to_smt i))
                    (by intro a; rw [__smtx_model_eval.eq_67])
                    x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.sign_extend i =>
                  exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
                    UserOp1.sign_extend i
                    (fun a => SmtTerm.sign_extend (__eo_to_smt i) a)
                    (fun a =>
                      __smtx_model_eval_sign_extend
                        (__smtx_model_eval M (__eo_to_smt i)) a)
                    (by intro a; rfl)
                    (sign_extend_arg_non_reg_of_non_none (__eo_to_smt i))
                    (by intro a; rw [__smtx_model_eval.eq_68])
                    x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.rotate_left i =>
                  exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
                    UserOp1.rotate_left i
                    (fun a => SmtTerm.rotate_left (__eo_to_smt i) a)
                    (fun a =>
                      __smtx_model_eval_rotate_left
                        (__smtx_model_eval M (__eo_to_smt i)) a)
                    (by intro a; rfl)
                    (rotate_left_arg_non_reg_of_non_none (__eo_to_smt i))
                    (by intro a; rw [__smtx_model_eval.eq_69])
                    x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.rotate_right i =>
                  exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
                    UserOp1.rotate_right i
                    (fun a => SmtTerm.rotate_right (__eo_to_smt i) a)
                    (fun a =>
                      __smtx_model_eval_rotate_right
                        (__smtx_model_eval M (__eo_to_smt i)) a)
                    (by intro a; rfl)
                    (rotate_right_arg_non_reg_of_non_none (__eo_to_smt i))
                    (by intro a; rw [__smtx_model_eval.eq_70])
                    x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.repeat i =>
                  exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
                    UserOp1.repeat i
                    (fun a => SmtTerm.repeat (__eo_to_smt i) a)
                    (fun a =>
                      __smtx_model_eval_repeat
                        (__smtx_model_eval M (__eo_to_smt i)) a)
                    (by intro a; rfl)
                    (repeat_arg_non_reg_of_non_none (__eo_to_smt i))
                    (by intro a; rw [__smtx_model_eval.eq_38])
                    x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.re_exp n =>
                  exact congTrueSpine_re_exp_eq_true M hM
                    n x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1._at_bit i =>
                  exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
                    UserOp1._at_bit i
                    (bvBitTerm (__eo_to_smt i))
                    (fun a =>
                      __smtx_model_eval_eq
                        (__smtx_model_eval_extract
                          (__smtx_model_eval M (__eo_to_smt i))
                          (__smtx_model_eval M (__eo_to_smt i)) a)
                        (SmtValue.Binary 1 1))
                    (by intro a; rfl)
                    (bv_bit_arg_non_reg_of_non_none (__eo_to_smt i))
                    (by
                      intro a
                      rw [bvBitTerm, smtx_model_eval_eq_term_eq,
                        __smtx_model_eval.eq_37, __smtx_model_eval.eq_5])
                    x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.int_to_bv w =>
                  exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
                    UserOp1.int_to_bv w
                    (fun a => SmtTerm.int_to_bv (__eo_to_smt w) a)
                    (fun a =>
                      __smtx_model_eval_int_to_bv
                        (__smtx_model_eval M (__eo_to_smt w)) a)
                    (by intro a; rfl)
                    (int_to_bv_arg_non_reg_of_non_none (__eo_to_smt w))
                    (by intro a; rw [smtx_model_eval_int_to_bv_term_eq])
                    x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.seq_empty T =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.UOp1 UserOp1.seq_empty T) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply
                              (__eo_to_smt_seq_empty (__eo_to_smt_type T))
                              (__eo_to_smt x)) = SmtType.None
                        exact typeof_apply_eo_to_smt_seq_empty_eq_none
                          (__eo_to_smt_type T) (__eo_to_smt x))
                      hEqBool)
              | Term.UOp1 UserOp1.set_empty T =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_type_none
                      (f := Term.UOp1 UserOp1.set_empty T) (x := x)
                      (rhs := Term.Apply g y) (by rfl)
                      (by
                        change
                          __smtx_typeof
                            (SmtTerm.Apply
                              (__eo_to_smt_set_empty (__eo_to_smt_type T))
                              (__eo_to_smt x)) = SmtType.None
                        exact typeof_apply_eo_to_smt_set_empty_eq_none
                          (__eo_to_smt_type T) (__eo_to_smt x))
                      hEqBool)
              | Term.UOp1 UserOp1.is c =>
                  exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
                    UserOp1.is c
                    (fun a => SmtTerm.Apply
                      (__eo_to_smt_tester (__eo_to_smt c)) a)
                    (fun a =>
                      match __eo_to_smt_tester (__eo_to_smt c) with
                      | SmtTerm.DtTester s d i =>
                          __smtx_model_eval_dt_tester s d i a
                      | tester =>
                          __smtx_model_eval_apply M
                            (__smtx_model_eval M tester) a)
                    (by intro a; rfl)
                    (is_arg_non_reg_of_non_none c)
                    (by
                      intro a
                      cases __eo_to_smt c <;>
                        simp [__eo_to_smt_tester, __smtx_model_eval])
                    x (Term.Apply g y) hEqBool hApp
              | Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x₁ =>
                  exact congTrueSpine_strings_stoi_result_eq_true M hM
                    x₁ x (Term.Apply g y) hEqBool hApp
              | Term.Apply (Term.UOp UserOp._at_strings_itos_result) x₁ =>
                  exact congTrueSpine_strings_itos_result_eq_true M hM
                    x₁ x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.tuple_select idx =>
                  exact congTrueSpine_tuple_select_eq_true M hM
                    idx x (Term.Apply g y) hEqBool hApp
              | Term.UOp2 UserOp2.extract i j =>
                  exact congTrueSpine_non_reg_indexed2_unop_eq_true M hM
                    UserOp2.extract i j
                    (fun a => SmtTerm.extract (__eo_to_smt i) (__eo_to_smt j) a)
                    (fun a =>
                      __smtx_model_eval_extract
                        (__smtx_model_eval M (__eo_to_smt i))
                        (__smtx_model_eval M (__eo_to_smt j)) a)
                    (by intro a; rfl)
                    (extract_arg_non_reg_of_non_none
                      (__eo_to_smt i) (__eo_to_smt j))
                    (by intro a; rw [__smtx_model_eval.eq_37])
                    x (Term.Apply g y) hEqBool hApp
              | Term.UOp2 UserOp2.re_loop lo hi =>
                  exact congTrueSpine_re_loop_eq_true M hM
                    lo hi x (Term.Apply g y) hEqBool hApp
              | Term.UOp1 UserOp1.update i =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_none_head
                      (f := Term.UOp1 UserOp1.update i) (x := x)
                      (rhs := Term.Apply g y) (by rfl) hEqBool)
              | Term.UOp1 UserOp1.tuple_update i =>
                  exact False.elim
                    (no_bool_eq_left_of_eo_apply_none_head
                      (f := Term.UOp1 UserOp1.tuple_update i) (x := x)
                      (rhs := Term.Apply g y) (by rfl) hEqBool)
              | Term.UOp2 UserOp2._at_const i j =>
                  cases hFn with
                  | refl _ =>
                      exact
                        congTrueSpine_same_generic_head_apply_eq_true
                          M hM
                          (Term.UOp2 UserOp2._at_const i j)
                          x y
                          (by intro a; rfl)
                          (generic_apply_type_of_non_datatype_head
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_sel i j)
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_tester i j))
                          (generic_apply_eval_of_non_datatype_head
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_sel i j)
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_tester i j))
                          (generic_apply_eval_of_non_datatype_head
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_sel i j)
                            (TranslationProofs.eo_to_smt_at_const_ne_dt_tester i j))
                          hEqBool hArg
              | Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n =>
                  cases hFn with
                  | refl _ =>
                      exact
                        congTrueSpine_same_generic_head_apply_eq_true
                          M hM (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n) x y
                          (by intro a; rfl)
                          (generic_apply_type_of_non_datatype_head
                            (eo_to_smt_at_bv_ne_dt_sel
                              (__eo_to_smt n) (__eo_to_smt w))
                            (eo_to_smt_at_bv_ne_dt_tester
                              (__eo_to_smt n) (__eo_to_smt w)))
                          (generic_apply_eval_of_non_datatype_head
                            (eo_to_smt_at_bv_ne_dt_sel
                              (__eo_to_smt n) (__eo_to_smt w))
                            (eo_to_smt_at_bv_ne_dt_tester
                              (__eo_to_smt n) (__eo_to_smt w)))
                          (generic_apply_eval_of_non_datatype_head
                            (eo_to_smt_at_bv_ne_dt_sel
                              (__eo_to_smt n) (__eo_to_smt w))
                            (eo_to_smt_at_bv_ne_dt_tester
                              (__eo_to_smt n) (__eo_to_smt w)))
                          hEqBool hArg
                  | @app f₂ g₂ n₂ n₂' hFn₂ hHeadTrue₂ hHeadStable₂ =>
                      cases hFn₂ with
                      | refl _ =>
                          exact
                            congTrueSpine_int_to_bv_head_congr_eq_true
                              M hM w n n₂' x y hEqBool hHeadTrue₂ hArg
              | Term.UOp2 UserOp2._at_quantifiers_skolemize q idx =>
                  cases hFn with
                  | refl _ =>
                      exact
                        congTrueSpine_same_generic_head_apply_eq_true
                          M hM
                          (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx)
                          x y
                          (by intro a; rfl)
                          (generic_apply_type_of_non_datatype_head
                            (eo_to_smt_quant_skolemize_top_ne_dt_sel q idx)
                            (eo_to_smt_quant_skolemize_top_ne_dt_tester q idx))
                          (generic_apply_eval_of_non_datatype_head
                            (eo_to_smt_quant_skolemize_top_ne_dt_sel q idx)
                            (eo_to_smt_quant_skolemize_top_ne_dt_tester q idx))
                          (generic_apply_eval_of_non_datatype_head
                            (eo_to_smt_quant_skolemize_top_ne_dt_sel q idx)
                            (eo_to_smt_quant_skolemize_top_ne_dt_tester q idx))
                          hEqBool hArg
              | Term.UOp3 UserOp3._at_re_unfold_pos_component str re idx =>
                  have hTypes :=
                    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                      (Term.Apply
                        (Term._at_re_unfold_pos_component str re idx) x)
                      (Term.Apply g y) hEqBool
                  exact False.elim (hTypes.2 (by
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
                        congTrueSpine_same_generic_head_apply_eq_true
                          M hM
                          (Term.UOp3 UserOp3._at_witness_string_length
                            T len id)
                          x y
                          (by intro a; rfl)
                          (generic_apply_type_of_non_datatype_head
                            (eo_to_smt_witness_string_length_ne_dt_sel T len id)
                            (eo_to_smt_witness_string_length_ne_dt_tester T len id))
                            (generic_apply_eval_of_non_datatype_head
                              (eo_to_smt_witness_string_length_ne_dt_sel T len id)
                              (eo_to_smt_witness_string_length_ne_dt_tester T len id))
                            (generic_apply_eval_of_non_datatype_head
                              (eo_to_smt_witness_string_length_ne_dt_sel T len id)
                              (eo_to_smt_witness_string_length_ne_dt_tester T len id))
                            hEqBool hArg
              | Term.Apply f' z =>
                  match hHead' :
                    (appSpineRev ((Term.Apply f' z).Apply x)).1 with
                  | Term.Var (Term.String s) T =>
                      exact congTrueSpine_appSpineRev_var_eq_true
                        M hM s T ((Term.Apply f' z).Apply x)
                        (Term.Apply g y) hHead' hEqBool hApp
                  | Term.UConst i T =>
                      exact congTrueSpine_appSpineRev_uconst_eq_true
                        M hM i T ((Term.Apply f' z).Apply x)
                        (Term.Apply g y) hHead' hEqBool hApp
                  | Term.DtCons s d i =>
                      exact congTrueSpine_appSpineRev_dtcons_eq_true
                        M hM s d i ((Term.Apply f' z).Apply x)
                        (Term.Apply g y) hHead' hEqBool hApp
                  | Term.DtSel s d i j =>
                      exact congTrueSpine_appSpineRev_dt_sel_eq_true
                        M hM s d i j ((Term.Apply f' z).Apply x)
                        (Term.Apply g y) hHead' hEqBool hApp
                  | _ =>
                      by_cases hHeadTrans :
                          RuleProofs.eo_has_smt_translation
                            (Term.Apply f' z)
                      · have hFnBool :
                            RuleProofs.eo_has_bool_type
                              (mkEq (Term.Apply f' z) g) :=
                          congTypeSpine_eq_has_bool_type
                            (Term.Apply f' z) g hHeadTrans
                            (congTypeSpine_of_congTrueSpine M hFn)
                        have hFnNotQuant :
                            NotTopLevelQuantifier (Term.Apply f' z) := by
                          constructor
                          · intro xs body hQ
                            have hHeadTransQ :
                                RuleProofs.eo_has_smt_translation
                                  (Term.Apply
                                    (Term.Apply (Term.UOp UserOp.forall) xs)
                                    body) := by
                              simpa [hQ] using hHeadTrans
                            have hEqBoolQ :
                                RuleProofs.eo_has_bool_type
                                  (mkEq
                                    (Term.Apply
                                      (Term.Apply
                                        (Term.Apply
                                          (Term.UOp UserOp.forall) xs)
                                        body) x)
                                    (Term.Apply g y)) := by
                              simpa [hQ] using hEqBool
                            exact
                              no_bool_eq_left_of_eo_apply_type_none
                                (f := Term.Apply
                                  (Term.Apply (Term.UOp UserOp.forall) xs)
                                  body)
                                (x := x) (rhs := Term.Apply g y)
                                (eo_to_smt_apply_generic_of_has_smt_translation
                                  (Term.Apply
                                    (Term.Apply (Term.UOp UserOp.forall) xs)
                                    body) x hHeadTransQ)
                                (smtx_typeof_apply_forall_top_none xs body x)
                                hEqBoolQ
                          · intro xs body hQ
                            have hHeadTransQ :
                                RuleProofs.eo_has_smt_translation
                                  (Term.Apply
                                    (Term.Apply (Term.UOp UserOp.exists) xs)
                                    body) := by
                              simpa [hQ] using hHeadTrans
                            have hEqBoolQ :
                                RuleProofs.eo_has_bool_type
                                  (mkEq
                                    (Term.Apply
                                      (Term.Apply
                                        (Term.Apply
                                          (Term.UOp UserOp.exists) xs)
                                        body) x)
                                    (Term.Apply g y)) := by
                              simpa [hQ] using hEqBool
                            exact
                              no_bool_eq_left_of_eo_apply_type_none
                                (f := Term.Apply
                                  (Term.Apply (Term.UOp UserOp.exists) xs)
                                  body)
                                (x := x) (rhs := Term.Apply g y)
                                (eo_to_smt_apply_generic_of_has_smt_translation
                                  (Term.Apply
                                    (Term.Apply (Term.UOp UserOp.exists) xs)
                                    body) x hHeadTransQ)
                                (smtx_typeof_apply_exists_top_none xs body x)
                                hEqBoolQ
                        have hFnTrue :
                            eo_interprets M
                              (mkEq (Term.Apply f' z) g) true :=
                          congTrueSpine_eq_true M hM
                            (Term.Apply f' z) g hFnNotQuant hFnBool hFn
                        have hGTrans :
                            RuleProofs.eo_has_smt_translation g :=
                          by
                            have hFnTypes :=
                              RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                (Term.Apply f' z) g hFnBool
                            intro hNone
                            exact hFnTypes.2 (hFnTypes.1.trans hNone)
                        exact
                          congTrueSpine_generic_apply_eq_true
                            M hM (Term.Apply f' z) g x y hEqBool
                            (eo_to_smt_apply_generic_of_has_smt_translation
                              (Term.Apply f' z) x hHeadTrans)
                            (eo_to_smt_apply_generic_of_has_smt_translation
                              g y hGTrans)
                            (generic_apply_type_of_non_datatype_head
                              (TranslationProofs.eo_to_smt_apply_ne_dt_sel f' z)
                              (TranslationProofs.eo_to_smt_apply_ne_dt_tester f' z))
                            (generic_apply_eval_of_non_datatype_head
                              (TranslationProofs.eo_to_smt_apply_ne_dt_sel f' z)
                              (TranslationProofs.eo_to_smt_apply_ne_dt_tester f' z))
                            (generic_apply_eval_of_non_datatype_head
                              (by
                                intro s d i j hSel
                                cases hFn with
                                | refl _ =>
                                    exact
                                      TranslationProofs.eo_to_smt_apply_ne_dt_sel
                                        f' z s d i j hSel
                                | app hHead hArg _ =>
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
                                | app hHead hArg _ =>
                                    exact
                                      TranslationProofs.eo_to_smt_apply_ne_dt_tester
                                        _ _ s d i hTester))
                            hFnTrue hArg
                      · match f' with
                        | Term.UOp op =>
                            cases op <;>
                              try
                                exact False.elim
                                  (hHeadTrans
                                    (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                      _ z x (by rfl)
                                      ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                        _ _ hEqBool).2)))
                            case eq =>
                              exact congTrueSpine_eq_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case and =>
                              exact congTrueSpine_and_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case or =>
                              exact congTrueSpine_or_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case imp =>
                              exact congTrueSpine_imp_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case xor =>
                              exact congTrueSpine_xor_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case plus =>
                              exact congTrueSpine_plus_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case neg =>
                              exact congTrueSpine_neg_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case mult =>
                              exact congTrueSpine_mult_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case lt =>
                              exact congTrueSpine_lt_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case leq =>
                              exact congTrueSpine_leq_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case gt =>
                              exact congTrueSpine_gt_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case geq =>
                              exact congTrueSpine_geq_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case div =>
                              exact congTrueSpine_div_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case mod =>
                              exact congTrueSpine_mod_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case div_total =>
                              exact congTrueSpine_div_total_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case mod_total =>
                              exact congTrueSpine_mod_total_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case divisible =>
                              exact congTrueSpine_divisible_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case select =>
                              exact congTrueSpine_non_reg_binop_eq_true M hM
                                UserOp.select SmtTerm.select
                                __smtx_model_eval_select
                                (by intro a b; rfl)
                                select_args_non_reg_of_non_none
                                (by intro a b; simp [__smtx_model_eval])
                                z x (Term.Apply g y) hEqBool hApp
                            case concat =>
                              exact congTrueSpine_bv_concat_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case qdiv =>
                              exact congTrueSpine_qdiv_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case qdiv_total =>
                              exact congTrueSpine_qdiv_total_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case str_concat =>
                              exact congTrueSpine_seq_binop_eq_true M hM
                                UserOp.str_concat SmtTerm.str_concat
                                __smtx_model_eval_str_concat
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_str_concat_eq a b)
                                (by intro a b; rw [__smtx_model_eval.eq_81])
                                z x (Term.Apply g y) hEqBool hApp
                            case str_contains =>
                              exact congTrueSpine_seq_binop_ret_eq_true M hM
                                UserOp.str_contains SmtTerm.str_contains
                                SmtType.Bool __smtx_model_eval_str_contains
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_str_contains_eq a b)
                                (by intro a b; rw [__smtx_model_eval.eq_83])
                                z x (Term.Apply g y) hEqBool hApp
                            case str_at =>
                              exact congTrueSpine_non_reg_binop_eq_true M hM
                                UserOp.str_at SmtTerm.str_at
                                __smtx_model_eval_str_at
                                (by intro a b; rfl)
                                str_at_args_non_reg_of_non_none
                                (by intro a b; rw [__smtx_model_eval.eq_86])
                                z x (Term.Apply g y) hEqBool hApp
                            case str_prefixof =>
                              exact congTrueSpine_seq_binop_ret_eq_true M hM
                                UserOp.str_prefixof SmtTerm.str_prefixof
                                SmtType.Bool __smtx_model_eval_str_prefixof
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_str_prefixof_eq a b)
                                (by intro a b; rw [__smtx_model_eval.eq_87])
                                z x (Term.Apply g y) hEqBool hApp
                            case str_suffixof =>
                              exact congTrueSpine_seq_binop_ret_eq_true M hM
                                UserOp.str_suffixof SmtTerm.str_suffixof
                                SmtType.Bool __smtx_model_eval_str_suffixof
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_str_suffixof_eq a b)
                                (by intro a b; rw [__smtx_model_eval.eq_88])
                                z x (Term.Apply g y) hEqBool hApp
                            case str_lt =>
                              exact congTrueSpine_seq_char_binop_eq_true M hM
                                UserOp.str_lt SmtTerm.str_lt SmtType.Bool
                                __smtx_model_eval_str_lt
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_str_lt_eq a b)
                                (by intro a b; rw [__smtx_model_eval.eq_98])
                                z x (Term.Apply g y) hEqBool hApp
                            case str_leq =>
                              exact congTrueSpine_seq_char_binop_eq_true M hM
                                UserOp.str_leq SmtTerm.str_leq SmtType.Bool
                                __smtx_model_eval_str_leq
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_str_leq_eq a b)
                                (by intro a b; rw [__smtx_model_eval.eq_99])
                                z x (Term.Apply g y) hEqBool hApp
                            case seq_nth =>
                              exact congTrueSpine_non_reg_binop_eq_true M hM
                                UserOp.seq_nth SmtTerm.seq_nth
                                (fun a b => __smtx_seq_nth M a b)
                                (by intro a b; rfl)
                                seq_nth_args_non_reg_of_non_none
                                (by intro a b; rw [smtx_model_eval_seq_nth_term_eq])
                                z x (Term.Apply g y) hEqBool hApp
                            case _at_array_deq_diff =>
                              exact
                                congTrueSpine_array_deq_diff_eq_true M hM
                                  z x (Term.Apply g y) hEqBool hApp
                            case _at_strings_deq_diff =>
                              exact
                                congTrueSpine_strings_deq_diff_eq_true M hM
                                  z x (Term.Apply g y) hEqBool hApp
                            case _at_strings_num_occur =>
                              exact congTrueSpine_strings_num_occur_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case _at_strings_num_occur_re =>
                              exact
                                congTrueSpine_strings_num_occur_re_eq_true M hM
                                  z x (Term.Apply g y) hEqBool hApp
                            case _at_strings_stoi_result =>
                              exact
                                congTrueSpine_strings_stoi_result_eq_true M hM
                                  z x (Term.Apply g y) hEqBool hApp
                            case _at_strings_itos_result =>
                              exact
                                congTrueSpine_strings_itos_result_eq_true M hM
                                  z x (Term.Apply g y) hEqBool hApp
                            case re_range =>
                              exact congTrueSpine_seq_char_binop_eq_true M hM
                                UserOp.re_range SmtTerm.re_range
                                SmtType.RegLan __smtx_model_eval_re_range
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_re_range_eq a b)
                                (by intro a b; rw [__smtx_model_eval.eq_113])
                                z x (Term.Apply g y) hEqBool hApp
                            case re_concat =>
                              exact congTrueSpine_re_concat_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case re_union =>
                              exact congTrueSpine_re_union_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case re_inter =>
                              exact congTrueSpine_re_inter_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case re_diff =>
                              exact congTrueSpine_re_diff_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case str_in_re =>
                              exact congTrueSpine_str_in_re_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case set_union =>
                              exact congTrueSpine_set_binop_eq_true M hM
                                UserOp.set_union SmtTerm.set_union
                                __smtx_model_eval_set_union
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_set_union_eq a b)
                                (by intro a b; rw [smtx_model_eval_set_union_term_eq])
                                z x (Term.Apply g y) hEqBool hApp
                            case set_inter =>
                              exact congTrueSpine_set_binop_eq_true M hM
                                UserOp.set_inter SmtTerm.set_inter
                                __smtx_model_eval_set_inter
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_set_inter_eq a b)
                                (by intro a b; rw [smtx_model_eval_set_inter_term_eq])
                                z x (Term.Apply g y) hEqBool hApp
                            case set_minus =>
                              exact congTrueSpine_set_binop_eq_true M hM
                                UserOp.set_minus SmtTerm.set_minus
                                __smtx_model_eval_set_minus
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_set_minus_eq a b)
                                (by intro a b; rw [smtx_model_eval_set_minus_term_eq])
                                z x (Term.Apply g y) hEqBool hApp
                            case set_member =>
                              exact congTrueSpine_non_reg_binop_eq_true M hM
                                UserOp.set_member SmtTerm.set_member
                                __smtx_model_eval_set_member
                                (by intro a b; rfl)
                                set_member_args_non_reg_of_non_none
                                (by intro a b; simp [__smtx_model_eval])
                                z x (Term.Apply g y) hEqBool hApp
                            case set_subset =>
                              exact congTrueSpine_set_binop_ret_eq_true M hM
                                UserOp.set_subset SmtTerm.set_subset
                                SmtType.Bool __smtx_model_eval_set_subset
                                (by intro a b; rfl)
                                (by intro a b; exact typeof_set_subset_eq a b)
                                (by intro a b; rw [smtx_model_eval_set_subset_term_eq])
                                z x (Term.Apply g y) hEqBool hApp
                            case _at_sets_deq_diff =>
                              exact
                                congTrueSpine_sets_deq_diff_eq_true M hM
                                  z x (Term.Apply g y) hEqBool hApp
                            case _at_from_bools =>
                              exact congTrueSpine_bv_from_bools_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case bvand =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvand SmtTerm.bvand
                                __smtx_model_eval_bvand
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_40])
                                (by intro a b; rw [__smtx_model_eval.eq_40])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvor =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvor SmtTerm.bvor
                                __smtx_model_eval_bvor
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_41])
                                (by intro a b; rw [__smtx_model_eval.eq_41])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvnand =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvnand SmtTerm.bvnand
                                __smtx_model_eval_bvnand
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_42])
                                (by intro a b; rw [__smtx_model_eval.eq_42])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvnor =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvnor SmtTerm.bvnor
                                __smtx_model_eval_bvnor
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_43])
                                (by intro a b; rw [__smtx_model_eval.eq_43])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvxor =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvxor SmtTerm.bvxor
                                __smtx_model_eval_bvxor
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_44])
                                (by intro a b; rw [__smtx_model_eval.eq_44])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvxnor =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvxnor SmtTerm.bvxnor
                                __smtx_model_eval_bvxnor
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_45])
                                (by intro a b; rw [__smtx_model_eval.eq_45])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvcomp =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvcomp SmtTerm.bvcomp
                                (SmtType.BitVec 1) __smtx_model_eval_bvcomp
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_46])
                                (by intro a b; rw [__smtx_model_eval.eq_46])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvadd =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvadd SmtTerm.bvadd
                                __smtx_model_eval_bvadd
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_48])
                                (by intro a b; rw [__smtx_model_eval.eq_48])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvmul =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvmul SmtTerm.bvmul
                                __smtx_model_eval_bvmul
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_49])
                                (by intro a b; rw [__smtx_model_eval.eq_49])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvudiv =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvudiv SmtTerm.bvudiv
                                __smtx_model_eval_bvudiv
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_50])
                                (by intro a b; rw [__smtx_model_eval.eq_50])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvurem =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvurem SmtTerm.bvurem
                                __smtx_model_eval_bvurem
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_51])
                                (by intro a b; rw [__smtx_model_eval.eq_51])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsub =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvsub SmtTerm.bvsub
                                __smtx_model_eval_bvsub
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_52])
                                (by intro a b; rw [__smtx_model_eval.eq_52])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsdiv =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvsdiv SmtTerm.bvsdiv
                                __smtx_model_eval_bvsdiv
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_53])
                                (by intro a b; rw [__smtx_model_eval.eq_53])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsrem =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvsrem SmtTerm.bvsrem
                                __smtx_model_eval_bvsrem
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_54])
                                (by intro a b; rw [__smtx_model_eval.eq_54])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsmod =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvsmod SmtTerm.bvsmod
                                __smtx_model_eval_bvsmod
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_55])
                                (by intro a b; rw [__smtx_model_eval.eq_55])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvult =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvult SmtTerm.bvult SmtType.Bool
                                __smtx_model_eval_bvult
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_56])
                                (by intro a b; rw [__smtx_model_eval.eq_56])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvule =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvule SmtTerm.bvule SmtType.Bool
                                __smtx_model_eval_bvule
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_57])
                                (by intro a b; rw [__smtx_model_eval.eq_57])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvugt =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvugt SmtTerm.bvugt SmtType.Bool
                                __smtx_model_eval_bvugt
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_58])
                                (by intro a b; rw [__smtx_model_eval.eq_58])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvuge =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvuge SmtTerm.bvuge SmtType.Bool
                                __smtx_model_eval_bvuge
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_59])
                                (by intro a b; rw [__smtx_model_eval.eq_59])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvslt =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvslt SmtTerm.bvslt SmtType.Bool
                                __smtx_model_eval_bvslt
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_60])
                                (by intro a b; rw [__smtx_model_eval.eq_60])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsle =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvsle SmtTerm.bvsle SmtType.Bool
                                __smtx_model_eval_bvsle
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_61])
                                (by intro a b; rw [__smtx_model_eval.eq_61])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsgt =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvsgt SmtTerm.bvsgt SmtType.Bool
                                __smtx_model_eval_bvsgt
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_62])
                                (by intro a b; rw [__smtx_model_eval.eq_62])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsge =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvsge SmtTerm.bvsge SmtType.Bool
                                __smtx_model_eval_bvsge
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_63])
                                (by intro a b; rw [__smtx_model_eval.eq_63])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvshl =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvshl SmtTerm.bvshl
                                __smtx_model_eval_bvshl
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_64])
                                (by intro a b; rw [__smtx_model_eval.eq_64])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvlshr =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvlshr SmtTerm.bvlshr
                                __smtx_model_eval_bvlshr
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_65])
                                (by intro a b; rw [__smtx_model_eval.eq_65])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvashr =>
                              exact congTrueSpine_bv_binop_eq_true M hM
                                UserOp.bvashr SmtTerm.bvashr
                                __smtx_model_eval_bvashr
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_66])
                                (by intro a b; rw [__smtx_model_eval.eq_66])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvuaddo =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvuaddo SmtTerm.bvuaddo SmtType.Bool
                                __smtx_model_eval_bvuaddo
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_71])
                                (by intro a b; rw [__smtx_model_eval.eq_71])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsaddo =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvsaddo SmtTerm.bvsaddo SmtType.Bool
                                __smtx_model_eval_bvsaddo
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_73])
                                (by intro a b; rw [__smtx_model_eval.eq_73])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvumulo =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvumulo SmtTerm.bvumulo SmtType.Bool
                                __smtx_model_eval_bvumulo
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_74])
                                (by intro a b; rw [__smtx_model_eval.eq_74])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsmulo =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvsmulo SmtTerm.bvsmulo SmtType.Bool
                                __smtx_model_eval_bvsmulo
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_75])
                                (by intro a b; rw [__smtx_model_eval.eq_75])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvusubo =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvusubo SmtTerm.bvusubo SmtType.Bool
                                __smtx_model_eval_bvusubo
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_76])
                                (by intro a b; rw [__smtx_model_eval.eq_76])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvssubo =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvssubo SmtTerm.bvssubo SmtType.Bool
                                __smtx_model_eval_bvssubo
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_77])
                                (by intro a b; rw [__smtx_model_eval.eq_77])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsdivo =>
                              exact congTrueSpine_bv_binop_ret_eq_true M hM
                                UserOp.bvsdivo SmtTerm.bvsdivo SmtType.Bool
                                __smtx_model_eval_bvsdivo
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_78])
                                (by intro a b; rw [__smtx_model_eval.eq_78])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvultbv =>
                              exact congTrueSpine_bv_pred_to_bv_eq_true M hM
                                UserOp.bvultbv SmtTerm.bvult
                                __smtx_model_eval_bvult
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_56])
                                (by
                                  intro a b
                                  rw [bvPredToBv, bvPredToBvEval,
                                    smtx_model_eval_ite_term_eq,
                                    __smtx_model_eval.eq_56,
                                    __smtx_model_eval.eq_5,
                                    __smtx_model_eval.eq_5])
                                z x (Term.Apply g y) hEqBool hApp
                            case bvsltbv =>
                              exact congTrueSpine_bv_pred_to_bv_eq_true M hM
                                UserOp.bvsltbv SmtTerm.bvslt
                                __smtx_model_eval_bvslt
                                (by intro a b; rfl)
                                (by intro a b; rw [__smtx_typeof.eq_60])
                                (by
                                  intro a b
                                  rw [bvPredToBv, bvPredToBvEval,
                                    smtx_model_eval_ite_term_eq,
                                    __smtx_model_eval.eq_60,
                                    __smtx_model_eval.eq_5,
                                    __smtx_model_eval.eq_5])
                                z x (Term.Apply g y) hEqBool hApp
                            case tuple =>
                              exact congTrueSpine_tuple_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case set_insert =>
                              exact congTrueSpine_set_insert_eq_true M hM
                                z x (Term.Apply g y) hEqBool hApp
                            case «forall» =>
                              exact False.elim ((hNotQuant.1 z x) rfl)
                            case «exists» =>
                              exact False.elim ((hNotQuant.2 z x) rfl)
                        | Term.Apply (Term.UOp UserOp.ite) c =>
                            exact congTrueSpine_ite_eq_true M hM
                              c z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.bvite) c =>
                            exact congTrueSpine_bvite_eq_true M hM
                              c z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.store) a =>
                            exact
                              congTrueSpine_non_reg_ternop_eq_true M hM
                                UserOp.store SmtTerm.store
                                __smtx_model_eval_store
                                (by intro a b c; rfl)
                                store_args_non_reg_of_non_none
                                (by intro a b c; simp [__smtx_model_eval])
                                a z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.str_substr) s =>
                            exact
                              congTrueSpine_non_reg_ternop_eq_true M hM
                                UserOp.str_substr SmtTerm.str_substr
                                __smtx_model_eval_str_substr
                                (by intro a b c; rfl)
                                str_substr_args_non_reg_of_non_none
                                (by intro a b c; rw [__smtx_model_eval.eq_82])
                                s z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.str_replace) s =>
                            exact
                              congTrueSpine_non_reg_ternop_eq_true M hM
                                UserOp.str_replace SmtTerm.str_replace
                                __smtx_model_eval_str_replace
                                (by intro a b c; rfl)
                                (seq_triop_args_non_reg_of_non_none
                                  SmtTerm.str_replace
                                  (by intro a b c; exact typeof_str_replace_eq a b c))
                                (by intro a b c; rw [__smtx_model_eval.eq_84])
                                s z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.str_indexof) s =>
                            exact
                              congTrueSpine_non_reg_ternop_eq_true M hM
                                UserOp.str_indexof SmtTerm.str_indexof
                                __smtx_model_eval_str_indexof
                                (by intro a b c; rfl)
                                str_indexof_args_non_reg_of_non_none
                                (by intro a b c; rw [__smtx_model_eval.eq_85])
                                s z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.str_update) s =>
                            exact
                              congTrueSpine_non_reg_ternop_eq_true M hM
                                UserOp.str_update SmtTerm.str_update
                                __smtx_model_eval_str_update
                                (by intro a b c; rfl)
                                str_update_args_non_reg_of_non_none
                                (by intro a b c; rw [__smtx_model_eval.eq_90])
                                s z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.str_replace_all) s =>
                            exact
                              congTrueSpine_non_reg_ternop_eq_true M hM
                                UserOp.str_replace_all SmtTerm.str_replace_all
                                __smtx_model_eval_str_replace_all
                                (by intro a b c; rfl)
                                (seq_triop_args_non_reg_of_non_none
                                  SmtTerm.str_replace_all
                                  (by intro a b c; exact typeof_str_replace_all_eq a b c))
                                (by intro a b c; rw [__smtx_model_eval.eq_100])
                                s z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.str_replace_re) s =>
                            exact congTrueSpine_str_replace_re_eq_true M hM
                              s z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.str_replace_re_all) s =>
                            exact congTrueSpine_str_replace_re_all_eq_true M hM
                              s z x (Term.Apply g y) hEqBool hApp
                        | Term.Apply (Term.UOp UserOp.str_indexof_re) s =>
                            exact congTrueSpine_str_indexof_re_eq_true M hM
                              s z x (Term.Apply g y) hEqBool hApp
                        | Term.UOp1 UserOp1.update i =>
                            exact
                              congTrueSpine_non_reg_indexed_binary_uop1_eq_true
                                M hM UserOp1.update i
                                (fun a b =>
                                  __eo_to_smt_updater (__eo_to_smt i) a b)
                                (by intro a b; rfl)
                                (by
                                  intro a b hNN
                                  exact updater_args_non_reg_of_non_none
                                    (__eo_to_smt i) a b hNN)
                                (by
                                  intro a b a' b' ha hb
                                  exact eo_to_smt_updater_eval_congr
                                    M (__eo_to_smt i) a b a' b' ha hb)
                                z x (Term.Apply g y) hEqBool hApp
                        | Term.UOp1 UserOp1.tuple_update i =>
                            exact congTrueSpine_tuple_update_eq_true M hM
                              i z x (Term.Apply g y) hEqBool hApp
                        | Term.UOp1 op i =>
                            cases op <;>
                              try
                                exact False.elim
                                  (hHeadTrans
                                    (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                      _ z x (by rfl)
                                      ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                        _ _ hEqBool).2)))
                            case update =>
                              exact
                                congTrueSpine_non_reg_indexed_binary_uop1_eq_true
                                  M hM UserOp1.update i
                                  (fun a b =>
                                    __eo_to_smt_updater (__eo_to_smt i) a b)
                                  (by intro a b; rfl)
                                  (by
                                    intro a b hNN
                                    exact updater_args_non_reg_of_non_none
                                      (__eo_to_smt i) a b hNN)
                                  (by
                                    intro a b a' b' ha hb
                                    exact eo_to_smt_updater_eval_congr
                                      M (__eo_to_smt i) a b a' b' ha hb)
                                  z x (Term.Apply g y) hEqBool hApp
                            case tuple_update =>
                              exact congTrueSpine_tuple_update_eq_true M hM
                                i z x (Term.Apply g y) hEqBool hApp
                        | Term.UOp2 op i j =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.UOp2 op i j) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.UOp3 op i j k =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.UOp3 op i j k) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.__eo_List =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.__eo_List z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.__eo_List_nil =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.__eo_List_nil z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.__eo_List_cons =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.__eo_List_cons z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Bool =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.Bool z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Boolean b =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Boolean b) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Numeral n =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Numeral n) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Rational r =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Rational r) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.String s =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.String s) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Binary w n =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Binary w n) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Type =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.Type z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Stuck =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.Stuck z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Apply f0 a =>
                            cases f0 <;>
                              try
                                exact False.elim
                                  (hHeadTrans
                                    (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                      _ z x (by rfl)
                                      ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                        _ _ hEqBool).2)))
                            case UOp op =>
                              cases op <;>
                                try
                                  exact False.elim
                                    (hHeadTrans
                                      (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                        _ z x (by rfl)
                                        ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                          _ _ hEqBool).2)))
                              case ite =>
                                exact congTrueSpine_ite_eq_true M hM
                                  a z x (Term.Apply g y) hEqBool hApp
                              case bvite =>
                                exact congTrueSpine_bvite_eq_true M hM
                                  a z x (Term.Apply g y) hEqBool hApp
                              case store =>
                                exact
                                  congTrueSpine_non_reg_ternop_eq_true M hM
                                    UserOp.store SmtTerm.store
                                    __smtx_model_eval_store
                                    (by intro a b c; rfl)
                                    store_args_non_reg_of_non_none
                                    (by intro a b c; simp [__smtx_model_eval])
                                    a z x (Term.Apply g y) hEqBool hApp
                              case str_substr =>
                                exact
                                  congTrueSpine_non_reg_ternop_eq_true M hM
                                    UserOp.str_substr SmtTerm.str_substr
                                    __smtx_model_eval_str_substr
                                    (by intro a b c; rfl)
                                    str_substr_args_non_reg_of_non_none
                                    (by intro a b c; rw [__smtx_model_eval.eq_82])
                                    a z x (Term.Apply g y) hEqBool hApp
                              case str_replace =>
                                exact
                                  congTrueSpine_non_reg_ternop_eq_true M hM
                                    UserOp.str_replace SmtTerm.str_replace
                                    __smtx_model_eval_str_replace
                                    (by intro a b c; rfl)
                                    (seq_triop_args_non_reg_of_non_none
                                      SmtTerm.str_replace
                                      (by intro a b c; exact typeof_str_replace_eq a b c))
                                    (by intro a b c; rw [__smtx_model_eval.eq_84])
                                    a z x (Term.Apply g y) hEqBool hApp
                              case str_indexof =>
                                exact
                                  congTrueSpine_non_reg_ternop_eq_true M hM
                                    UserOp.str_indexof SmtTerm.str_indexof
                                    __smtx_model_eval_str_indexof
                                    (by intro a b c; rfl)
                                    str_indexof_args_non_reg_of_non_none
                                    (by intro a b c; rw [__smtx_model_eval.eq_85])
                                    a z x (Term.Apply g y) hEqBool hApp
                              case str_update =>
                                exact
                                  congTrueSpine_non_reg_ternop_eq_true M hM
                                    UserOp.str_update SmtTerm.str_update
                                    __smtx_model_eval_str_update
                                    (by intro a b c; rfl)
                                    str_update_args_non_reg_of_non_none
                                    (by intro a b c; rw [__smtx_model_eval.eq_90])
                                    a z x (Term.Apply g y) hEqBool hApp
                              case str_replace_all =>
                                exact
                                  congTrueSpine_non_reg_ternop_eq_true M hM
                                    UserOp.str_replace_all SmtTerm.str_replace_all
                                    __smtx_model_eval_str_replace_all
                                    (by intro a b c; rfl)
                                    (seq_triop_args_non_reg_of_non_none
                                      SmtTerm.str_replace_all
                                      (by intro a b c; exact typeof_str_replace_all_eq a b c))
                                    (by intro a b c; rw [__smtx_model_eval.eq_100])
                                    a z x (Term.Apply g y) hEqBool hApp
                              case str_replace_re =>
                                exact congTrueSpine_str_replace_re_eq_true M hM
                                  a z x (Term.Apply g y) hEqBool hApp
                              case str_replace_re_all =>
                                exact congTrueSpine_str_replace_re_all_eq_true M hM
                                  a z x (Term.Apply g y) hEqBool hApp
                              case str_indexof_re =>
                                exact congTrueSpine_str_indexof_re_eq_true M hM
                                  a z x (Term.Apply g y) hEqBool hApp
                              case _at_strings_occur_index =>
                                exact
                                  congTrueSpine_strings_occur_index_eq_true M hM
                                    a z x (Term.Apply g y) hEqBool hApp
                              case _at_strings_occur_index_re =>
                                exact
                                  congTrueSpine_strings_occur_index_re_eq_true
                                    M hM a z x (Term.Apply g y) hEqBool hApp
                            case Apply f1 b =>
                              cases f1 <;>
                                try
                                  exact False.elim
                                    (hHeadTrans
                                      (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                        _ z x (by rfl)
                                        ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                          _ _ hEqBool).2)))
                              case UOp op =>
                                cases op <;>
                                  try
                                    exact False.elim
                                      (hHeadTrans
                                        (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                          _ z x (by rfl)
                                          ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                            _ _ hEqBool).2)))
                                case _at_strings_replace_all_result =>
                                  exact
                                    congTrueSpine_strings_replace_all_result_eq_true
                                      M hM b a z x (Term.Apply g y) hEqBool
                                      hApp
                                case _at_strings_replace_re_all_result =>
                                  exact
                                    congTrueSpine_strings_replace_re_all_result_eq_true
                                      M hM b a z x (Term.Apply g y) hEqBool
                                      hApp
                        | Term.FunType =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  Term.FunType z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.Var name T =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.Var name T) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.DatatypeType s d =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DatatypeType s d) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.DatatypeTypeRef s =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DatatypeTypeRef s) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.DtcAppType T U =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DtcAppType T U) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.DtCons s d i =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DtCons s d i) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.DtSel s d i j =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.DtSel s d i j) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.USort u =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.USort u) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))
                        | Term.UConst u T =>
                            exact False.elim
                              (hHeadTrans
                                (eo_apply_apply_head_has_translation_of_generic_apply_translation
                                  (Term.UConst u T) z x (by rfl)
                                  ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                    _ _ hEqBool).2)))


end CongSupport
