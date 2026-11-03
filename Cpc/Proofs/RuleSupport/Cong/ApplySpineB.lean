module

public import Cpc.Proofs.RuleSupport.Cong.ApplySpineA
import all Cpc.Proofs.RuleSupport.Cong.ApplySpineA

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

theorem congTrueSpine_var_apply_apply_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) x₆) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_apply_apply_apply_apply_inv M s T
      x₁ x₂ x₃ x₄ x₅ x₆ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, y₆, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅,
      hArg₆⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let X₅ : SmtTerm := __eo_to_smt x₅
    let X₆ : SmtTerm := __eo_to_smt x₆
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    let Y₅ : SmtTerm := __eo_to_smt y₅
    let Y₆ : SmtTerm := __eo_to_smt y₆
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆)
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                y₃) y₄) y₅) y₆) hEqBool
    have hLeftNN :
        __smtx_typeof
          (mkSmtAppSpineRev F [X₆, X₅, X₄, X₃, X₂, X₁]) ≠
            SmtType.None := by
      exact hTypes.2
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (mkSmtAppSpineRev F [X₆, X₅, X₄, X₃, X₂, X₁]))
        (__smtx_model_eval M
          (mkSmtAppSpineRev F [Y₆, Y₅, Y₄, Y₃, Y₂, Y₁]))
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
        (RuleProofs.smt_value_rel_refl _)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (ListRel.cons hArg₆
          (ListRel.cons hArg₅
            (ListRel.cons hArg₄
              (ListRel.cons hArg₃
                (ListRel.cons hArg₂
                  (ListRel.cons hArg₁ ListRel.nil))))))
        hLeftNN).2

theorem congTrueSpine_uconst_apply_apply_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) x₆) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_apply_apply_apply_apply_inv M i T
      x₁ x₂ x₃ x₄ x₅ x₆ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, y₆, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅,
      hArg₆⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let X₅ : SmtTerm := __eo_to_smt x₅
    let X₆ : SmtTerm := __eo_to_smt x₆
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    let Y₅ : SmtTerm := __eo_to_smt y₅
    let Y₆ : SmtTerm := __eo_to_smt y₆
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆)
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                y₃) y₄) y₅) y₆) hEqBool
    have hLeftNN :
        __smtx_typeof
          (mkSmtAppSpineRev F [X₆, X₅, X₄, X₃, X₂, X₁]) ≠
            SmtType.None := by
      exact hTypes.2
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (mkSmtAppSpineRev F [X₆, X₅, X₄, X₃, X₂, X₁]))
        (__smtx_model_eval M
          (mkSmtAppSpineRev F [Y₆, Y₅, Y₄, Y₃, Y₂, Y₁]))
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
        (RuleProofs.smt_value_rel_refl _)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (ListRel.cons hArg₆
          (ListRel.cons hArg₅
            (ListRel.cons hArg₄
              (ListRel.cons hArg₃
                (ListRel.cons hArg₂
                  (ListRel.cons hArg₁ ListRel.nil))))))
        hLeftNN).2

theorem congTypeSpine_bvsize_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_bvsize) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_unary_uop_inv UserOp._at_bvsize x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y)) := by
    let op : SmtTerm -> SmtTerm := fun a =>
      let w := __eo_to_smt_bv_size (__smtx_typeof a)
      native_ite (native_zleq 0 w)
        (SmtTerm._at_purify (SmtTerm.Numeral w))
        SmtTerm.None
    change
      __smtx_typeof (op (__eo_to_smt x)) =
        __smtx_typeof (op (__eo_to_smt y))
    simp [op, hArgTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)
    (Term.Apply (Term.UOp UserOp._at_bvsize) y)
    hOpTy hTrans

theorem congTrueSpine_bvsize_eq_true
    (M : SmtModel) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp._at_bvsize x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    let op : SmtTerm -> SmtTerm := fun a =>
      let w := __eo_to_smt_bv_size (__smtx_typeof a)
      native_ite (native_zleq 0 w)
        (SmtTerm._at_purify (SmtTerm.Numeral w))
        SmtTerm.None
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (op (__eo_to_smt x)))
        (__smtx_model_eval M (op (__eo_to_smt y)))
    have hTerm :
        op (__eo_to_smt x) = op (__eo_to_smt y) := by
      simp [op, hArgTy]
    rw [hTerm]
    exact RuleProofs.smt_value_rel_refl _

theorem congTrueSpine_or_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs) true :=
  congTrueSpine_bool_binop_eq_true M hM UserOp.or SmtTerm.or
    __smtx_model_eval_or
    (by intro a b; rfl)
    smt_typeof_or_args_bool_of_non_none
    (by intro a b; rw [__smtx_model_eval.eq_8])
    x₁ x₂ rhs

theorem congTypeSpine_or_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs) :=
  congTypeSpine_bool_binop_eq_has_bool_type UserOp.or SmtTerm.or
    (by intro a b; rfl)
    smt_typeof_or_args_bool_of_non_none
    (by
      intro a b ha hb
      rw [typeof_or_eq, ha, hb]
      simp [native_ite, native_Teq])
    x₁ x₂ rhs

theorem congTrueSpine_imp_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs) true :=
  congTrueSpine_bool_binop_eq_true M hM UserOp.imp SmtTerm.imp
    __smtx_model_eval_imp
    (by intro a b; rfl)
    smt_typeof_imp_args_bool_of_non_none
    (by intro a b; rw [__smtx_model_eval.eq_10])
    x₁ x₂ rhs

theorem congTypeSpine_imp_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs) :=
  congTypeSpine_bool_binop_eq_has_bool_type UserOp.imp SmtTerm.imp
    (by intro a b; rfl)
    smt_typeof_imp_args_bool_of_non_none
    (by
      intro a b ha hb
      rw [typeof_imp_eq, ha, hb]
      simp [native_ite, native_Teq])
    x₁ x₂ rhs

theorem congTrueSpine_xor_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs) true :=
  congTrueSpine_bool_binop_eq_true M hM UserOp.xor SmtTerm.xor
    __smtx_model_eval_xor
    (by intro a b; rfl)
    smt_typeof_xor_args_bool_of_non_none
    (by intro a b; rw [__smtx_model_eval.eq_11])
    x₁ x₂ rhs

theorem congTypeSpine_xor_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs) :=
  congTypeSpine_bool_binop_eq_has_bool_type UserOp.xor SmtTerm.xor
    (by intro a b; rfl)
    smt_typeof_xor_args_bool_of_non_none
    (by
      intro a b ha hb
      rw [typeof_xor_eq, ha, hb]
      simp [native_ite, native_Teq])
    x₁ x₂ rhs

theorem arith_overload_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2
            (__smtx_typeof a) (__smtx_typeof b))
    (a b : SmtTerm) :
    __smtx_typeof (op a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases arith_binop_args_of_non_none (op := op) (hTy a b) hTerm with
    hInt | hReal
  · exact ⟨SmtType.Int, SmtType.Int, hInt.1, hInt.2,
      by simp, by simp, by simp, by simp⟩
  · exact ⟨SmtType.Real, SmtType.Real, hReal.1, hReal.2,
      by simp, by simp, by simp, by simp⟩

theorem arith_overload_ret_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (a b : SmtTerm) :
    __smtx_typeof (op a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases arith_binop_ret_args_of_non_none (op := op) (R := R)
      (hTy a b) hTerm with
    hInt | hReal
  · exact ⟨SmtType.Int, SmtType.Int, hInt.1, hInt.2,
      by simp, by simp, by simp, by simp⟩
  · exact ⟨SmtType.Real, SmtType.Real, hReal.1, hReal.2,
      by simp, by simp, by simp, by simp⟩

theorem int_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Int)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.Int)
              R SmtType.None)
            SmtType.None)
    (a b : SmtTerm) :
    __smtx_typeof (op a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    exact hNN
  have hArgs := int_binop_args_of_non_none (op := op) (R := R)
    (hTy a b) hTerm
  exact ⟨SmtType.Int, SmtType.Int, hArgs.1, hArgs.2,
    by simp, by simp, by simp, by simp⟩

theorem arith_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_arith_overload_op_1 (__smtx_typeof a))
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases arith_unop_arg_of_non_none (op := op) (hTy a) hTerm with
    hInt | hReal
  · exact ⟨SmtType.Int, hInt, by simp, by simp⟩
  · exact ⟨SmtType.Real, hReal, by simp, by simp⟩

theorem int_ret_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Int)
            R SmtType.None)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  have hArg := int_ret_arg_of_non_none (op := op) (R := R)
    (hTy a) hTerm
  exact ⟨SmtType.Int, hArg, by simp, by simp⟩

theorem real_ret_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Real)
            R SmtType.None)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  have hArg := real_arg_of_non_none (op := op) (Tout := R)
    (hTy a) hTerm
  exact ⟨SmtType.Real, hArg, by simp, by simp⟩

theorem to_real_args_non_reg_of_non_none
    (a : SmtTerm) :
    __smtx_typeof (SmtTerm.to_real a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.to_real a) := by
    unfold term_has_non_none_type
    exact hNN
  have hInt := to_real_arg_of_non_none hTerm
  exact ⟨SmtType.Int, hInt, by simp, by simp⟩

noncomputable abbrev smtEvalDiv
    (M : SmtModel) (x₁ x₂ : SmtValue) : SmtValue :=
  let _v0 := x₂
  let _v1 := x₁
  __smtx_model_eval_ite
    (__smtx_model_eval_eq _v0 (SmtValue.Numeral 0))
      (__smtx_model_eval_apply M
      (native_model_lookup M native_div_by_zero_id
        (SmtType.FunType SmtType.Int SmtType.Int))
      _v1)
    (__smtx_model_eval_div_total _v1 _v0)

noncomputable abbrev smtEvalMod
    (M : SmtModel) (x₁ x₂ : SmtValue) : SmtValue :=
  let _v0 := x₂
  let _v1 := x₁
  __smtx_model_eval_ite
    (__smtx_model_eval_eq _v0 (SmtValue.Numeral 0))
      (__smtx_model_eval_apply M
      (native_model_lookup M native_mod_by_zero_id
        (SmtType.FunType SmtType.Int SmtType.Int))
      _v1)
    (__smtx_model_eval_mod_total _v1 _v0)

noncomputable abbrev smtEvalQdiv
    (M : SmtModel) (x₁ x₂ : SmtValue) : SmtValue :=
  let _v0 := x₂
  let _v1 := x₁
  let _v0r := __smtx_to_real_coerce _v0
  let _v1r := __smtx_to_real_coerce _v1
  __smtx_model_eval_ite
    (__smtx_model_eval_eq _v0r
      (SmtValue.Rational (native_mk_rational 0 1)))
      (__smtx_model_eval_apply M
      (native_model_lookup M native_qdiv_by_zero_id
        (SmtType.FunType SmtType.Real SmtType.Real))
      _v1r)
    (__smtx_model_eval_qdiv_total _v1r _v0r)

theorem div_by_zero_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (SmtTerm.div a (SmtTerm.Numeral 0)) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  rcases int_binop_args_non_reg_of_non_none SmtTerm.div SmtType.Int
      (by intro x y; exact typeof_div_eq x y)
      a (SmtTerm.Numeral 0) hNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

theorem mod_by_zero_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (SmtTerm.mod a (SmtTerm.Numeral 0)) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  rcases int_binop_args_non_reg_of_non_none SmtTerm.mod SmtType.Int
      (by intro x y; exact typeof_mod_eq x y)
      a (SmtTerm.Numeral 0) hNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

theorem qdiv_by_zero_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof
        (SmtTerm.qdiv a (SmtTerm.Rational (native_mk_rational 0 1))) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  rcases arith_overload_ret_binop_args_non_reg_of_non_none
      SmtTerm.qdiv SmtType.Real
      (by intro x y; exact typeof_qdiv_eq x y)
      a (SmtTerm.Rational (native_mk_rational 0 1)) hNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

theorem bv_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_bv_op_1 (__smtx_typeof a))
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases bv_unop_arg_of_non_none (op := op) (hTy a) hTerm with
    ⟨w, hA⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

theorem bv_unop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_bv_op_1_ret (__smtx_typeof a) R)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases bv_unop_ret_arg_of_non_none (op := op) (ret := R)
      (hTy a) hTerm with
    ⟨w, hA⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

theorem extract_arg_non_reg_of_non_none
    (i j a : SmtTerm) :
    __smtx_typeof (SmtTerm.extract i j a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.extract i j a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases extract_args_of_non_none hTerm with
    ⟨_hi, _hj, w, _hI, _hJ, hA, _hj0, _hji, _hiw⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

theorem repeat_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.repeat i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.repeat i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases repeat_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

theorem zero_extend_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.zero_extend i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.zero_extend i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases zero_extend_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

theorem sign_extend_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.sign_extend i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.sign_extend i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases sign_extend_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

theorem rotate_left_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.rotate_left i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.rotate_left i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases rotate_left_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

theorem rotate_right_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.rotate_right i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.rotate_right i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases rotate_right_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

theorem int_to_bv_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.int_to_bv i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.int_to_bv i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases int_to_bv_args_of_non_none hTerm with
    ⟨_i, _hI, hA, _hi⟩
  exact ⟨SmtType.Int, hA, by simp, by simp⟩

theorem is_arg_non_reg_of_non_none
    (idx : Term) (a : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx)) a) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTester :
      (∃ s d i,
          __eo_to_smt_tester (__eo_to_smt idx) =
            SmtTerm.DtTester s d i) ∨
        __eo_to_smt_tester (__eo_to_smt idx) = SmtTerm.None := by
    cases __eo_to_smt idx <;> simp [__eo_to_smt_tester]
  rcases hTester with ⟨s, d, i, hTester⟩ | hTester
  · have hTerm :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtTester s d i) a) := by
      unfold term_has_non_none_type
      simpa [hTester] using hNN
    exact ⟨SmtType.Datatype s d,
      dt_tester_arg_datatype_of_non_none hTerm, by simp, by simp⟩
  · exfalso
    apply hNN
    simp [hTester, __smtx_typeof, __smtx_typeof_apply]

theorem dt_sel_arg_non_reg_of_non_none
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (a : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) a) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hSel :
      (∃ (ss : native_String) (dd : SmtDatatypeDecl) (ii jj : native_Nat),
          __eo_to_smt (Term.DtSel s d i j) =
            SmtTerm.DtSel ss dd ii jj) ∨
        __eo_to_smt (Term.DtSel s d i j) = SmtTerm.None := by
    rw [TranslationProofs.eo_to_smt_term_dt_sel]
    cases TranslationProofs.__eo_reserved_datatype_name s <;>
      simp [native_ite]
  rcases hSel with ⟨ss, dd, ii, jj, hSel⟩ | hSel
  · have hTerm :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel ss dd ii jj) a) := by
      unfold term_has_non_none_type
      simpa [hSel] using hNN
    exact ⟨SmtType.Datatype ss dd,
      dt_sel_arg_datatype_of_non_none hTerm, by simp, by simp⟩
  · exfalso
    apply hNN
    simp [hSel, __smtx_typeof, __smtx_typeof_apply]

private theorem smt_apply_same_head_type_congr
    (f x y : SmtTerm) :
    __smtx_typeof x = __smtx_typeof y ->
      __smtx_typeof (SmtTerm.Apply f x) =
        __smtx_typeof (SmtTerm.Apply f y) := by
  intro h
  cases f <;> simp [__smtx_typeof, __smtx_typeof_apply, h]

private theorem eo_to_smt_updater_rec_type_congr
    (sel : SmtTerm) (n : native_Nat)
    (t u acc t' u' : SmtTerm) :
    __smtx_typeof t = __smtx_typeof t' ->
    __smtx_typeof u = __smtx_typeof u' ->
      __smtx_typeof (__eo_to_smt_updater_rec sel n t u acc) =
        __smtx_typeof (__eo_to_smt_updater_rec sel n t' u' acc) := by
  intro ht hu
  induction n generalizing acc with
  | zero =>
      cases sel <;> simp [__eo_to_smt_updater_rec]
  | succ k ih =>
      cases sel <;> simp [__eo_to_smt_updater_rec]
      case DtSel s d i j =>
        have hArg :
            __smtx_typeof
                (native_ite (native_nateq j k) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)) =
              __smtx_typeof
                (native_ite (native_nateq j k) u'
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t')) := by
          cases hEq : native_nateq j k <;>
            simp [native_ite, ht, hu, __smtx_typeof,
              __smtx_typeof_apply]
        cases k with
        | zero =>
            simpa [__eo_to_smt_updater_rec] using
              smt_apply_same_head_type_congr acc
                (native_ite (native_nateq j 0) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i 0) t))
                (native_ite (native_nateq j 0) u'
                  (SmtTerm.Apply (SmtTerm.DtSel s d i 0) t')) hArg
        | succ k' =>
            have hGeneric :
                generic_apply_type
                  (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                    (Nat.succ k') t u acc)
                  (native_ite (native_nateq j (Nat.succ k')) u
                    (SmtTerm.Apply (SmtTerm.DtSel s d i (Nat.succ k')) t)) :=
              generic_apply_type_of_non_datatype_head
                (by intro s0 d0 i0 j0 h; cases h)
                (by intro s0 d0 i0 h; cases h)
            have hGeneric' :
                generic_apply_type
                  (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                    (Nat.succ k') t' u' acc)
                  (native_ite (native_nateq j (Nat.succ k')) u'
                    (SmtTerm.Apply (SmtTerm.DtSel s d i (Nat.succ k')) t')) :=
              generic_apply_type_of_non_datatype_head
                (by intro s0 d0 i0 j0 h; cases h)
                (by intro s0 d0 i0 h; cases h)
            unfold generic_apply_type at hGeneric hGeneric'
            simp [native_ite] at hGeneric hGeneric' hArg
            rw [hGeneric, hGeneric']
            rw [ih acc]
            rw [hArg]

private abbrev smtx_decl_num_sels
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    native_Nat :=
  __smtx_dt_num_sels (__smtx_dd_lookup s d) i

theorem eo_to_smt_updater_type_congr
    (sel t u t' u' : SmtTerm) :
    __smtx_typeof t = __smtx_typeof t' ->
    __smtx_typeof u = __smtx_typeof u' ->
      __smtx_typeof (__eo_to_smt_updater sel t u) =
        __smtx_typeof (__eo_to_smt_updater sel t' u') := by
  intro ht hu
  cases sel
  case DtSel s d i j =>
    cases hGuard :
        native_zlt (native_nat_to_int j)
          (native_nat_to_int (smtx_decl_num_sels s d i))
    case false =>
      simp [__eo_to_smt_updater, native_ite, hGuard]
    case true =>
      have hUpdater :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t u =
            SmtTerm.ite
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t)
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (smtx_decl_num_sels s d i) t u (SmtTerm.DtCons s d i))
              t := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      have hUpdater' :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t' u' =
            SmtTerm.ite
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t')
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (smtx_decl_num_sels s d i) t' u' (SmtTerm.DtCons s d i))
              t' := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      rw [hUpdater, hUpdater']
      rw [typeof_ite_eq, typeof_ite_eq]
      have hCond :
          __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) t) =
            __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) t') := by
        simp [__smtx_typeof, __smtx_typeof_apply, ht]
      have hThen :
          __smtx_typeof
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (smtx_decl_num_sels s d i) t u (SmtTerm.DtCons s d i)) =
            __smtx_typeof
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (smtx_decl_num_sels s d i) t' u' (SmtTerm.DtCons s d i)) :=
        eo_to_smt_updater_rec_type_congr
          (SmtTerm.DtSel s d i j) (smtx_decl_num_sels s d i)
          t u (SmtTerm.DtCons s d i) t' u' ht hu
      rw [hCond, hThen, ht]
  all_goals simp [__eo_to_smt_updater]

private theorem eo_to_smt_tuple_update_type_congr
    (T T' : SmtType) (idx t u t' u' : SmtTerm) :
    T = T' ->
    __smtx_typeof t = __smtx_typeof t' ->
    __smtx_typeof u = __smtx_typeof u' ->
      __smtx_typeof (__eo_to_smt_tuple_update T idx t u) =
        __smtx_typeof (__eo_to_smt_tuple_update T' idx t' u') := by
  intro hT ht hu
  subst T'
  cases T <;> cases idx <;>
    try simp [__eo_to_smt_tuple_update]
  case Datatype.Numeral s dd n =>
    cases dd with
    | nil =>
        simp
    | cons s2 body rest =>
        cases rest with
        | nil =>
            by_cases hCond :
                (s = native_string_lit "@Tuple" ∧
                  s2 = native_string_lit "@Tuple") ∧
                    native_zleq 0 n = true
            · simp [hCond]
              exact eo_to_smt_updater_type_congr
                (SmtTerm.DtSel (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl body) native_nat_zero
                  (native_int_to_nat n))
                t u t' u' ht hu
            · simp [hCond]
        | cons s3 body3 rest3 =>
            simp

theorem congTypeSpine_tuple_update_eq_has_bool_type
    (idx x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_indexed_binary_uop1_inv
      UserOp1.tuple_update idx x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgEoTy₁ : __eo_typeof x₁ = __eo_typeof y₁ :=
    eo_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) y₁) y₂)) := by
    change
      __smtx_typeof
          (__eo_to_smt_tuple_update
            (__smtx_typeof (__eo_to_smt x₁)) (__eo_to_smt idx)
            (__eo_to_smt x₁) (__eo_to_smt x₂)) =
        __smtx_typeof
          (__eo_to_smt_tuple_update
            (__smtx_typeof (__eo_to_smt y₁)) (__eo_to_smt idx)
            (__eo_to_smt y₁) (__eo_to_smt y₂))
    exact eo_to_smt_tuple_update_type_congr
      (__smtx_typeof (__eo_to_smt x₁))
      (__smtx_typeof (__eo_to_smt y₁))
      (__eo_to_smt idx) (__eo_to_smt x₁) (__eo_to_smt x₂)
      (__eo_to_smt y₁) (__eo_to_smt y₂)
      hArgTy₁ hArgTy₁ hArgTy₂
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) y₁) y₂)
    hOpTy
    hTrans

private theorem smtx_apply_arg_non_reg_of_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    ∃ A,
      __smtx_typeof x = A ∧ A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
        SmtType.None := by
    cases f
    case DtSel s d i j =>
      exact False.elim (hSel s d i j rfl)
    case DtTester s d i =>
      exact False.elim (hTester s d i rfl)
    all_goals
      simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with
    ⟨A, B, hHead, hArg, hA, _hB⟩
  have hFNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    exact smt_type_ne_none_of_apply_head hHead
  have hANeReg : A ≠ SmtType.RegLan :=
    Smtm.smt_term_fun_like_arg_ne_reglan_of_non_none
      f hFNN hHead
  exact ⟨A, hArg, hA, hANeReg⟩

private theorem eo_to_smt_updater_rec_ne_dt_sel
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat)
    (t u acc : SmtTerm)
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (s0 : native_String) (d0 : SmtDatatypeDecl) (i0 j0 : native_Nat) :
    __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc ≠
      SmtTerm.DtSel s0 d0 i0 j0 := by
  intro h
  cases n with
  | zero =>
      simpa [__eo_to_smt_updater_rec] using hAccSel s0 d0 i0 j0 h
  | succ _ =>
      cases h

private theorem eo_to_smt_updater_rec_ne_dt_tester
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat)
    (t u acc : SmtTerm)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (s0 : native_String) (d0 : SmtDatatypeDecl) (i0 : native_Nat) :
    __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc ≠
      SmtTerm.DtTester s0 d0 i0 := by
  intro h
  cases n with
  | zero =>
      simpa [__eo_to_smt_updater_rec] using hAccTester s0 d0 i0 h
  | succ _ =>
      cases h

private theorem eo_to_smt_updater_rec_update_arg_non_reg_of_non_none
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat)
    (t u acc : SmtTerm)
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (hIdx :
      native_zlt (native_nat_to_int j) (native_nat_to_int n) = true)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc) ≠
        SmtType.None) :
    ∃ B,
      __smtx_typeof u = B ∧ B ≠ SmtType.None ∧ B ≠ SmtType.RegLan := by
  induction n generalizing acc with
  | zero =>
      have hj : (j : Int) < 0 := by
        -- `simp` rewrites inside `decide`'s `Prop` argument but leaves the
        -- `Decidable` instance stale, so `decide_eq_true_eq` no longer fires on
        -- the hypothesis; strip the `decide` explicitly instead.
        have h := hIdx
        simp [native_zlt, SmtEval.native_zlt, native_nat_to_int,
          SmtEval.native_nat_to_int] at h
        exact of_decide_eq_true h
      have hjNonneg : (0 : Int) ≤ j := Int.natCast_nonneg j
      omega
  | succ k ih =>
      let recTerm :=
        __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u acc
      let argTerm :=
        native_ite (native_nateq j k) u
          (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)
      have hTermNN :
          __smtx_typeof (SmtTerm.Apply recTerm argTerm) ≠ SmtType.None := by
        simpa [__eo_to_smt_updater_rec, recTerm, argTerm] using hNN
      have hRecSel :
          ∀ s0 d0 i0 j0, recTerm ≠ SmtTerm.DtSel s0 d0 i0 j0 := by
        exact eo_to_smt_updater_rec_ne_dt_sel s d i j k t u acc hAccSel
      have hRecTester :
          ∀ s0 d0 i0, recTerm ≠ SmtTerm.DtTester s0 d0 i0 := by
        exact eo_to_smt_updater_rec_ne_dt_tester s d i j k t u acc
          hAccTester
      by_cases hEq : native_nateq j k = true
      · rcases smtx_apply_arg_non_reg_of_non_none recTerm argTerm
            hRecSel hRecTester hTermNN with
          ⟨B, hArgB, hBNN, hBReg⟩
        exact ⟨B, by simpa [argTerm, native_ite, hEq] using hArgB,
          hBNN, hBReg⟩
      · have hIdxK :
            native_zlt (native_nat_to_int j) (native_nat_to_int k) = true := by
          have hjk : j < k := by
            have hjSucc : j < Nat.succ k := by
              have hjSuccInt : (j : Int) < (Nat.succ k : Int) := by
                have h := hIdx
                simp [native_zlt, SmtEval.native_zlt, native_nat_to_int,
                  SmtEval.native_nat_to_int] at h
                exact of_decide_eq_true h
              exact Int.ofNat_lt.mp hjSuccInt
            have hne : j ≠ k := by
              intro h
              subst j
              simp [native_nateq, SmtEval.native_nateq] at hEq
            exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjSucc) hne
          have hjkInt : (j : Int) < (k : Int) := Int.ofNat_lt.mpr hjk
          simpa [native_zlt, SmtEval.native_zlt, native_nat_to_int,
            SmtEval.native_nat_to_int] using hjkInt
        have hGeneric : generic_apply_type recTerm argTerm :=
          generic_apply_type_of_non_datatype_head hRecSel hRecTester
        have hApplyNN :
            __smtx_typeof_apply (__smtx_typeof recTerm)
                (__smtx_typeof argTerm) ≠
              SmtType.None := by
          unfold generic_apply_type at hGeneric
          rw [hGeneric] at hTermNN
          exact hTermNN
        have hRecNN :
            __smtx_typeof recTerm ≠ SmtType.None :=
          smt_apply_head_non_none_of_apply_non_none hApplyNN
        exact ih acc hAccSel hAccTester hIdxK
          (by simpa [recTerm] using hRecNN)

theorem updater_args_non_reg_of_non_none
    (sel t u : SmtTerm) :
    __smtx_typeof (__eo_to_smt_updater sel t u) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof t = A ∧ __smtx_typeof u = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  cases sel
  case DtSel s d i j =>
    have hIdx :
        native_zlt (native_nat_to_int j)
            (native_nat_to_int (smtx_decl_num_sels s d i)) =
          true :=
      TranslationProofs.eo_to_smt_updater_dt_sel_guard_of_non_none
        s d i j t u hNN
    have hIteNN :
        term_has_non_none_type
          (SmtTerm.ite
            (SmtTerm.Apply (SmtTerm.DtTester s d i) t)
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
              (smtx_decl_num_sels s d i) t u (SmtTerm.DtCons s d i))
            t) := by
      unfold term_has_non_none_type
      simpa [__eo_to_smt_updater, native_ite, hIdx] using hNN
    rcases ite_args_of_non_none hIteNN with
      ⟨T, hCond, hThen, _hElse, hTNN⟩
    have hCondNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtTester s d i) t) := by
      unfold term_has_non_none_type
      rw [hCond]
      simp
    have htTy : __smtx_typeof t = SmtType.Datatype s d :=
      dt_tester_arg_datatype_of_non_none hCondNN
    have hRecNN :
        __smtx_typeof
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
              (smtx_decl_num_sels s d i) t u (SmtTerm.DtCons s d i)) ≠
          SmtType.None := by
      rw [hThen]
      exact hTNN
    rcases eo_to_smt_updater_rec_update_arg_non_reg_of_non_none
        s d i j (smtx_decl_num_sels s d i) t u (SmtTerm.DtCons s d i)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hIdx hRecNN with
      ⟨B, huB, hBNN, hBReg⟩
    exact ⟨SmtType.Datatype s d, B, htTy, huB, by simp, hBNN,
      by simp, hBReg⟩
  all_goals
    exfalso
    apply hNN
    simp [__eo_to_smt_updater]

private theorem smt_apply_same_head_eval_congr
    (M : SmtModel) (f x y : SmtTerm) :
    __smtx_model_eval M x = __smtx_model_eval M y ->
      __smtx_model_eval M (SmtTerm.Apply f x) =
        __smtx_model_eval M (SmtTerm.Apply f y) := by
  intro h
  cases f <;> simp [__smtx_model_eval, h]

private theorem eo_to_smt_updater_rec_eval_congr
    (M : SmtModel) (sel : SmtTerm) (n : native_Nat)
    (t u acc t' u' : SmtTerm) :
    __smtx_model_eval M t = __smtx_model_eval M t' ->
    __smtx_model_eval M u = __smtx_model_eval M u' ->
      __smtx_model_eval M (__eo_to_smt_updater_rec sel n t u acc) =
        __smtx_model_eval M (__eo_to_smt_updater_rec sel n t' u' acc) := by
  intro ht hu
  induction n generalizing acc with
  | zero =>
      cases sel <;> simp [__eo_to_smt_updater_rec]
  | succ k ih =>
      cases sel <;> simp [__eo_to_smt_updater_rec]
      case DtSel s d i j =>
        have hArg :
            __smtx_model_eval M
                (native_ite (native_nateq j k) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)) =
              __smtx_model_eval M
                (native_ite (native_nateq j k) u'
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t')) := by
          cases hEq : native_nateq j k <;>
            simp [native_ite, ht, hu, __smtx_model_eval]
        cases k with
        | zero =>
            simpa [__eo_to_smt_updater_rec] using
              smt_apply_same_head_eval_congr M acc
                (native_ite (native_nateq j 0) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i 0) t))
                (native_ite (native_nateq j 0) u'
                  (SmtTerm.Apply (SmtTerm.DtSel s d i 0) t')) hArg
        | succ k' =>
            have hGeneric :
                generic_apply_eval
                  (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                    (Nat.succ k') t u acc)
                  (native_ite (native_nateq j (Nat.succ k')) u
                    (SmtTerm.Apply (SmtTerm.DtSel s d i (Nat.succ k')) t)) :=
              generic_apply_eval_of_non_datatype_head
                (by intro s0 d0 i0 j0 h; cases h)
                (by intro s0 d0 i0 h; cases h)
            have hGeneric' :
                generic_apply_eval
                  (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                    (Nat.succ k') t' u' acc)
                  (native_ite (native_nateq j (Nat.succ k')) u'
                    (SmtTerm.Apply (SmtTerm.DtSel s d i (Nat.succ k')) t')) :=
              generic_apply_eval_of_non_datatype_head
                (by intro s0 d0 i0 j0 h; cases h)
                (by intro s0 d0 i0 h; cases h)
            unfold generic_apply_eval at hGeneric hGeneric'
            simp [native_ite] at hGeneric hGeneric' hArg
            rw [hGeneric M, hGeneric' M]
            rw [ih acc, hArg]

theorem eo_to_smt_updater_eval_congr
    (M : SmtModel) (sel t u t' u' : SmtTerm) :
    __smtx_model_eval M t = __smtx_model_eval M t' ->
    __smtx_model_eval M u = __smtx_model_eval M u' ->
      __smtx_model_eval M (__eo_to_smt_updater sel t u) =
        __smtx_model_eval M (__eo_to_smt_updater sel t' u') := by
  intro ht hu
  cases sel
  case DtSel s d i j =>
    cases hGuard :
        native_zlt (native_nat_to_int j)
          (native_nat_to_int (smtx_decl_num_sels s d i))
    case false =>
      simp [__eo_to_smt_updater, native_ite, hGuard]
    case true =>
      have hUpdater :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t u =
            SmtTerm.ite
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t)
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (smtx_decl_num_sels s d i) t u (SmtTerm.DtCons s d i))
              t := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      have hUpdater' :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t' u' =
            SmtTerm.ite
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t')
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (smtx_decl_num_sels s d i) t' u' (SmtTerm.DtCons s d i))
              t' := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      rw [hUpdater, hUpdater']
      have hCond :
          __smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtTester s d i) t) =
            __smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtTester s d i) t') :=
        smt_apply_same_head_eval_congr M (SmtTerm.DtTester s d i) t t' ht
      have hThen :
          __smtx_model_eval M
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (smtx_decl_num_sels s d i) t u (SmtTerm.DtCons s d i)) =
            __smtx_model_eval M
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (smtx_decl_num_sels s d i) t' u' (SmtTerm.DtCons s d i)) :=
        eo_to_smt_updater_rec_eval_congr M
          (SmtTerm.DtSel s d i j) (smtx_decl_num_sels s d i)
          t u (SmtTerm.DtCons s d i) t' u' ht hu
      rw [smtx_model_eval_ite_term_eq, smtx_model_eval_ite_term_eq]
      rw [hCond, hThen, ht]
  all_goals simp [__eo_to_smt_updater]

theorem congTrueSpine_non_reg_indexed_binary_uop1_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp1) (idx : Term)
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hArgsOfNN :
      ∀ a b,
        __smtx_typeof (smtOp a b) ≠ SmtType.None ->
          ∃ A B,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan)
    (hEvalCong :
      ∀ a b a' b',
        __smtx_model_eval M a = __smtx_model_eval M a' ->
        __smtx_model_eval M b = __smtx_model_eval M b' ->
          __smtx_model_eval M (smtOp a b) =
            __smtx_model_eval M (smtOp a' b'))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂) rhs)
      true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed_binary_uop1_inv M eoOp idx x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp1 eoOp idx) y₁) y₂) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      rw [← hToSmt x₁ x₂]
      exact hTypes.2
    rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
      ⟨A, B, hx₁A, hx₂B, hANN, hBNN, hAReg, hBReg⟩
    have hy₁A : __smtx_typeof (__eo_to_smt y₁) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁A
    have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂B
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        A hx₁A hy₁A hANN hAReg hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        B hx₂B hy₂B hBNN hBReg hArg₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    rw [hEvalCong (__eo_to_smt x₁) (__eo_to_smt x₂)
      (__eo_to_smt y₁) (__eo_to_smt y₂) hEval₁ hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

private theorem eo_to_smt_tuple_update_eval_congr
    (M : SmtModel) (T T' : SmtType) (idx t u t' u' : SmtTerm) :
    T = T' ->
    __smtx_model_eval M t = __smtx_model_eval M t' ->
    __smtx_model_eval M u = __smtx_model_eval M u' ->
      __smtx_model_eval M (__eo_to_smt_tuple_update T idx t u) =
        __smtx_model_eval M (__eo_to_smt_tuple_update T' idx t' u') := by
  intro hT ht hu
  subst T'
  cases T <;> cases idx <;>
    try simp [__eo_to_smt_tuple_update]
  case Datatype.Numeral s dd n =>
    cases dd with
    | nil =>
        simp
    | cons s2 body rest =>
        cases rest with
        | nil =>
            by_cases hCond :
                (s = native_string_lit "@Tuple" ∧
                  s2 = native_string_lit "@Tuple") ∧
                    native_zleq 0 n = true
            · simp [hCond]
              exact eo_to_smt_updater_eval_congr M
                (SmtTerm.DtSel (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl body) native_nat_zero
                  (native_int_to_nat n))
                t u t' u' ht hu
            · simp [hCond]
        | cons s3 body3 rest3 =>
            simp

theorem tuple_update_args_non_reg_of_non_none
    (T : SmtType) (idx t u : SmtTerm) :
    __smtx_typeof (__eo_to_smt_tuple_update T idx t u) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof t = A ∧ __smtx_typeof u = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  cases T <;> cases idx
  case Datatype.Numeral s dd n =>
    cases dd with
    | nil =>
        exfalso
        apply hNN
        simp [__eo_to_smt_tuple_update]
    | cons s2 body rest =>
        cases rest with
        | nil =>
            by_cases hCond :
                (s = native_string_lit "@Tuple" ∧
                  s2 = native_string_lit "@Tuple") ∧
                    native_zleq 0 n = true
            · have hUpdaterNN :
                  __smtx_typeof
                      (__eo_to_smt_updater
                        (SmtTerm.DtSel (native_string_lit "@Tuple")
                          (__eo_to_smt_tuple_decl body) native_nat_zero
                          (native_int_to_nat n)) t u) ≠
                    SmtType.None := by
                simpa [__eo_to_smt_tuple_update, hCond] using hNN
              exact updater_args_non_reg_of_non_none
                (SmtTerm.DtSel (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl body) native_nat_zero
                  (native_int_to_nat n))
                t u hUpdaterNN
            · exfalso
              apply hNN
              simp [__eo_to_smt_tuple_update, hCond]
        | cons s3 body3 rest3 =>
            exfalso
            apply hNN
            simp [__eo_to_smt_tuple_update]
  all_goals
    exfalso
    apply hNN
    simp [__eo_to_smt_tuple_update]

theorem congTrueSpine_tuple_update_eq_true
    (M : SmtModel) (hM : model_wf M)
    (idx x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed_binary_uop1_inv
      M UserOp1.tuple_update idx x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) y₁) y₂)
        hEqBool
    have hxOpNN :
        __smtx_typeof
            (__eo_to_smt_tuple_update
              (__smtx_typeof (__eo_to_smt x₁)) (__eo_to_smt idx)
              (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      change
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x₁)
                x₂)) ≠
          SmtType.None
      exact hTypes.2
    rcases tuple_update_args_non_reg_of_non_none
        (__smtx_typeof (__eo_to_smt x₁)) (__eo_to_smt idx)
        (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
      ⟨A, B, hx₁A, hx₂B, hANN, hBNN, hAReg, hBReg⟩
    have hy₁A : __smtx_typeof (__eo_to_smt y₁) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁A
    have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂B
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        A hx₁A hy₁A hANN hAReg hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        B hx₂B hy₂B hBNN hBReg hArg₂
    have hArgEoTy₁ : __eo_typeof x₁ = __eo_typeof y₁ :=
      eo_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt_tuple_update
            (__smtx_typeof (__eo_to_smt x₁)) (__eo_to_smt idx)
            (__eo_to_smt x₁) (__eo_to_smt x₂)))
        (__smtx_model_eval M
          (__eo_to_smt_tuple_update
            (__smtx_typeof (__eo_to_smt y₁)) (__eo_to_smt idx)
            (__eo_to_smt y₁) (__eo_to_smt y₂))) =
        SmtValue.Boolean true
    rw [eo_to_smt_tuple_update_eval_congr M
      (__smtx_typeof (__eo_to_smt x₁))
      (__smtx_typeof (__eo_to_smt y₁))
      (__eo_to_smt idx) (__eo_to_smt x₁) (__eo_to_smt x₂)
      (__eo_to_smt y₁) (__eo_to_smt y₂)
      (smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁) hEval₁ hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

private theorem eo_to_smt_tuple_prepend_rec_ne_dt_sel
    (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i j, acc ≠ SmtTerm.DtSel s d i j) ->
        ∀ s d i j,
          __eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
            tailD tail k acc ≠
            SmtTerm.DtSel s d i j
  | native_nat_zero, acc, hAcc, s, d, i, j => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc s d i j
  | native_nat_succ _k, _acc, _hAcc, _s, _d, _i, _j => by
      intro h
      cases h

private theorem eo_to_smt_tuple_prepend_rec_ne_dt_tester
    (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i, acc ≠ SmtTerm.DtTester s d i) ->
        ∀ s d i,
          __eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
            tailD tail k acc ≠
            SmtTerm.DtTester s d i
  | native_nat_zero, acc, hAcc, s, d, i => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc s d i
  | native_nat_succ _k, _acc, _hAcc, _s, _d, _i => by
      intro h
      cases h

private theorem eo_to_smt_tuple_prepend_rec_type_congr
    (tailD : SmtDatatype) (tail tail' acc acc' : SmtTerm)
    (hTail : __smtx_typeof tail = __smtx_typeof tail')
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (hAcc'Sel : ∀ s d i j, acc' ≠ SmtTerm.DtSel s d i j)
    (hAcc'Tester : ∀ s d i, acc' ≠ SmtTerm.DtTester s d i)
    (hAcc : __smtx_typeof acc = __smtx_typeof acc') :
    ∀ k,
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
            tailD tail k acc) =
        __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
            tailD tail' k acc')
  | native_nat_zero => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc
  | native_nat_succ k => by
      let recTerm :=
        __eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
          tailD tail k acc
      let recTerm' :=
        __eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
          tailD tail' k acc'
      let argTerm :=
        SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero k) tail
      let argTerm' :=
        SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero k) tail'
      have hRecTy : __smtx_typeof recTerm = __smtx_typeof recTerm' := by
        simpa [recTerm, recTerm'] using
          eo_to_smt_tuple_prepend_rec_type_congr tailD tail tail' acc acc'
            hTail hAccSel hAccTester hAcc'Sel hAcc'Tester hAcc k
      have hArgTy : __smtx_typeof argTerm = __smtx_typeof argTerm' := by
        simp [argTerm, argTerm', __smtx_typeof, hTail]
      have hGen : generic_apply_type recTerm argTerm :=
        generic_apply_type_of_non_datatype_head
          (by
            intro s d i j h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_sel tailD tail k acc
                hAccSel s d i j (by simpa [recTerm] using h))
          (by
            intro s d i h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_tester tailD tail k acc
                hAccTester s d i (by simpa [recTerm] using h))
      have hGen' : generic_apply_type recTerm' argTerm' :=
        generic_apply_type_of_non_datatype_head
          (by
            intro s d i j h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_sel tailD tail' k acc'
                hAcc'Sel s d i j (by simpa [recTerm'] using h))
          (by
            intro s d i h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_tester tailD tail' k acc'
                hAcc'Tester s d i (by simpa [recTerm'] using h))
      unfold generic_apply_type at hGen hGen'
      change
        __smtx_typeof (SmtTerm.Apply recTerm argTerm) =
          __smtx_typeof (SmtTerm.Apply recTerm' argTerm')
      rw [hGen, hGen', hRecTy, hArgTy]

private theorem eo_to_smt_tuple_prepend_type_congr
    (head head' tail tail' : SmtTerm) (headTy headTy' : SmtType) :
    __smtx_typeof head = __smtx_typeof head' ->
    headTy = headTy' ->
    __smtx_typeof tail = __smtx_typeof tail' ->
      __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
        __smtx_typeof (__eo_to_smt_tuple_prepend head' headTy' tail') := by
  intro hHead hHeadTy hTail
  subst headTy'
  unfold __eo_to_smt_tuple_prepend
  rw [← hTail]
  cases hTailTy : __smtx_typeof tail with
  | Datatype s dd =>
      cases dd with
      | nil =>
          simp [__eo_to_smt_tuple_prepend_of_type]
      | cons s2 body rest =>
          cases rest with
          | cons s3 body3 rest3 =>
              simp [__eo_to_smt_tuple_prepend_of_type]
          | nil =>
              cases body with
              | null =>
                  simp [__eo_to_smt_tuple_prepend_of_type]
              | sum c bodyRest =>
                  cases bodyRest with
                  | sum c' bodyRest' =>
                      simp [__eo_to_smt_tuple_prepend_of_type]
                  | null =>
                      by_cases hs : s = native_string_lit "@Tuple"
                      · subst s
                        by_cases hs2 : s2 = native_string_lit "@Tuple"
                        · subst s2
                          let tailD := SmtDatatype.sum c SmtDatatype.null
                          let fullD :=
                            SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                              SmtDatatype.null
                          let seed :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons (native_string_lit "@Tuple")
                                (__eo_to_smt_tuple_decl fullD)
                                native_nat_zero) head
                          let seed' :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons (native_string_lit "@Tuple")
                                (__eo_to_smt_tuple_decl fullD)
                                native_nat_zero) head'
                          cases hWf :
                              __smtx_type_wf (SmtType.Datatype
                                (native_string_lit "@Tuple")
                                (__eo_to_smt_tuple_decl fullD))
                          · dsimp [fullD, __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_streq,
                              native_and, native_ite,
                              hWf]
                          · dsimp [fullD, __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_streq,
                              native_and, native_ite,
                              hWf]
                            exact
                              eo_to_smt_tuple_prepend_rec_type_congr tailD
                                tail tail' seed seed' hTail
                                (by intro s d i j h; simp [seed] at h)
                                (by intro s d i h; simp [seed] at h)
                                (by intro s d i j h; simp [seed'] at h)
                                (by intro s d i h; simp [seed'] at h)
                                (by simp [seed, seed', __smtx_typeof, hHead])
                                (__smtx_dt_num_sels tailD native_nat_zero)
                        · simp [__eo_to_smt_tuple_prepend_of_type, hs2]
                      · simp [__eo_to_smt_tuple_prepend_of_type, hs]
  | _ =>
      simp [__eo_to_smt_tuple_prepend_of_type]

theorem congTypeSpine_tuple_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv UserOp.tuple x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgEoTy₁ : __eo_typeof x₁ = __eo_typeof y₁ :=
    eo_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y₁) y₂)) := by
    change
      __smtx_typeof
          (__eo_to_smt_tuple_prepend
            (__eo_to_smt x₁) (__smtx_typeof (__eo_to_smt x₁))
            (__eo_to_smt x₂)) =
        __smtx_typeof
          (__eo_to_smt_tuple_prepend
            (__eo_to_smt y₁) (__smtx_typeof (__eo_to_smt y₁))
            (__eo_to_smt y₂))
    exact eo_to_smt_tuple_prepend_type_congr
      (__eo_to_smt x₁) (__eo_to_smt y₁)
      (__eo_to_smt x₂) (__eo_to_smt y₂)
      (__smtx_typeof (__eo_to_smt x₁))
      (__smtx_typeof (__eo_to_smt y₁))
      hArgTy₁ hArgTy₁ hArgTy₂
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y₁) y₂)
    hOpTy
    hTrans

private theorem smtx_tuple_prepend_rec_seed_non_none_of_non_none
    (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i j, acc ≠ SmtTerm.DtSel s d i j) ->
      (∀ s d i, acc ≠ SmtTerm.DtTester s d i) ->
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
            tailD tail k acc) ≠
        SmtType.None ->
        __smtx_typeof acc ≠ SmtType.None
  | native_nat_zero, acc, _hAccSel, _hAccTester, hNN => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hNN
  | native_nat_succ k, acc, hAccSel, hAccTester, hNN => by
      let recTerm :=
        __eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
          tailD tail k acc
      let argTerm :=
        SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero k) tail
      have hGen : generic_apply_type recTerm argTerm :=
        generic_apply_type_of_non_datatype_head
          (by
            intro s d i j h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_sel tailD tail k acc
                hAccSel s d i j (by simpa [recTerm] using h))
          (by
            intro s d i h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_tester tailD tail k acc
                hAccTester s d i (by simpa [recTerm] using h))
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof recTerm)
              (__smtx_typeof argTerm) ≠
            SmtType.None := by
        unfold generic_apply_type at hGen
        rw [← hGen]
        simpa [recTerm, argTerm, __eo_to_smt_tuple_prepend_rec] using hNN
      have hRecNN : __smtx_typeof recTerm ≠ SmtType.None :=
        smt_apply_head_non_none_of_apply_non_none hApplyNN
      exact
        smtx_tuple_prepend_rec_seed_non_none_of_non_none tailD tail k acc
          hAccSel hAccTester (by simpa [recTerm] using hRecNN)

theorem tuple_prepend_tail_type_of_non_none
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm) :
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
      SmtType.None ->
    ∃ c,
      __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)) := by
  intro hNN
  unfold __eo_to_smt_tuple_prepend at hNN
  cases hTail : __smtx_typeof tail with
  | Datatype s dd =>
      by_cases hs : s = (native_string_lit "@Tuple")
      · subst s
        cases dd with
        | nil =>
            exact False.elim (hNN (by
              simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
        | cons s2 body rest =>
            cases body with
            | null =>
                exact False.elim (hNN (by
                  simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
            | sum c bodyRest =>
                cases bodyRest with
                | sum c' bodyRest' =>
                    exact False.elim (hNN (by
                      simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
                | null =>
                    cases rest with
                    | cons s3 body3 rest3 =>
                        exact False.elim (hNN (by
                          simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
                    | nil =>
                        by_cases hs2 : s2 = native_string_lit "@Tuple"
                        · subst s2
                          exact ⟨c, by
                            simp [__eo_to_smt_tuple_decl]⟩
                        · exact False.elim (hNN (by
                            simp [hTail, __eo_to_smt_tuple_prepend_of_type,
                              hs2]))
      · exact False.elim (hNN (by
          cases dd with
          | nil =>
              simp [hTail, __eo_to_smt_tuple_prepend_of_type]
          | cons s2 body rest =>
              cases body with
              | null =>
                  simp [hTail, __eo_to_smt_tuple_prepend_of_type]
              | sum c bodyRest =>
                  cases bodyRest <;> cases rest <;>
                    simp [hTail, __eo_to_smt_tuple_prepend_of_type, hs]))
  | _ =>
      exact False.elim (hNN (by
        simp [hTail, __eo_to_smt_tuple_prepend_of_type]))

theorem tuple_prepend_head_non_reg_of_non_none
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm)
    (c : SmtDatatypeCons)
    (hTailTy :
      __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null))) :
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
      SmtType.None ->
    ∃ A,
      __smtx_typeof head = A ∧
        A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD :=
    SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null
  let seed :=
    SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl fullD) native_nat_zero) head
  have hFullWf :
      __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl fullD)) = true := by
    cases hWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl fullD))
    · exfalso
      apply hNN
      unfold __eo_to_smt_tuple_prepend
      rw [hTailTy]
      dsimp [fullD, __eo_to_smt_tuple_decl] at hWf
      simp [__eo_to_smt_tuple_prepend_of_type, __eo_to_smt_tuple_decl,
        native_streq, native_and, native_ite, hWf]
    · rfl
  dsimp [fullD, __eo_to_smt_tuple_decl] at hFullWf
  have hTerm :
      __eo_to_smt_tuple_prepend head headTy tail =
        __eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
          tailD tail
          (__smtx_dt_num_sels tailD native_nat_zero) seed := by
    unfold __eo_to_smt_tuple_prepend
    rw [hTailTy]
    simp [__eo_to_smt_tuple_prepend_of_type, __eo_to_smt_tuple_decl,
      native_streq, native_and, native_ite, hFullWf, tailD, fullD, seed]
  have hRecNN :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
            tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero) seed) ≠
        SmtType.None := by
    rw [← hTerm]
    exact hNN
  have hSeedNN : __smtx_typeof seed ≠ SmtType.None :=
    smtx_tuple_prepend_rec_seed_non_none_of_non_none tailD tail
      (__smtx_dt_num_sels tailD native_nat_zero) seed
      (by intro s d i j h; simp [seed] at h)
      (by intro s d i h; simp [seed] at h)
      hRecNN
  exact
    smtx_apply_arg_non_reg_of_non_none
      (SmtTerm.DtCons (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl fullD) native_nat_zero) head
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by simpa [seed] using hSeedNN)

private theorem eo_to_smt_tuple_prepend_rec_eval_congr
    (M : SmtModel) (tailD : SmtDatatype)
    (tail tail' acc acc' : SmtTerm)
    (hTail : __smtx_model_eval M tail = __smtx_model_eval M tail')
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (hAcc'Sel : ∀ s d i j, acc' ≠ SmtTerm.DtSel s d i j)
    (hAcc'Tester : ∀ s d i, acc' ≠ SmtTerm.DtTester s d i)
    (hAcc : __smtx_model_eval M acc = __smtx_model_eval M acc') :
    ∀ k,
      __smtx_model_eval M
          (__eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
            tailD tail k acc) =
        __smtx_model_eval M
          (__eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
            tailD tail' k acc')
  | native_nat_zero => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc
  | native_nat_succ k => by
      let recTerm :=
        __eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
          tailD tail k acc
      let recTerm' :=
        __eo_to_smt_tuple_prepend_rec (__eo_to_smt_tuple_decl tailD)
          tailD tail' k acc'
      let argTerm :=
        SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero k) tail
      let argTerm' :=
        SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero k) tail'
      have hRecEval :
          __smtx_model_eval M recTerm = __smtx_model_eval M recTerm' := by
        simpa [recTerm, recTerm'] using
          eo_to_smt_tuple_prepend_rec_eval_congr M tailD tail tail' acc acc'
            hTail hAccSel hAccTester hAcc'Sel hAcc'Tester hAcc k
      have hArgEval :
          __smtx_model_eval M argTerm = __smtx_model_eval M argTerm' := by
        simp [argTerm, argTerm', __smtx_model_eval, hTail]
      have hGen : generic_apply_eval recTerm argTerm :=
        generic_apply_eval_of_non_datatype_head
          (by
            intro s d i j h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_sel tailD tail k acc
                hAccSel s d i j (by simpa [recTerm] using h))
          (by
            intro s d i h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_tester tailD tail k acc
                hAccTester s d i (by simpa [recTerm] using h))
      have hGen' : generic_apply_eval recTerm' argTerm' :=
        generic_apply_eval_of_non_datatype_head
          (by
            intro s d i j h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_sel tailD tail' k acc'
                hAcc'Sel s d i j (by simpa [recTerm'] using h))
          (by
            intro s d i h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_tester tailD tail' k acc'
                hAcc'Tester s d i (by simpa [recTerm'] using h))
      unfold generic_apply_eval at hGen hGen'
      change
        __smtx_model_eval M (SmtTerm.Apply recTerm argTerm) =
          __smtx_model_eval M (SmtTerm.Apply recTerm' argTerm')
      rw [hGen M, hGen' M, hRecEval, hArgEval]

theorem eo_to_smt_tuple_prepend_eval_congr
    (M : SmtModel) (head head' tail tail' : SmtTerm)
    (headTy headTy' : SmtType) :
    headTy = headTy' ->
    __smtx_typeof tail = __smtx_typeof tail' ->
    __smtx_model_eval M head = __smtx_model_eval M head' ->
    __smtx_model_eval M tail = __smtx_model_eval M tail' ->
      __smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail) =
        __smtx_model_eval M
          (__eo_to_smt_tuple_prepend head' headTy' tail') := by
  intro hHeadTy hTailTy hHead hTail
  subst headTy'
  unfold __eo_to_smt_tuple_prepend
  rw [← hTailTy]
  cases hTailTy0 : __smtx_typeof tail with
  | Datatype s dd =>
      cases dd with
      | nil =>
          simp [__eo_to_smt_tuple_prepend_of_type]
      | cons s2 body rest =>
          cases rest with
          | cons s3 body3 rest3 =>
              simp [__eo_to_smt_tuple_prepend_of_type]
          | nil =>
              cases body with
              | null =>
                  simp [__eo_to_smt_tuple_prepend_of_type]
              | sum c bodyRest =>
                  cases bodyRest with
                  | sum c' bodyRest' =>
                      simp [__eo_to_smt_tuple_prepend_of_type]
                  | null =>
                      by_cases hs : s = native_string_lit "@Tuple"
                      · subst s
                        by_cases hs2 : s2 = native_string_lit "@Tuple"
                        · subst s2
                          let tailD := SmtDatatype.sum c SmtDatatype.null
                          let fullD :=
                            SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                              SmtDatatype.null
                          let seed :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons (native_string_lit "@Tuple")
                                (__eo_to_smt_tuple_decl fullD)
                                native_nat_zero) head
                          let seed' :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons (native_string_lit "@Tuple")
                                (__eo_to_smt_tuple_decl fullD)
                                native_nat_zero) head'
                          cases hWf :
                              __smtx_type_wf (SmtType.Datatype
                                (native_string_lit "@Tuple")
                                (__eo_to_smt_tuple_decl fullD))
                          · dsimp [fullD, __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_streq,
                              native_and, native_ite,
                              hWf]
                          · dsimp [fullD, __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_streq,
                              native_and, native_ite,
                              hWf]
                            exact
                              eo_to_smt_tuple_prepend_rec_eval_congr M tailD
                                tail tail' seed seed' hTail
                                (by intro s d i j h; simp [seed] at h)
                                (by intro s d i h; simp [seed] at h)
                                (by intro s d i j h; simp [seed'] at h)
                                (by intro s d i h; simp [seed'] at h)
                                (by
                                  simp [seed, seed', __smtx_model_eval,
                                    hHead])
                                (__smtx_dt_num_sels tailD native_nat_zero)
                        · simp [__eo_to_smt_tuple_prepend_of_type, hs2]
                      · simp [__eo_to_smt_tuple_prepend_of_type, hs]
  | _ =>
      simp [__eo_to_smt_tuple_prepend_of_type]

theorem congTrueSpine_tuple_eq_true
    (M : SmtModel) (hM : model_wf M)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M UserOp.tuple x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y₁) y₂)
        hEqBool
    have hxOpNN :
        __smtx_typeof
            (__eo_to_smt_tuple_prepend
              (__eo_to_smt x₁) (__smtx_typeof (__eo_to_smt x₁))
              (__eo_to_smt x₂)) ≠
          SmtType.None := by
      change
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x₁) x₂)) ≠
          SmtType.None
      exact hTypes.2
    rcases tuple_prepend_tail_type_of_non_none
        (__eo_to_smt x₁) (__smtx_typeof (__eo_to_smt x₁))
        (__eo_to_smt x₂) hxOpNN with
      ⟨c, hx₂Tail⟩
    rcases tuple_prepend_head_non_reg_of_non_none
        (__eo_to_smt x₁) (__smtx_typeof (__eo_to_smt x₁))
        (__eo_to_smt x₂) c hx₂Tail hxOpNN with
      ⟨A, hx₁A, hANN, hAReg⟩
    let B := SmtType.Datatype (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl
        (SmtDatatype.sum c SmtDatatype.null))
    have hx₂B : __smtx_typeof (__eo_to_smt x₂) = B := by
      simpa [B] using hx₂Tail
    have hBNN : B ≠ SmtType.None := by
      simp [B]
    have hBReg : B ≠ SmtType.RegLan := by
      simp [B]
    have hy₁A : __smtx_typeof (__eo_to_smt y₁) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁A
    have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂B
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        A hx₁A hy₁A hANN hAReg hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        B hx₂B hy₂B hBNN hBReg hArg₂
    have hArgEoTy₁ : __eo_typeof x₁ = __eo_typeof y₁ :=
      eo_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt_tuple_prepend
            (__eo_to_smt x₁) (__smtx_typeof (__eo_to_smt x₁))
            (__eo_to_smt x₂)))
        (__smtx_model_eval M
          (__eo_to_smt_tuple_prepend
            (__eo_to_smt y₁) (__smtx_typeof (__eo_to_smt y₁))
            (__eo_to_smt y₂))) =
        SmtValue.Boolean true
    rw [eo_to_smt_tuple_prepend_eval_congr M
      (__eo_to_smt x₁) (__eo_to_smt y₁)
      (__eo_to_smt x₂) (__eo_to_smt y₂)
      (__smtx_typeof (__eo_to_smt x₁))
      (__smtx_typeof (__eo_to_smt y₁))
      (smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁)
      (smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂)
      hEval₁ hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)


end CongSupport
