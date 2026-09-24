module

public import Cpc.Proofs.RuleSupport.Cong.ApplySpineB
import all Cpc.Proofs.RuleSupport.Cong.ApplySpineB

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

theorem bv_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b))
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
  rcases bv_binop_args_of_non_none (op := op) (hTy a b) hTerm with
    ⟨w, hA, hB⟩
  exact ⟨SmtType.BitVec w, SmtType.BitVec w, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem bv_binop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2_ret
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
  rcases bv_binop_ret_args_of_non_none (op := op) (ret := R)
      (hTy a b) hTerm with
    ⟨w, hA, hB⟩
  exact ⟨SmtType.BitVec w, SmtType.BitVec w, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem bv_concat_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.concat a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.concat a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases bv_concat_args_of_non_none hTerm with
    ⟨wA, wB, hA, hB⟩
  exact ⟨SmtType.BitVec wA, SmtType.BitVec wB, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem seq_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_seq_op_1 (__smtx_typeof a))
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases seq_arg_of_non_none (op := op) (hTy a) hTerm with
    ⟨T, hA⟩
  exact ⟨SmtType.Seq T, hA, by simp, by simp⟩

theorem seq_unop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_seq_op_1_ret (__smtx_typeof a) R)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases seq_arg_of_non_none_ret (op := op) (R := R) (hTy a)
      hTerm with
    ⟨T, hA⟩
  exact ⟨SmtType.Seq T, hA, by simp, by simp⟩

theorem seq_char_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          native_ite (native_Teq (__smtx_typeof a)
            (SmtType.Seq SmtType.Char)) R SmtType.None)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  have hA :
      __smtx_typeof a = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := op) (ret := R) (hTy a) hTerm
  exact ⟨SmtType.Seq SmtType.Char, hA, by simp, by simp⟩

theorem seq_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2 (__smtx_typeof a) (__smtx_typeof b))
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
  rcases seq_binop_args_of_non_none (op := op) (hTy a b)
      hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Seq T, SmtType.Seq T, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem seq_binop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2_ret
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
  rcases seq_binop_args_of_non_none_ret (op := op) (R := R)
      (hTy a b) hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Seq T, SmtType.Seq T, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem seq_char_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
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
  rcases seq_char_binop_args_of_non_none (op := op) (ret := R)
      (hTy a b) hTerm with
    ⟨hA, hB⟩
  exact ⟨SmtType.Seq SmtType.Char, SmtType.Seq SmtType.Char, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem seq_triop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b c,
        __smtx_typeof (op a b c) =
          __smtx_typeof_seq_op_3
            (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c))
    (a b c : SmtTerm) :
    __smtx_typeof (op a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases seq_triop_args_of_non_none (op := op) (hTy a b c)
      hTerm with
    ⟨T, hA, hB, hC⟩
  exact ⟨SmtType.Seq T, SmtType.Seq T, SmtType.Seq T,
    hA, hB, hC, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem seq_nth_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_nth a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.seq_nth a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases seq_nth_args_of_non_none hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Seq T, SmtType.Int, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem seq_unit_arg_non_reg_of_non_none
    (a : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_unit a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hGuardNN :
      __smtx_typeof_guard_wf
          (SmtType.Seq (__smtx_typeof a))
          (SmtType.Seq (__smtx_typeof a)) ≠ SmtType.None := by
    simpa [smtx_typeof_seq_unit_term_eq] using hNN
  have hSeqWf :
      __smtx_type_wf (SmtType.Seq (__smtx_typeof a)) = true :=
    smtx_typeof_guard_wf_wf_of_non_none
      (SmtType.Seq (__smtx_typeof a))
      (SmtType.Seq (__smtx_typeof a)) hGuardNN
  have hSeqComponent :
      __smtx_type_wf_component (SmtType.Seq (__smtx_typeof a)) = true := by
    simpa [__smtx_type_wf] using hSeqWf
  have hSeqWfRec :
      __smtx_type_wf_rec (SmtType.Seq (__smtx_typeof a)) = true :=
    (smtx_type_wf_component_parts hSeqComponent).2
  have hArgWfRec :
      __smtx_type_wf_rec (__smtx_typeof a) = true :=
    TranslationProofs.seq_type_wf_rec_component_of_wf hSeqWfRec
  exact ⟨__smtx_typeof a, rfl,
    by
      intro hNone
      rw [hNone] at hArgWfRec
      simp [__smtx_type_wf_rec] at hArgWfRec,
    type_wf_rec_ne_reglan hArgWfRec⟩

theorem set_singleton_arg_non_reg_of_non_none
    (a : SmtTerm) :
    __smtx_typeof (SmtTerm.set_singleton a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hGuardNN :
      __smtx_typeof_guard_wf
          (SmtType.Set (__smtx_typeof a))
          (SmtType.Set (__smtx_typeof a)) ≠ SmtType.None := by
    simpa [smtx_typeof_set_singleton_term_eq] using hNN
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__smtx_typeof a)) = true :=
    smtx_typeof_guard_wf_wf_of_non_none
      (SmtType.Set (__smtx_typeof a))
      (SmtType.Set (__smtx_typeof a)) hGuardNN
  have hSetComponent :
      __smtx_type_wf_component (SmtType.Set (__smtx_typeof a)) = true := by
    simpa [__smtx_type_wf] using hSetWf
  have hSetWfRec :
      __smtx_type_wf_rec (SmtType.Set (__smtx_typeof a)) = true :=
    (smtx_type_wf_component_parts hSetComponent).2
  have hArgWfRec :
      __smtx_type_wf_rec (__smtx_typeof a) = true :=
    TranslationProofs.set_type_wf_rec_component_of_wf hSetWfRec
  exact ⟨__smtx_typeof a, rfl,
    by
      intro hNone
      rw [hNone] at hArgWfRec
      simp [__smtx_type_wf_rec] at hArgWfRec,
    type_wf_rec_ne_reglan hArgWfRec⟩

theorem select_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.select a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.select a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases select_args_of_non_none hTerm with ⟨K, V, ha, hb⟩
  have hKWf :
      __smtx_type_wf_rec K = true :=
    (smt_map_components_wf_rec_of_non_none_type a K V ha).1
  exact ⟨SmtType.Map K V, K, ha, hb,
    by simp,
    by
      intro hNone
      rw [hNone] at hKWf
      simp [__smtx_type_wf_rec] at hKWf,
    by simp,
    type_wf_rec_ne_reglan hKWf⟩

theorem set_member_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.set_member a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.set_member a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases set_member_args_of_non_none hTerm with ⟨K, ha, hb⟩
  have hKWf :
      __smtx_type_wf_rec K = true :=
    smt_set_component_wf_rec_of_non_none_type b K hb
  exact ⟨K, SmtType.Set K, ha, hb,
    by
      intro hNone
      rw [hNone] at hKWf
      simp [__smtx_type_wf_rec] at hKWf,
    by simp,
    type_wf_rec_ne_reglan hKWf,
    by simp⟩

theorem store_args_non_reg_of_non_none
    (a b c : SmtTerm) :
    __smtx_typeof (SmtTerm.store a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.store a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases store_args_of_non_none hTerm with ⟨K, V, ha, hb, hc⟩
  have hComps :=
    smt_map_components_wf_rec_of_non_none_type a K V ha
  exact ⟨SmtType.Map K V, K, V, ha, hb, hc,
    by simp,
    by
      intro hNone
      rw [hNone] at hComps
      simp [__smtx_type_wf_rec] at hComps,
    by
      intro hNone
      rw [hNone] at hComps
      simp [__smtx_type_wf_rec] at hComps,
    by simp,
    type_wf_rec_ne_reglan hComps.1,
    type_wf_rec_ne_reglan hComps.2⟩

theorem str_substr_args_non_reg_of_non_none
    (a b c : SmtTerm) :
    __smtx_typeof (SmtTerm.str_substr a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.str_substr a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases str_substr_args_of_non_none hTerm with
    ⟨T, hA, hB, hC⟩
  exact ⟨SmtType.Seq T, SmtType.Int, SmtType.Int, hA, hB, hC,
    by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem str_indexof_args_non_reg_of_non_none
    (a b c : SmtTerm) :
    __smtx_typeof (SmtTerm.str_indexof a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.str_indexof a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases str_indexof_args_of_non_none hTerm with
    ⟨T, hA, hB, hC⟩
  exact ⟨SmtType.Seq T, SmtType.Seq T, SmtType.Int, hA, hB, hC,
    by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem str_at_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.str_at a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.str_at a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases str_at_args_of_non_none hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Seq T, SmtType.Int, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem str_update_args_non_reg_of_non_none
    (a b c : SmtTerm) :
    __smtx_typeof (SmtTerm.str_update a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.str_update a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases str_update_args_of_non_none hTerm with
    ⟨T, hA, hB, hC⟩
  exact ⟨SmtType.Seq T, SmtType.Int, SmtType.Seq T, hA, hB, hC,
    by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem congTrueSpine_plus_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.plus SmtTerm.plus
    __smtx_model_eval_plus
    (by intro a b; rfl)
    (arith_overload_binop_args_non_reg_of_non_none SmtTerm.plus
      (by intro a b; exact typeof_plus_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_14])
    x₁ x₂ rhs

theorem congTypeSpine_plus_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.plus SmtTerm.plus
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_plus_eq, typeof_plus_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_neg_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.neg SmtTerm.neg
    __smtx_model_eval__
    (by intro a b; rfl)
    (arith_overload_binop_args_non_reg_of_non_none SmtTerm.neg
      (by intro a b; exact typeof_neg_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_15])
    x₁ x₂ rhs

theorem congTypeSpine_neg_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.neg SmtTerm.neg
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_neg_eq, typeof_neg_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_mult_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.mult SmtTerm.mult
    __smtx_model_eval_mult
    (by intro a b; rfl)
    (arith_overload_binop_args_non_reg_of_non_none SmtTerm.mult
      (by intro a b; exact typeof_mult_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_16])
    x₁ x₂ rhs

theorem congTypeSpine_mult_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.mult SmtTerm.mult
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_mult_eq, typeof_mult_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_lt_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.lt SmtTerm.lt
    __smtx_model_eval_lt
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.lt SmtType.Bool
      (by intro a b; exact typeof_lt_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_17])
    x₁ x₂ rhs

theorem congTypeSpine_lt_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.lt SmtTerm.lt
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_lt_eq, typeof_lt_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_leq_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.leq SmtTerm.leq
    __smtx_model_eval_leq
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.leq SmtType.Bool
      (by intro a b; exact typeof_leq_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_18])
    x₁ x₂ rhs

theorem congTypeSpine_leq_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.leq SmtTerm.leq
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_leq_eq, typeof_leq_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_gt_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.gt SmtTerm.gt
    __smtx_model_eval_gt
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.gt SmtType.Bool
      (by intro a b; exact typeof_gt_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_19])
    x₁ x₂ rhs

theorem congTypeSpine_gt_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.gt SmtTerm.gt
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_gt_eq, typeof_gt_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_geq_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.geq SmtTerm.geq
    __smtx_model_eval_geq
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.geq SmtType.Bool
      (by intro a b; exact typeof_geq_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_20])
    x₁ x₂ rhs

theorem congTypeSpine_geq_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.geq SmtTerm.geq
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_geq_eq, typeof_geq_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_to_real_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.to_real) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.to_real) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.to_real) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.to_real SmtTerm.to_real
    __smtx_model_eval_to_real
    (by intro a; rfl)
    to_real_args_non_reg_of_non_none
    (by intro a; rw [__smtx_model_eval.eq_21])
    x rhs

theorem congTypeSpine_to_real_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.to_real) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.to_real) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.to_real) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.to_real SmtTerm.to_real
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_to_real_eq, typeof_to_real_eq, h])
    x rhs

theorem congTrueSpine_to_int_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.to_int) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.to_int) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.to_int) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.to_int SmtTerm.to_int
    __smtx_model_eval_to_int
    (by intro a; rfl)
    (real_ret_unop_args_non_reg_of_non_none SmtTerm.to_int SmtType.Int
      (by intro a; exact typeof_to_int_eq a))
    (by intro a; rw [__smtx_model_eval.eq_22])
    x rhs

theorem congTypeSpine_to_int_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.to_int) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.to_int) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.to_int) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.to_int SmtTerm.to_int
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_to_int_eq, typeof_to_int_eq, h])
    x rhs

theorem congTrueSpine_is_int_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.is_int) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.is_int) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.is_int) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.is_int SmtTerm.is_int
    __smtx_model_eval_is_int
    (by intro a; rfl)
    (real_ret_unop_args_non_reg_of_non_none SmtTerm.is_int SmtType.Bool
      (by intro a; exact typeof_is_int_eq a))
    (by intro a; rw [__smtx_model_eval.eq_23])
    x rhs

theorem congTypeSpine_is_int_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.is_int) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.is_int) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.is_int) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.is_int SmtTerm.is_int
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_is_int_eq, typeof_is_int_eq, h])
    x rhs

theorem congTrueSpine_abs_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.abs) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.abs) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.abs) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.abs SmtTerm.abs
    __smtx_model_eval_abs
    (by intro a; rfl)
    (arith_unop_args_non_reg_of_non_none SmtTerm.abs
      (by intro a; exact typeof_abs_eq a))
    (by intro a; rw [__smtx_model_eval.eq_24])
    x rhs

theorem congTypeSpine_abs_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.abs) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.abs) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.abs) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.abs SmtTerm.abs
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_abs_eq, typeof_abs_eq, h])
    x rhs

theorem congTrueSpine_uneg_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.__eoo_neg_2 SmtTerm.uneg
    __smtx_model_eval_uneg
    (by intro a; rfl)
    (arith_unop_args_non_reg_of_non_none SmtTerm.uneg
      (by intro a; exact typeof_uneg_eq a))
    (by intro a; rw [__smtx_model_eval.eq_25])
    x rhs

theorem congTypeSpine_uneg_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.__eoo_neg_2 SmtTerm.uneg
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_uneg_eq, typeof_uneg_eq, h])
    x rhs

theorem congTrueSpine_div_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.div SmtTerm.div
    (smtEvalDiv M)
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.div SmtType.Int
      (by intro a b; exact typeof_div_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_26])
    x₁ x₂ rhs

theorem congTypeSpine_div_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.div SmtTerm.div
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_div_eq, typeof_div_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_mod_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.mod SmtTerm.mod
    (smtEvalMod M)
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.mod SmtType.Int
      (by intro a b; exact typeof_mod_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_27])
    x₁ x₂ rhs

theorem congTypeSpine_mod_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.mod SmtTerm.mod
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_mod_eq, typeof_mod_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_div_total_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.div_total SmtTerm.div_total
    __smtx_model_eval_div_total
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.div_total SmtType.Int
      (by intro a b; exact typeof_div_total_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_31])
    x₁ x₂ rhs

theorem congTypeSpine_div_total_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.div_total SmtTerm.div_total
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_div_total_eq, typeof_div_total_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_mod_total_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.mod_total SmtTerm.mod_total
    __smtx_model_eval_mod_total
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.mod_total SmtType.Int
      (by intro a b; exact typeof_mod_total_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_32])
    x₁ x₂ rhs

theorem congTypeSpine_mod_total_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.mod_total SmtTerm.mod_total
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_mod_total_eq, typeof_mod_total_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_divisible_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.divisible SmtTerm.divisible
    __smtx_model_eval_divisible
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.divisible SmtType.Bool
      (by intro a b; exact typeof_divisible_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_28])
    x₁ x₂ rhs

theorem congTypeSpine_divisible_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.divisible SmtTerm.divisible
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_divisible_eq, typeof_divisible_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_int_pow2_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.int_pow2 SmtTerm.int_pow2
    __smtx_model_eval_int_pow2
    (by intro a; rfl)
    (int_ret_unop_args_non_reg_of_non_none SmtTerm.int_pow2 SmtType.Int
      (by intro a; exact typeof_int_pow2_eq a))
    (by intro a; rw [__smtx_model_eval.eq_29])
    x rhs

theorem congTypeSpine_int_pow2_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.int_pow2) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.int_pow2 SmtTerm.int_pow2
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_int_pow2_eq, typeof_int_pow2_eq, h])
    x rhs

theorem congTrueSpine_int_log2_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_log2) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.int_log2) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.int_log2) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.int_log2 SmtTerm.int_log2
    __smtx_model_eval_int_log2
    (by intro a; rfl)
    (int_ret_unop_args_non_reg_of_non_none SmtTerm.int_log2 SmtType.Int
      (by intro a; exact typeof_int_log2_eq a))
    (by intro a; rw [__smtx_model_eval.eq_30])
    x rhs

theorem congTypeSpine_int_log2_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.int_log2) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.int_log2) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_log2) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.int_log2 SmtTerm.int_log2
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_int_log2_eq, typeof_int_log2_eq, h])
    x rhs

private def intIspow2Term (a : SmtTerm) : SmtTerm :=
  SmtTerm.and (SmtTerm.geq a (SmtTerm.Numeral 0))
    (SmtTerm.eq a (SmtTerm.int_pow2 (SmtTerm.int_log2 a)))

private noncomputable def intIspow2Eval (a : SmtValue) : SmtValue :=
  __smtx_model_eval_and
    (__smtx_model_eval_geq a (SmtValue.Numeral 0))
    (__smtx_model_eval_eq a
      (__smtx_model_eval_int_pow2 (__smtx_model_eval_int_log2 a)))

private theorem int_ispow2_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (intIspow2Term a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hAnd := smt_typeof_and_args_bool_of_non_none
    (SmtTerm.geq a (SmtTerm.Numeral 0))
    (SmtTerm.eq a (SmtTerm.int_pow2 (SmtTerm.int_log2 a)))
    (by simpa [intIspow2Term] using hNN)
  have hGeqNN : __smtx_typeof (SmtTerm.geq a (SmtTerm.Numeral 0)) ≠
      SmtType.None := by
    rw [hAnd.1]
    simp
  rcases arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.geq
      SmtType.Bool (by intro x y; exact typeof_geq_eq x y)
      a (SmtTerm.Numeral 0) hGeqNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

theorem congTrueSpine_int_ispow2_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.int_ispow2 intIspow2Term
    intIspow2Eval
    (by intro a; rfl)
    int_ispow2_arg_non_reg_of_non_none
    (by
      intro a
      rw [intIspow2Term, intIspow2Eval, __smtx_model_eval.eq_9,
        __smtx_model_eval.eq_20, smtx_model_eval_eq_term_eq,
        __smtx_model_eval.eq_29, __smtx_model_eval.eq_30,
        __smtx_model_eval.eq_2])
    x rhs

theorem congTypeSpine_int_ispow2_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.int_ispow2) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.int_ispow2
    intIspow2Term
    (by intro a; rfl)
    (by
      intro a b h
      rw [intIspow2Term, intIspow2Term, typeof_and_eq, typeof_and_eq,
        typeof_geq_eq, typeof_geq_eq, typeof_eq_eq, typeof_eq_eq,
        typeof_int_pow2_eq, typeof_int_pow2_eq, typeof_int_log2_eq,
        typeof_int_log2_eq, h])
    x rhs

theorem congTrueSpine_int_div_by_zero_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp._at_int_div_by_zero
    (fun a => SmtTerm.div a (SmtTerm.Numeral 0))
    (fun v => smtEvalDiv M v (SmtValue.Numeral 0))
    (by intro a; rfl)
    div_by_zero_arg_non_reg_of_non_none
    (by intro a; rw [__smtx_model_eval.eq_26, __smtx_model_eval.eq_2])
    x rhs

theorem congTypeSpine_int_div_by_zero_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp._at_int_div_by_zero
    (fun a => SmtTerm.div a (SmtTerm.Numeral 0))
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_div_eq, typeof_div_eq, h])
    x rhs

theorem congTrueSpine_mod_by_zero_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp._at_mod_by_zero
    (fun a => SmtTerm.mod a (SmtTerm.Numeral 0))
    (fun v => smtEvalMod M v (SmtValue.Numeral 0))
    (by intro a; rfl)
    mod_by_zero_arg_non_reg_of_non_none
    (by intro a; rw [__smtx_model_eval.eq_27, __smtx_model_eval.eq_2])
    x rhs

theorem congTypeSpine_mod_by_zero_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp._at_mod_by_zero
    (fun a => SmtTerm.mod a (SmtTerm.Numeral 0))
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_mod_eq, typeof_mod_eq, h])
    x rhs

theorem congTrueSpine_qdiv_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.qdiv SmtTerm.qdiv
    (smtEvalQdiv M)
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.qdiv
      SmtType.Real (by intro a b; exact typeof_qdiv_eq a b))
    (by intro a b; rw [smtx_model_eval_qdiv_term_eq])
    x₁ x₂ rhs

theorem congTypeSpine_qdiv_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.qdiv SmtTerm.qdiv
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_qdiv_eq, typeof_qdiv_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_qdiv_total_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.qdiv_total
    SmtTerm.qdiv_total
    __smtx_model_eval_qdiv_total
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.qdiv_total
      SmtType.Real (by intro a b; exact typeof_qdiv_total_eq a b))
    (by intro a b; rw [smtx_model_eval_qdiv_total_term_eq])
    x₁ x₂ rhs

theorem congTypeSpine_qdiv_total_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.qdiv_total
    SmtTerm.qdiv_total
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_qdiv_total_eq, typeof_qdiv_total_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_qdiv_by_zero_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp._at_div_by_zero
    (fun a => SmtTerm.qdiv a (SmtTerm.Rational (native_mk_rational 0 1)))
    (fun v => smtEvalQdiv M v
      (SmtValue.Rational (native_mk_rational 0 1)))
    (by intro a; rfl)
    qdiv_by_zero_arg_non_reg_of_non_none
    (by
      intro a
      rw [smtx_model_eval_qdiv_term_eq]
      rw [__smtx_model_eval.eq_def] <;> simp only)
    x rhs

theorem congTypeSpine_qdiv_by_zero_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp._at_div_by_zero
    (fun a => SmtTerm.qdiv a (SmtTerm.Rational (native_mk_rational 0 1)))
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_qdiv_eq, typeof_qdiv_eq, h])
    x rhs

theorem congTrueSpine_bv_unop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_bv_op_1 (__smtx_typeof a))
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (bv_unop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x rhs

theorem congTypeSpine_bv_unop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_bv_op_1 (__smtx_typeof a))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

theorem congTrueSpine_bv_unop_ret_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_bv_op_1_ret (__smtx_typeof a) R)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (bv_unop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x rhs

theorem congTypeSpine_bv_unop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_bv_op_1_ret (__smtx_typeof a) R)
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

theorem congTrueSpine_bv_binop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (bv_binop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x₁ x₂ rhs

theorem congTypeSpine_bv_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_bv_binop_ret_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (bv_binop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x₁ x₂ rhs

theorem congTypeSpine_bv_binop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

def bvPredToBv (pred : SmtTerm -> SmtTerm -> SmtTerm)
    (a b : SmtTerm) : SmtTerm :=
  SmtTerm.ite (pred a b) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)

def bvPredToBvEval (predEval : SmtValue -> SmtValue -> SmtValue)
    (a b : SmtValue) : SmtValue :=
  __smtx_model_eval_ite (predEval a b)
    (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)

def bvBitTerm (i a : SmtTerm) : SmtTerm :=
  SmtTerm.eq (SmtTerm.extract i i a) (SmtTerm.Binary 1 1)

theorem bv_pred_to_bv_args_non_reg_of_non_none
    (pred : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (pred a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) SmtType.Bool)
    (a b : SmtTerm) :
    __smtx_typeof (bvPredToBv pred a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (bvPredToBv pred a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases ite_args_of_non_none hTerm with ⟨_T, hCond, _hThen, _hElse, _hT⟩
  have hPredNN : __smtx_typeof (pred a b) ≠ SmtType.None := by
    rw [hCond]
    simp
  exact bv_binop_ret_args_non_reg_of_non_none pred SmtType.Bool hTy
    a b hPredNN

theorem bv_bit_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (bvBitTerm i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (SmtTerm.extract i i a))
          (__smtx_typeof (SmtTerm.Binary 1 1)) ≠
        SmtType.None := by
    simpa [bvBitTerm, typeof_eq_eq] using hNN
  have hExtractNN : __smtx_typeof (SmtTerm.extract i i a) ≠ SmtType.None :=
    (cong_smtx_typeof_eq_non_none hEqNN).2
  exact extract_arg_non_reg_of_non_none i i a hExtractNN

theorem congTrueSpine_bv_pred_to_bv_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (pred : SmtTerm -> SmtTerm -> SmtTerm)
    (predEval : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          bvPredToBv pred (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (pred a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) SmtType.Bool)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (bvPredToBv pred a b) =
          bvPredToBvEval predEval
            (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp (bvPredToBv pred)
    (bvPredToBvEval predEval) hToSmt
    (bv_pred_to_bv_args_non_reg_of_non_none pred hTy) hEval
    x₁ x₂ rhs

theorem congTypeSpine_bv_pred_to_bv_eq_has_bool_type
    (eoOp : UserOp) (pred : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          bvPredToBv pred (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (pred a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) SmtType.Bool)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp (bvPredToBv pred)
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [bvPredToBv, bvPredToBv, typeof_ite_eq, typeof_ite_eq,
        hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private noncomputable def bvZeroTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.Binary (__eo_to_smt_bv_size (__smtx_typeof a)) 0

private noncomputable def bvAllOnesTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.bvnot (bvZeroTerm a)

private noncomputable def bvRedandTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.bvcomp a (bvAllOnesTerm a)

private noncomputable def bvRedorTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.bvnot (SmtTerm.bvcomp a (bvZeroTerm a))

private theorem bvredand_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (bvRedandTerm a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  rcases bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvcomp
      (SmtType.BitVec 1)
      (by intro x y; rw [__smtx_typeof.eq_46])
      a (bvAllOnesTerm a) (by simpa [bvRedandTerm] using hNN) with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

private theorem bvredor_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (bvRedorTerm a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hInnerNN :
      __smtx_typeof (SmtTerm.bvcomp a (bvZeroTerm a)) ≠ SmtType.None := by
    rcases bv_unop_args_non_reg_of_non_none SmtTerm.bvnot
        (by intro x; rw [__smtx_typeof.eq_39])
        (SmtTerm.bvcomp a (bvZeroTerm a))
        (by simpa [bvRedorTerm] using hNN) with
      ⟨A, hA, hANN, _hAReg⟩
    rw [hA]
    exact hANN
  rcases bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvcomp
      (SmtType.BitVec 1)
      (by intro x y; rw [__smtx_typeof.eq_46])
      a (bvZeroTerm a) hInnerNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

theorem congTrueSpine_bvredand_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.bvredand) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.bvredand) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.bvredand) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true_of_eval_congr M hM UserOp.bvredand
    bvRedandTerm
    (by intro a; rfl)
    bvredand_arg_non_reg_of_non_none
    (by
      intro a b hTy hEval
      rw [bvRedandTerm, bvAllOnesTerm, bvZeroTerm, bvRedandTerm,
        bvAllOnesTerm, bvZeroTerm, __smtx_model_eval.eq_46,
        __smtx_model_eval.eq_46, __smtx_model_eval.eq_39,
        __smtx_model_eval.eq_39, __smtx_model_eval.eq_5,
        __smtx_model_eval.eq_5, hTy, hEval])
    x rhs

theorem congTypeSpine_bvredand_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.bvredand) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.bvredand) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.bvredand) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.bvredand
    bvRedandTerm
    (by intro a; rfl)
    (by
      intro a b h
      rw [bvRedandTerm, bvAllOnesTerm, bvZeroTerm, bvRedandTerm,
        bvAllOnesTerm, bvZeroTerm, __smtx_typeof.eq_46,
        __smtx_typeof.eq_46, __smtx_typeof.eq_39, __smtx_typeof.eq_39,
        __smtx_typeof.eq_5, __smtx_typeof.eq_5, h])
    x rhs

theorem congTrueSpine_bvredor_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.bvredor) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.bvredor) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.bvredor) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true_of_eval_congr M hM UserOp.bvredor
    bvRedorTerm
    (by intro a; rfl)
    bvredor_arg_non_reg_of_non_none
    (by
      intro a b hTy hEval
      rw [bvRedorTerm, bvZeroTerm, bvRedorTerm, bvZeroTerm,
        __smtx_model_eval.eq_39, __smtx_model_eval.eq_39,
        __smtx_model_eval.eq_46, __smtx_model_eval.eq_46,
        __smtx_model_eval.eq_5, __smtx_model_eval.eq_5, hTy, hEval])
    x rhs

theorem congTypeSpine_bvredor_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.bvredor) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.bvredor) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.bvredor) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.bvredor
    bvRedorTerm
    (by intro a; rfl)
    (by
      intro a b h
      rw [bvRedorTerm, bvZeroTerm, bvRedorTerm, bvZeroTerm,
        __smtx_typeof.eq_39, __smtx_typeof.eq_39, __smtx_typeof.eq_46,
        __smtx_typeof.eq_46, __smtx_typeof.eq_5, __smtx_typeof.eq_5, h])
    x rhs

private theorem typeof_binary_one_eq :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hWidth : native_zleq 0 1 = true := by native_decide
  have hMod : native_zeq 1 (native_mod_total 1 (native_int_pow2 1)) = true := by
    native_decide
  have hNat : native_int_to_nat 1 = 1 := by native_decide
  unfold __smtx_typeof
  simp [native_ite, SmtEval.native_and, hWidth, hMod, hNat]

private def bvIteTerm (c t e : SmtTerm) : SmtTerm :=
  SmtTerm.ite (SmtTerm.eq c (SmtTerm.Binary 1 1)) t e

theorem congTrueSpine_bvite_eq_true
    (M : SmtModel) (hM : model_wf M)
    (c t e rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
      rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.bvite c t e rhs hSpine with
    ⟨c', t', e', hRhs, hCond, hThen, hElse⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let C : SmtTerm := __eo_to_smt c
    let T : SmtTerm := __eo_to_smt t
    let E : SmtTerm := __eo_to_smt e
    let C' : SmtTerm := __eo_to_smt c'
    let T' : SmtTerm := __eo_to_smt t'
    let E' : SmtTerm := __eo_to_smt e'
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c') t') e')
        hEqBool
    have hLeftNN :
        __smtx_typeof (bvIteTerm C T E) ≠ SmtType.None := by
      exact hTypes.2
    have hIteNN : term_has_non_none_type (bvIteTerm C T E) := by
      unfold term_has_non_none_type
      exact hLeftNN
    rcases ite_args_of_non_none hIteNN with
      ⟨_R, hCondTy, _hThenTy, _hElseTy, _hRNN⟩
    have hCondNN :
        __smtx_typeof (SmtTerm.eq C (SmtTerm.Binary 1 1)) ≠
          SmtType.None := by
      rw [hCondTy]
      simp
    have hCondEqNN :
        __smtx_typeof_eq
            (__smtx_typeof C) (__smtx_typeof (SmtTerm.Binary 1 1)) ≠
          SmtType.None := by
      simpa [typeof_eq_eq] using hCondNN
    have hEqArgs := cong_smtx_typeof_eq_non_none hCondEqNN
    have hCReg : __smtx_typeof C ≠ SmtType.RegLan := by
      rw [hEqArgs.1, typeof_binary_one_eq]
      simp
    have hCondTyEq : __smtx_typeof C = __smtx_typeof C' :=
      smt_type_eq_of_eq_true_or_same M c c' hCond
    have hCondEval :
        __smtx_model_eval M C = __smtx_model_eval M C' :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM c c'
        (__smtx_typeof C) rfl (by rw [← hCondTyEq])
        hEqArgs.2 hCReg hCond
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (bvIteTerm C T E))
        (__smtx_model_eval M (bvIteTerm C' T' E'))
    rw [bvIteTerm, bvIteTerm, smtx_model_eval_ite_term_eq,
      smtx_model_eval_ite_term_eq, smtx_model_eval_eq_term_eq,
      smtx_model_eval_eq_term_eq, hCondEval]
    rcases smtx_model_eval_eq_boolean
        (__smtx_model_eval M C')
        (__smtx_model_eval M (SmtTerm.Binary 1 1)) with ⟨b, hb⟩
    rw [hb]
    cases b with
    | false =>
        simpa [__smtx_model_eval_ite] using
          smt_value_rel_of_eq_true_or_same M e e' hElse
    | true =>
        simpa [__smtx_model_eval_ite] using
          smt_value_rel_of_eq_true_or_same M t t' hThen

theorem congTypeSpine_bvite_eq_has_bool_type
    (c t e rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
        rhs) :=
  congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.bvite bvIteTerm
    (by intro a b c; rfl)
    (by
      intro a b c a' b' c' ha hb hc
      rw [bvIteTerm, bvIteTerm, typeof_ite_eq, typeof_ite_eq,
        typeof_eq_eq, typeof_eq_eq, ha, hb, hc])
    c t e rhs

def bvFromBoolsTerm (a b : SmtTerm) : SmtTerm :=
  SmtTerm.concat
    b (SmtTerm.ite a (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))

private def bvFromBoolsEval (a b : SmtValue) : SmtValue :=
  __smtx_model_eval_concat
    b (__smtx_model_eval_ite a (SmtValue.Binary 1 1) (SmtValue.Binary 1 0))

theorem bv_from_bools_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (bvFromBoolsTerm a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  rcases bv_concat_args_non_reg_of_non_none
      b (SmtTerm.ite a (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
      (by simpa [bvFromBoolsTerm] using hNN) with
    ⟨B, I, hB, hI, hBNN, hINN, hBReg, _hIReg⟩
  have hIteNN :
      __smtx_typeof
          (SmtTerm.ite a (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) ≠
        SmtType.None := by
    rw [hI]
    exact hINN
  have hIteTerm :
      term_has_non_none_type
        (SmtTerm.ite a (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) := by
    unfold term_has_non_none_type
    exact hIteNN
  rcases ite_args_of_non_none hIteTerm with
    ⟨_T, hA, _hThen, _hElse, _hTNN⟩
  exact ⟨SmtType.Bool, B, hA, hB, by simp, hBNN, by simp, hBReg⟩

theorem congTrueSpine_bv_from_bools_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
        rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp._at_from_bools
    bvFromBoolsTerm bvFromBoolsEval
    (by intro a b; rfl)
    bv_from_bools_args_non_reg_of_non_none
    (by
      intro a b
      rw [bvFromBoolsTerm, bvFromBoolsEval, __smtx_model_eval.eq_36,
        smtx_model_eval_ite_term_eq, __smtx_model_eval.eq_5,
        __smtx_model_eval.eq_5])
    x₁ x₂ rhs

theorem congTypeSpine_bv_from_bools_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp._at_from_bools
    bvFromBoolsTerm
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [bvFromBoolsTerm, bvFromBoolsTerm, typeof_concat_eq,
        typeof_concat_eq, typeof_ite_eq, typeof_ite_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_bv_concat_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.concat SmtTerm.concat
    __smtx_model_eval_concat
    (by intro a b; rfl)
    bv_concat_args_non_reg_of_non_none
    (by intro a b; rw [__smtx_model_eval.eq_36])
    x₁ x₂ rhs

theorem congTypeSpine_bv_concat_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.concat SmtTerm.concat
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_concat_eq, typeof_concat_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_seq_unop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_seq_op_1 (__smtx_typeof a))
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_unop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x rhs

theorem congTypeSpine_seq_unop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_seq_op_1 (__smtx_typeof a))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

theorem congTrueSpine_seq_unop_ret_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_seq_op_1_ret (__smtx_typeof a) R)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_unop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x rhs

theorem congTypeSpine_seq_unop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_seq_op_1_ret (__smtx_typeof a) R)
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

theorem congTrueSpine_seq_char_unop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            R SmtType.None)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_char_unop_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x rhs

theorem congTypeSpine_seq_char_unop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            R SmtType.None)
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

theorem congTrueSpine_seq_binop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_seq_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_binop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x₁ x₂ rhs

theorem congTypeSpine_seq_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_seq_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_seq_binop_ret_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_binop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x₁ x₂ rhs

theorem congTypeSpine_seq_binop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_seq_char_binop_eq_true
    (M : SmtModel) (hM : model_wf M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
              R SmtType.None)
            SmtType.None)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_char_binop_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x₁ x₂ rhs

theorem congTypeSpine_seq_char_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
              R SmtType.None)
            SmtType.None)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private theorem native_model_str_in_re_eq_local
    (str : native_String) (r : SmtRegLan) :
    Smtm.native_str_in_re (impl_native_string_to_values str) r =
      native_str_in_re str r := by
  rw [← RuleProofs.native_str_in_re_eq_model]
  rfl

theorem congTrueSpine_str_in_re_eq_true
    (M : SmtModel) (hM : model_wf M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M UserOp.str_in_re x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y₁) y₂)
        hEqBool
    have hLeftNN :
        __smtx_typeof (SmtTerm.str_in_re X₁ X₂) ≠ SmtType.None := by
      exact hTypes.2
    have hTerm : term_has_non_none_type (SmtTerm.str_in_re X₁ X₂) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs :=
      seq_char_reglan_args_of_non_none
        (op := SmtTerm.str_in_re) (typeof_str_in_re_eq X₁ X₂) hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    have hX₁ValTy :
        __smtx_typeof_value (__smtx_model_eval M X₁) =
          SmtType.Seq SmtType.Char := by
      simpa [hArgs.1] using
        smt_model_eval_preserves_type_of_non_none M hM X₁
          (by simp [term_has_non_none_type, hArgs.1])
    have hSxTy :
        __smtx_typeof_seq_value sx = SmtType.Seq SmtType.Char := by
      simpa [hX₁Eval, __smtx_typeof_value] using hX₁ValTy
    have hUnpack :
        native_unpack_seq sx =
          impl_native_string_to_values (native_unpack_string sx) :=
      native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSxTy
    have hStringValid :
        native_string_valid (native_unpack_string sx) = true :=
      native_unpack_string_valid_of_typeof_seq_char hSxTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2 with
      ⟨rx, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry, hY₂Eval⟩
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt : ∀ str,
        native_string_valid str = true ->
          Smtm.native_str_in_re (impl_native_string_to_values str) rx =
            Smtm.native_str_in_re (impl_native_string_to_values str) ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_in_re X₁ X₂))
        (__smtx_model_eval M (SmtTerm.str_in_re Y₁ Y₂)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_119,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval]
    simp [__smtx_model_eval_str_in_re, __smtx_model_eval_eq, native_veq,
      hUnpack, hExt (native_unpack_string sx) hStringValid]

theorem congTypeSpine_str_in_re_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.str_in_re
    SmtTerm.str_in_re
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_str_in_re_eq, typeof_str_in_re_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_re_comp_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_comp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.re_comp) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.re_comp) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp.re_comp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.re_comp) x)
        (Term.Apply (Term.UOp UserOp.re_comp) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_comp X) ≠ SmtType.None := by
      exact hTypes.2
    have hTerm : term_has_non_none_type (SmtTerm.re_comp X) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hXTy : __smtx_typeof X = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_comp)
        (typeof_re_comp_eq X) hTerm
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hModelExt : ∀ str,
        native_string_valid str = true ->
          Smtm.native_str_in_re (impl_native_string_to_values str) rx =
            Smtm.native_str_in_re (impl_native_string_to_values str) ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      intro str hValid
      simpa only [native_model_str_in_re_eq_local] using
        hModelExt str hValid
    have hExtComp : ∀ str,
        native_string_valid str = true ->
        native_str_in_re str (native_re_comp rx) =
          native_str_in_re str (native_re_comp ry) := by
      intro str hValid
      rw [native_str_in_re_re_comp, native_str_in_re_re_comp, hExt str hValid]
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.re_comp X))
        (__smtx_model_eval M (SmtTerm.re_comp Y)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_112, __smtx_model_eval.eq_112, hXEval,
      hYEval]
    simp [__smtx_model_eval_re_comp, __smtx_model_eval_eq]
    intro s hs
    simpa only [native_model_str_in_re_eq_local] using hExtComp s hs

theorem congTypeSpine_re_comp_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.re_comp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.re_comp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_comp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.re_comp
    SmtTerm.re_comp
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_re_comp_eq, typeof_re_comp_eq, h])
    x rhs

theorem congTrueSpine_re_mult_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_mult) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.re_mult) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.re_mult) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp.re_mult x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.re_mult) x)
        (Term.Apply (Term.UOp UserOp.re_mult) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_mult X) ≠ SmtType.None := by
      exact hTypes.2
    have hTerm : term_has_non_none_type (SmtTerm.re_mult X) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hXTy : __smtx_typeof X = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_mult)
        (typeof_re_mult_eq X) hTerm
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hModelExt : ∀ str,
        native_string_valid str = true ->
          Smtm.native_str_in_re (impl_native_string_to_values str) rx =
            Smtm.native_str_in_re (impl_native_string_to_values str) ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      intro str hValid
      simpa only [native_model_str_in_re_eq_local] using
        hModelExt str hValid
    have hExtStar : ∀ str,
        native_string_valid str = true ->
        native_str_in_re str (native_re_mult rx) =
          native_str_in_re str (native_re_mult ry) := by
      intro str _hValid
      exact native_str_in_re_re_mult_congr str rx ry hExt
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.re_mult X))
        (__smtx_model_eval M (SmtTerm.re_mult Y)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_108, __smtx_model_eval.eq_108, hXEval,
      hYEval]
    simp [__smtx_model_eval_re_mult, __smtx_model_eval_eq]
    intro s hs
    simpa only [native_model_str_in_re_eq_local] using hExtStar s hs

theorem congTrueSpine_re_plus_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_plus) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.re_plus) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.re_plus) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp.re_plus x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.re_plus) x)
        (Term.Apply (Term.UOp UserOp.re_plus) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_plus X) ≠ SmtType.None := by
      exact hTypes.2
    have hTerm : term_has_non_none_type (SmtTerm.re_plus X) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hXTy : __smtx_typeof X = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_plus)
        (typeof_re_plus_eq X) hTerm
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hModelExt : ∀ str,
        native_string_valid str = true ->
          Smtm.native_str_in_re (impl_native_string_to_values str) rx =
            Smtm.native_str_in_re (impl_native_string_to_values str) ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      intro str hValid
      simpa only [native_model_str_in_re_eq_local] using
        hModelExt str hValid
    have hExtPlus : ∀ str,
        native_string_valid str = true ->
        native_str_in_re str (native_re_plus rx) =
          native_str_in_re str (native_re_plus ry) := by
      intro str _hValid
      exact native_str_in_re_re_plus_congr str rx ry hExt
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.re_plus X))
        (__smtx_model_eval M (SmtTerm.re_plus Y)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_109, __smtx_model_eval.eq_109, hXEval,
      hYEval]
    simp [__smtx_model_eval_re_plus, __smtx_model_eval_re_concat,
      __smtx_model_eval_re_mult, native_re_mult,
      native_re_concat, __smtx_model_eval_eq]
    intro s hs
    simpa [native_re_plus, native_re_concat, native_re_mult,
      native_model_str_in_re_eq_local] using hExtPlus s hs

theorem congTrueSpine_re_opt_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_opt) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.re_opt) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.re_opt) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp.re_opt x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    let eps : SmtRegLan :=
      native_str_to_re (native_unpack_seq (SmtSeq.empty SmtType.Char))
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.re_opt) x)
        (Term.Apply (Term.UOp UserOp.re_opt) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_opt X) ≠ SmtType.None := by
      exact hTypes.2
    have hTerm : term_has_non_none_type (SmtTerm.re_opt X) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hXTy : __smtx_typeof X = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_opt)
        (typeof_re_opt_eq X) hTerm
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hModelExt : ∀ str,
        native_string_valid str = true ->
          Smtm.native_str_in_re (impl_native_string_to_values str) rx =
            Smtm.native_str_in_re (impl_native_string_to_values str) ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      intro str hValid
      simpa only [native_model_str_in_re_eq_local] using
        hModelExt str hValid
    have hExtOpt : ∀ str,
        native_string_valid str = true ->
        native_str_in_re str (native_re_union rx eps) =
          native_str_in_re str (native_re_union ry eps) := by
      intro str hValid
      rw [native_str_in_re_re_union, native_str_in_re_re_union, hExt str hValid]
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.re_opt X))
        (__smtx_model_eval M (SmtTerm.re_opt Y)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_111, __smtx_model_eval.eq_111, hXEval,
      hYEval]
    simp [__smtx_model_eval_re_opt, __smtx_model_eval_re_union,
      __smtx_model_eval_eq]
    intro s hs
    simpa only [native_model_str_in_re_eq_local] using hExtOpt s hs

theorem congTypeSpine_re_opt_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.re_opt) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.re_opt) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_opt) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.re_opt
    SmtTerm.re_opt
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_re_opt_eq, typeof_re_opt_eq, h])
    x rhs

private def nativeReEpsilon : SmtRegLan :=
  native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char))

private def nativeReExpRec : native_Nat -> SmtRegLan -> SmtRegLan
  | native_nat_zero, _ => nativeReEpsilon
  | native_nat_succ n, r => native_re_concat (nativeReExpRec n r) r

private theorem model_eval_re_exp_rec_reglan_eq :
    ∀ n r,
      __smtx_re_exp_rec n (SmtValue.RegLan r) =
        SmtValue.RegLan (nativeReExpRec n r) := by
  intro n
  induction n with
  | zero =>
      intro r
      rfl
  | succ n ih =>
      intro r
      simp [__smtx_re_exp_rec, nativeReExpRec, ih,
        __smtx_model_eval_re_concat]

private theorem native_str_in_re_re_exp_rec_congr :
    ∀ n r r',
      (∀ str, native_string_valid str = true ->
        native_str_in_re str r = native_str_in_re str r') ->
      ∀ str,
        native_str_in_re str (nativeReExpRec n r) =
          native_str_in_re str (nativeReExpRec n r') := by
  intro n
  induction n with
  | zero =>
      intro r r' h str
      rfl
  | succ n ih =>
      intro r r' h str
      simpa [nativeReExpRec] using
        native_str_in_re_re_concat_congr str
          (nativeReExpRec n r) (nativeReExpRec n r') r r'
          (fun s _hs => ih r r' h s) h

theorem smt_value_rel_re_exp_reglan_congr
    (n : native_Int) {r r' : SmtRegLan}
    (hExt : ∀ str, native_string_valid str = true ->
      native_str_in_re str r = native_str_in_re str r') :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_re_exp (SmtValue.Numeral n) (SmtValue.RegLan r))
      (__smtx_model_eval_re_exp (SmtValue.Numeral n) (SmtValue.RegLan r')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  have hExtExp :
      ∀ str,
        native_string_valid str = true ->
        native_str_in_re str (nativeReExpRec (native_int_to_nat n) r) =
          native_str_in_re str (nativeReExpRec (native_int_to_nat n) r') :=
    fun str _hValid =>
      native_str_in_re_re_exp_rec_congr (native_int_to_nat n) r r' hExt str
  simp [__smtx_model_eval_re_exp, model_eval_re_exp_rec_reglan_eq,
    __smtx_model_eval_eq]
  intro s hs
  simpa only [native_model_str_in_re_eq_local] using hExtExp s hs

theorem re_exp_index_arg_of_non_none (idx t : SmtTerm) :
    __smtx_typeof (SmtTerm.re_exp idx t) ≠ SmtType.None ->
      ∃ k,
        idx = SmtTerm.Numeral k ∧ __smtx_typeof t = SmtType.RegLan := by
  intro hNN
  cases idx <;> simp [typeof_re_exp_eq, __smtx_typeof_re_exp] at hNN
  case Numeral k =>
    have hTerm : term_has_non_none_type (SmtTerm.re_exp (SmtTerm.Numeral k) t) := by
      unfold term_has_non_none_type
      rw [typeof_re_exp_eq]
      exact hNN
    exact ⟨k, rfl, (re_exp_arg_of_non_none hTerm).2⟩

private def nativeReLoopRec :
    native_Nat -> native_Int -> native_Int -> SmtRegLan -> SmtRegLan
  | native_nat_zero, lo, _hi, r => nativeReExpRec (native_int_to_nat lo) r
  | native_nat_succ n, lo, hi, r =>
      native_re_union
        (nativeReLoopRec n lo (native_zplus hi (native_zneg 1)) r)
        (nativeReExpRec (native_int_to_nat hi) r)

private theorem model_eval_re_loop_rec_reglan_eq :
    ∀ n lo hi r,
      __smtx_re_loop_rec n (SmtValue.Numeral lo)
          (SmtValue.Numeral hi) (SmtValue.RegLan r) =
        SmtValue.RegLan (nativeReLoopRec n lo hi r) := by
  intro n
  induction n with
  | zero =>
      intro lo hi r
      simp [__smtx_re_loop_rec, nativeReLoopRec,
        model_eval_re_exp_rec_reglan_eq, __smtx_model_eval_re_exp]
  | succ n ih =>
      intro lo hi r
      simp [__smtx_re_loop_rec, nativeReLoopRec, ih,
        model_eval_re_exp_rec_reglan_eq, __smtx_model_eval_re_exp,
        __smtx_model_eval_re_union]

private theorem native_str_in_re_re_loop_rec_congr :
    ∀ n lo hi r r',
      (∀ str, native_string_valid str = true ->
        native_str_in_re str r = native_str_in_re str r') ->
      ∀ str,
        native_str_in_re str (nativeReLoopRec n lo hi r) =
          native_str_in_re str (nativeReLoopRec n lo hi r') := by
  intro n
  induction n with
  | zero =>
      intro lo hi r r' h str
      simpa [nativeReLoopRec] using
        native_str_in_re_re_exp_rec_congr (native_int_to_nat lo) r r' h str
  | succ n ih =>
      intro lo hi r r' h str
      rw [nativeReLoopRec, nativeReLoopRec, native_str_in_re_re_union,
        native_str_in_re_re_union,
        ih lo (native_zplus hi (native_zneg 1)) r r' h str,
        native_str_in_re_re_exp_rec_congr (native_int_to_nat hi) r r' h str]

theorem smt_value_rel_re_loop_reglan_congr
    (lo hi : native_Int) {r r' : SmtRegLan}
    (hExt : ∀ str, native_string_valid str = true ->
      native_str_in_re str r = native_str_in_re str r') :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_re_loop (SmtValue.Numeral lo) (SmtValue.Numeral hi)
        (SmtValue.RegLan r))
      (__smtx_model_eval_re_loop (SmtValue.Numeral lo) (SmtValue.Numeral hi)
        (SmtValue.RegLan r')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  by_cases hLt : native_zlt hi lo
  · simp [__smtx_model_eval_re_loop, __smtx_model_eval_gt,
      __smtx_model_eval_lt, __smtx_model_eval_ite, __smtx_model_eval_eq,
      hLt]
  · have hExtLoop :
        ∀ str,
          native_string_valid str = true ->
          native_str_in_re str
              (nativeReLoopRec (native_int_to_nat (native_zplus hi (native_zneg lo)))
                lo hi r) =
            native_str_in_re str
              (nativeReLoopRec (native_int_to_nat (native_zplus hi (native_zneg lo)))
                lo hi r') :=
      fun str _hValid =>
        native_str_in_re_re_loop_rec_congr
          (native_int_to_nat (native_zplus hi (native_zneg lo))) lo hi r r' hExt str
    simp [__smtx_model_eval_re_loop, __smtx_model_eval_gt,
      __smtx_model_eval_lt, __smtx_model_eval_ite,
      model_eval_re_loop_rec_reglan_eq, __smtx_model_eval_eq, hLt]
    intro s hs
    simpa only [native_model_str_in_re_eq_local] using hExtLoop s hs

theorem re_loop_index_arg_of_non_none (lo hi t : SmtTerm) :
    __smtx_typeof (SmtTerm.re_loop lo hi t) ≠ SmtType.None ->
      ∃ loN hiN,
        lo = SmtTerm.Numeral loN ∧ hi = SmtTerm.Numeral hiN ∧
          __smtx_typeof t = SmtType.RegLan := by
  intro hNN
  cases lo
  case Numeral loN =>
    cases hi
    case Numeral hiN =>
      have hTerm :
          term_has_non_none_type
            (SmtTerm.re_loop (SmtTerm.Numeral loN) (SmtTerm.Numeral hiN) t) := by
        unfold term_has_non_none_type
        exact hNN
      exact ⟨loN, hiN, rfl, rfl, (re_loop_arg_of_non_none hTerm).2.2⟩
    all_goals
      exfalso
      apply hNN
      rw [typeof_re_loop_eq]
      simp [__smtx_typeof_re_loop]
  all_goals
    exfalso
    apply hNN
    rw [typeof_re_loop_eq]
    simp [__smtx_typeof_re_loop]


end CongSupport
