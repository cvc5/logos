module

public import Cpc.Proofs.RuleSupport.StrInReConsume.Basic
import all Cpc.Proofs.RuleSupport.StrInReConsume.Basic

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

def StrInReConsumeInternal.str_re_consume_rec_model_rel_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
        side) ->
    side = __str_re_consume_rec s r fuel ->
    side ≠ Term.Stuck ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side))

def StrInReConsumeInternal.str_re_consume_union_model_rel_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
        side) ->
    side = __str_re_consume_union s r fuel ->
    side ≠ Term.Stuck ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side))

def StrInReConsumeInternal.str_re_consume_inter_model_rel_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
        side) ->
    side = __str_re_consume_inter s r fuel ->
    side ≠ Term.Stuck ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side))

def StrInReConsumeInternal.str_re_consume_rec_type_motive
    (s r fuel : Term) : Prop :=
  __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
  __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
  __str_re_consume_rec s r fuel ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (__str_re_consume_rec s r fuel)) =
      SmtType.Bool

def StrInReConsumeInternal.str_re_consume_union_type_motive
    (s r fuel : Term) : Prop :=
  __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
  __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
  __str_re_consume_union s r fuel ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (__str_re_consume_union s r fuel)) =
      SmtType.Bool

def StrInReConsumeInternal.str_re_consume_inter_type_motive
    (s r fuel : Term) : Prop :=
  __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
  __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
  __str_re_consume_inter s r fuel ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (__str_re_consume_inter s r fuel)) =
      SmtType.Bool

theorem StrInReConsumeInternal.consume_eval_eps_re_early_local (M : SmtModel) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
      SmtValue.RegLan (native_str_to_re []) := by
  change __smtx_model_eval M
      (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtValue.RegLan (native_str_to_re [])
  rw [show __smtx_model_eval M
      (SmtTerm.str_to_re (SmtTerm.String [])) =
    __smtx_model_eval_str_to_re
      (__smtx_model_eval M (SmtTerm.String [])) from by
    simp [__smtx_model_eval]]
  rw [show __smtx_model_eval M (SmtTerm.String []) =
    SmtValue.Seq (native_pack_string []) from by
    simp [__smtx_model_eval]]
  simp [__smtx_model_eval_str_to_re]

theorem StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_early_local
    {r1 r2 : SmtRegLan}
    (h : RuleProofs.smt_value_rel (SmtValue.RegLan r1)
      (SmtValue.RegLan r2))
    (str : native_String) :
    native_str_in_re str r1 = native_str_in_re str r2 := by
  cases hV : native_string_valid str with
  | true =>
      simpa [native_str_in_re_eq_model] using
        smt_value_rel_reglan_valid_eq h hV
  | false => simp [native_str_in_re, hV]

theorem StrInReConsumeInternal.consume_elim_unflat_eps_of_eps_early_local :
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
      Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
  have h1 : __re_unflatten (Term.Boolean true)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
      Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
    simp [__re_unflatten]
  rw [h1]
  rfl

theorem StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local
    {X : Term}
    (h : X = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) :
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true) X) =
      Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
  rw [h]
  exact StrInReConsumeInternal.consume_elim_unflat_eps_of_eps_early_local

theorem StrInReConsumeInternal.consume_elim_unflat_stuck_early_local :
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true) Term.Stuck) =
      Term.Stuck := by
  have h1 : __re_unflatten (Term.Boolean true) Term.Stuck =
      Term.Stuck := by
    simp [__re_unflatten]
  rw [h1]
  rfl

def StrInReConsumeInternal.str_re_consume_rec_no_prefix_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_rec s r fuel ->
    side = Term.Boolean false ->
    ∀ ss rv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false

def StrInReConsumeInternal.str_re_consume_union_no_prefix_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_union s r fuel ->
    side = Term.Boolean false ->
    ∀ ss rv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false

def StrInReConsumeInternal.str_re_consume_inter_no_prefix_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_inter s r fuel ->
    side = Term.Boolean false ->
    ∀ ss rv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false

def StrInReConsumeInternal.str_re_consume_rec_residual_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_rec s r fuel ->
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re side)) =
      Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
      SmtType.Seq SmtType.Char ∧
      ∀ q ss rv ss' qv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ss' ->
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (native_unpack_string ss)
              (native_re_concat rv qv) =
            native_str_in_re (native_unpack_string ss') qv

def StrInReConsumeInternal.str_re_consume_union_residual_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_union s r fuel ->
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re side)) =
      Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
      SmtType.Seq SmtType.Char ∧
      ∀ q ss rv ss' qv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ss' ->
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (native_unpack_string ss)
              (native_re_concat rv qv) =
            native_str_in_re (native_unpack_string ss') qv

def StrInReConsumeInternal.str_re_consume_inter_residual_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_inter s r fuel ->
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re side)) =
      Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
      SmtType.Seq SmtType.Char ∧
      ∀ q ss rv ss' qv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ss' ->
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (native_unpack_string ss)
              (native_re_concat rv qv) =
            native_str_in_re (native_unpack_string ss') qv

def StrInReConsumeInternal.str_re_consume_rec_semantic_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  StrInReConsumeInternal.str_re_consume_rec_no_prefix_motive M s r fuel ∧
    StrInReConsumeInternal.str_re_consume_rec_residual_motive M s r fuel

def StrInReConsumeInternal.str_re_consume_union_semantic_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  StrInReConsumeInternal.str_re_consume_union_no_prefix_motive M s r fuel ∧
    StrInReConsumeInternal.str_re_consume_union_residual_motive M s r fuel

def StrInReConsumeInternal.str_re_consume_inter_semantic_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  StrInReConsumeInternal.str_re_consume_inter_no_prefix_motive M s r fuel ∧
    StrInReConsumeInternal.str_re_consume_inter_residual_motive M s r fuel

theorem str_re_consume_no_prefix_side_str_in_re_absurd_local
    (M : SmtModel) (s r side : Term)
    (hSide :
      side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)
    (hFalse : side = Term.Boolean false) :
    ∀ ss rv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false := by
  subst side
  cases hFalse

theorem str_re_consume_residual_side_str_in_re_local
    (M : SmtModel) (hM : model_wf M) (s r side : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hSide :
      side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)
    (hMemEq :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re side)) =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) :
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
      SmtType.Seq SmtType.Char ∧
      ∀ q ss rv ss' qv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ss' ->
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (native_unpack_string ss)
              (native_re_concat rv qv) =
            native_str_in_re (native_unpack_string ss') qv := by
  subst side
  rw [str_membership_re_str_in_re] at hMemEq
  constructor
  · rw [str_membership_str_str_in_re]
    exact hSTy
  · intro q ss rv ss' qv hSEval hREval hTailEval hQEval
    rw [str_membership_str_str_in_re] at hTailEval
    have hSs : ss = ss' := by
      rw [hSEval] at hTailEval
      injection hTailEval
    subst hSs
    have hElimNe :
        __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true) r) ≠ Term.Stuck := by
      rw [hMemEq]
      intro h
      cases h
    rcases re_unflatten_singleton_elim_eval_rel_consume_local M hM r rv
        hRTy hREval hElimNe with ⟨outRv, hOutEval, _hOutTy, hOutRel⟩
    rw [hMemEq] at hOutEval
    have hOutEps : outRv = native_str_to_re [] := by
      rw [StrInReConsumeInternal.consume_eval_eps_re_early_local M] at hOutEval
      injection hOutEval with hh
      exact hh.symm
    rw [hOutEps] at hOutRel
    have hConcatRel :=
      smt_value_rel_re_concat_consume_local
        (RuleProofs.smt_value_rel_symm _ _ hOutRel)
        (RuleProofs.smt_value_rel_refl (SmtValue.RegLan qv))
    rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_early_local hConcatRel]
    rw [native_re_concat_left_empty_local]

theorem str_re_consume_rec_semantic_of_side_eq_str_in_re_local
    (M : SmtModel) (hM : model_wf M) (s r fuel : Term)
    (hEq :
      __str_re_consume_rec s r fuel =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s r fuel := by
  constructor
  · intro side _hSTy _hRTy hSide hFalse
    have hSideStr :
        side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
      rw [hSide, hEq]
    exact str_re_consume_no_prefix_side_str_in_re_absurd_local M s r
      side hSideStr hFalse
  · intro side hSTy hRTy hSide hMemEq
    have hSideStr :
        side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
      rw [hSide, hEq]
    exact str_re_consume_residual_side_str_in_re_local M hM s r side
      hSTy hRTy hSideStr hMemEq

theorem str_re_consume_union_semantic_of_side_eq_str_in_re_local
    (M : SmtModel) (hM : model_wf M) (s r fuel : Term)
    (hEq :
      __str_re_consume_union s r fuel =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    StrInReConsumeInternal.str_re_consume_union_semantic_motive M s r fuel := by
  constructor
  · intro side _hSTy _hRTy hSide hFalse
    have hSideStr :
        side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
      rw [hSide, hEq]
    exact str_re_consume_no_prefix_side_str_in_re_absurd_local M s r
      side hSideStr hFalse
  · intro side hSTy hRTy hSide hMemEq
    have hSideStr :
        side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
      rw [hSide, hEq]
    exact str_re_consume_residual_side_str_in_re_local M hM s r side
      hSTy hRTy hSideStr hMemEq

theorem str_re_consume_inter_semantic_of_side_eq_str_in_re_local
    (M : SmtModel) (hM : model_wf M) (s r fuel : Term)
    (hEq :
      __str_re_consume_inter s r fuel =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    StrInReConsumeInternal.str_re_consume_inter_semantic_motive M s r fuel := by
  constructor
  · intro side _hSTy _hRTy hSide hFalse
    have hSideStr :
        side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
      rw [hSide, hEq]
    exact str_re_consume_no_prefix_side_str_in_re_absurd_local M s r
      side hSideStr hFalse
  · intro side hSTy hRTy hSide hMemEq
    have hSideStr :
        side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
      rw [hSide, hEq]
    exact str_re_consume_residual_side_str_in_re_local M hM s r side
      hSTy hRTy hSideStr hMemEq

theorem str_re_consume_rec_semantic_of_false_local
    (M : SmtModel) (s r fuel : Term)
    (hEq : __str_re_consume_rec s r fuel = Term.Boolean false)
    (hNoPrefix :
      ∀ (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
        (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
        (ss : SmtSeq) (rv : SmtRegLan),
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              native_str_in_re pre rv = false) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s r fuel := by
  constructor
  · intro side hSTy hRTy hSide hFalse ss rv hSEval hREval pre suf hAppend
    exact hNoPrefix hSTy hRTy ss rv hSEval hREval pre suf hAppend
  · intro side _hSTy _hRTy hSide hMemEq
    have hSideFalse : side = Term.Boolean false := by
      rw [hSide, hEq]
    rw [hSideFalse] at hMemEq
    rw [show __str_membership_re (Term.Boolean false) = Term.Stuck by
      simp [__str_membership_re]] at hMemEq
    rw [StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    cases hMemEq

theorem str_re_consume_union_semantic_of_false_local
    (M : SmtModel) (s r fuel : Term)
    (hEq : __str_re_consume_union s r fuel = Term.Boolean false)
    (hNoPrefix :
      ∀ (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
        (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
        (ss : SmtSeq) (rv : SmtRegLan),
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              native_str_in_re pre rv = false) :
    StrInReConsumeInternal.str_re_consume_union_semantic_motive M s r fuel := by
  constructor
  · intro side hSTy hRTy hSide hFalse ss rv hSEval hREval pre suf hAppend
    exact hNoPrefix hSTy hRTy ss rv hSEval hREval pre suf hAppend
  · intro side _hSTy _hRTy hSide hMemEq
    have hSideFalse : side = Term.Boolean false := by
      rw [hSide, hEq]
    rw [hSideFalse] at hMemEq
    rw [show __str_membership_re (Term.Boolean false) = Term.Stuck by
      simp [__str_membership_re]] at hMemEq
    rw [StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    cases hMemEq

theorem str_re_consume_inter_semantic_of_false_local
    (M : SmtModel) (s r fuel : Term)
    (hEq : __str_re_consume_inter s r fuel = Term.Boolean false)
    (hNoPrefix :
      ∀ (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
        (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
        (ss : SmtSeq) (rv : SmtRegLan),
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              native_str_in_re pre rv = false) :
    StrInReConsumeInternal.str_re_consume_inter_semantic_motive M s r fuel := by
  constructor
  · intro side hSTy hRTy hSide hFalse ss rv hSEval hREval pre suf hAppend
    exact hNoPrefix hSTy hRTy ss rv hSEval hREval pre suf hAppend
  · intro side _hSTy _hRTy hSide hMemEq
    have hSideFalse : side = Term.Boolean false := by
      rw [hSide, hEq]
    rw [hSideFalse] at hMemEq
    rw [show __str_membership_re (Term.Boolean false) = Term.Stuck by
      simp [__str_membership_re]] at hMemEq
    rw [StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    cases hMemEq

theorem str_re_consume_rec_re_concat_empty_left_semantic_from_ih
    (M : SmtModel) (hM : model_wf M) (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s r fuel) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
        r)
      fuel := by
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let concat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) eps) r
  have hEq :
      __str_re_consume_rec s concat fuel =
        __str_re_consume_rec s r fuel := by
    simpa [eps, concat] using
      str_re_consume_rec_re_concat_empty_left_eq s r fuel hS hFuel
  constructor
  · intro side hSTy hConcatTy hSide hFalse
    have hArgs :
        __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt eps) (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt concat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt concat) = SmtType.RegLan by
          simpa [eps, concat] using hConcatTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt eps) (__eo_to_smt r)) hNN
    have hSide' : side = __str_re_consume_rec s r fuel := by
      rw [hSide, hEq]
    intro ss rv hSEval hConcatEval pre suf hAppend
    rcases eval_re_concat_parts_consume_local M hM eps r rv
        (by simpa [eps, concat] using hConcatTy)
        (by simpa [eps, concat] using hConcatEval) with
      ⟨rvEps, rvTail, _hEpsTy, hRTy, hEpsEval, hRTailEval, hRv⟩
    have hEpsEval' :
        __smtx_model_eval M (__eo_to_smt eps) =
          SmtValue.RegLan (native_str_to_re []) := by
      dsimp [eps]
      change __smtx_model_eval M
          (SmtTerm.str_to_re (SmtTerm.String [])) =
        SmtValue.RegLan (native_str_to_re [])
      simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
       ]
    have hRvEps : rvEps = native_str_to_re [] := by
      rw [hEpsEval'] at hEpsEval
      cases hEpsEval
      rfl
    subst rvEps
    have hRvTail : rv = rvTail := by
      rw [hRv, native_re_concat_left_empty_local]
    subst rv
    simpa [native_re_concat_left_empty_local] using
      ih.1 side hSTy hRTy hSide' hFalse ss rvTail hSEval
        hRTailEval pre suf hAppend
  · intro side hSTy hConcatTy hSide hMemEq
    have hArgs :
        __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt eps) (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt concat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt concat) = SmtType.RegLan by
          simpa [eps, concat] using hConcatTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt eps) (__eo_to_smt r)) hNN
    have hSide' : side = __str_re_consume_rec s r fuel := by
      rw [hSide, hEq]
    refine ⟨(ih.2 side hSTy hArgs.2 hSide' hMemEq).1, ?_⟩
    intro q ss rv ss' qv hSEval hConcatEval hTailEval hQEval
    rcases eval_re_concat_parts_consume_local M hM eps r rv
        (by simpa [eps, concat] using hConcatTy)
        (by simpa [eps, concat] using hConcatEval) with
      ⟨rvEps, rvTail, _hEpsTy, hRTy, hEpsEval, hRTailEval, hRv⟩
    have hEpsEval' :
        __smtx_model_eval M (__eo_to_smt eps) =
          SmtValue.RegLan (native_str_to_re []) := by
      dsimp [eps]
      change __smtx_model_eval M
          (SmtTerm.str_to_re (SmtTerm.String [])) =
        SmtValue.RegLan (native_str_to_re [])
      simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
       ]
    have hRvEps : rvEps = native_str_to_re [] := by
      rw [hEpsEval'] at hEpsEval
      cases hEpsEval
      rfl
    subst rvEps
    have hRvTail : rv = rvTail := by
      rw [hRv, native_re_concat_left_empty_local]
    subst rv
    simpa [native_re_concat_left_empty_local] using
      (ih.2 side hSTy hRTy hSide' hMemEq).2 q ss rvTail ss' qv
        hSEval hRTailEval hTailEval hQEval

theorem str_re_consume_union_re_none_semantic_from_ih
    (M : SmtModel) (hM : model_wf M) (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s r fuel) :
    StrInReConsumeInternal.str_re_consume_union_semantic_motive M s
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r)
        (Term.UOp UserOp.re_none))
      fuel := by
  let none := Term.UOp UserOp.re_none
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) none
  have hEq :
      __str_re_consume_union s union fuel =
        __str_re_consume_rec s r fuel := by
    simpa [none, union] using
      str_re_consume_union_re_none_eq s r fuel hS hFuel
  constructor
  · intro side hSTy hUnionTy hSide hFalse ss rv hSEval hUnionEval pre
      suf hAppend
    have hSide' : side = __str_re_consume_rec s r fuel := by
      rw [hSide, hEq]
    rcases eval_re_union_parts_consume_local M hM r none rv
        (by simpa [none, union] using hUnionTy)
        (by simpa [none, union] using hUnionEval) with
      ⟨rvR, rvNone, hRTy, _hNoneTy, hREval, hNoneEval, hRv⟩
    have hRvNone : rvNone = native_re_none := by
      change __smtx_model_eval M SmtTerm.re_none =
        SmtValue.RegLan rvNone at hNoneEval
      simpa [__smtx_model_eval] using hNoneEval.symm
    subst rvNone
    subst rv
    rw [native_str_in_re_re_union_right_none_consume_local]
    exact ih.1 side hSTy hRTy hSide' hFalse ss rvR hSEval hREval
      pre suf hAppend
  · intro side hSTy hUnionTy hSide hMemEq
    have hArgs :
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt none) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_union (__eo_to_smt r) (__eo_to_smt none)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt union) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt union) = SmtType.RegLan by
          simpa [none, union] using hUnionTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
        (typeof_re_union_eq (__eo_to_smt r) (__eo_to_smt none)) hNN
    have hSide' : side = __str_re_consume_rec s r fuel := by
      rw [hSide, hEq]
    refine ⟨(ih.2 side hSTy hArgs.1 hSide' hMemEq).1, ?_⟩
    intro q ss rv ss' qv hSEval hUnionEval hTailEval hQEval
    rcases eval_re_union_parts_consume_local M hM r none rv
        (by simpa [none, union] using hUnionTy)
        (by simpa [none, union] using hUnionEval) with
      ⟨rvR, rvNone, hRTy, _hNoneTy, hREval, hNoneEval, hRv⟩
    have hRvNone : rvNone = native_re_none := by
      change __smtx_model_eval M SmtTerm.re_none =
        SmtValue.RegLan rvNone at hNoneEval
      simpa [__smtx_model_eval] using hNoneEval.symm
    subst rvNone
    subst rv
    rw [native_str_in_re_re_concat_union_right_none_consume_local]
    exact (ih.2 side hSTy hRTy hSide' hMemEq).2 q ss rvR ss' qv
      hSEval hREval hTailEval hQEval

theorem str_re_consume_inter_re_all_semantic_from_ih
    (M : SmtModel) (hM : model_wf M) (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s r fuel) :
    StrInReConsumeInternal.str_re_consume_inter_semantic_motive M s
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r)
        (Term.UOp UserOp.re_all))
      fuel := by
  let all := Term.UOp UserOp.re_all
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) all
  have hEq :
      __str_re_consume_inter s inter fuel =
        __str_re_consume_rec s r fuel := by
    simpa [all, inter] using
      str_re_consume_inter_re_all_eq s r fuel hS hFuel
  constructor
  · intro side hSTy hInterTy hSide hFalse ss rv hSEval hInterEval pre
      suf hAppend
    have hSide' : side = __str_re_consume_rec s r fuel := by
      rw [hSide, hEq]
    rcases eval_re_inter_parts_consume_local M hM r all rv
        (by simpa [all, inter] using hInterTy)
        (by simpa [all, inter] using hInterEval) with
      ⟨rvR, rvAll, hRTy, _hAllTy, hREval, hAllEval, hRv⟩
    have hRvAll : rvAll = native_re_all := by
      change __smtx_model_eval M SmtTerm.re_all =
        SmtValue.RegLan rvAll at hAllEval
      simpa [__smtx_model_eval] using hAllEval.symm
    subst rvAll
    subst rv
    rw [native_str_in_re_re_inter_right_all_consume_local]
    exact ih.1 side hSTy hRTy hSide' hFalse ss rvR hSEval hREval
      pre suf hAppend
  · intro side hSTy hInterTy hSide hMemEq
    have hArgs :
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt all) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_inter (__eo_to_smt r) (__eo_to_smt all)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt inter) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt inter) = SmtType.RegLan by
          simpa [all, inter] using hInterTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
        (typeof_re_inter_eq (__eo_to_smt r) (__eo_to_smt all)) hNN
    have hSide' : side = __str_re_consume_rec s r fuel := by
      rw [hSide, hEq]
    refine ⟨(ih.2 side hSTy hArgs.1 hSide' hMemEq).1, ?_⟩
    intro q ss rv ss' qv hSEval hInterEval hTailEval hQEval
    rcases eval_re_inter_parts_consume_local M hM r all rv
        (by simpa [all, inter] using hInterTy)
        (by simpa [all, inter] using hInterEval) with
      ⟨rvR, rvAll, hRTy, _hAllTy, hREval, hAllEval, hRv⟩
    have hRvAll : rvAll = native_re_all := by
      change __smtx_model_eval M SmtTerm.re_all =
        SmtValue.RegLan rvAll at hAllEval
      simpa [__smtx_model_eval] using hAllEval.symm
    subst rvAll
    subst rv
    rw [native_str_in_re_re_concat_inter_right_all_consume_local]
    exact (ih.2 side hSTy hRTy hSide' hMemEq).2 q ss rvR ss' qv
      hSEval hREval hTailEval hQEval

theorem str_re_consume_union_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_none)
    (ihLeft : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s c1 fuel)
    (ihRight : StrInReConsumeInternal.str_re_consume_union_semantic_motive M s c2 fuel) :
    StrInReConsumeInternal.str_re_consume_union_semantic_motive M s
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
      fuel := by
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2
  let left := __str_re_consume_rec s c1 fuel
  let right := __str_re_consume_union s c2 fuel
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let condLeftFalse := __eo_is_eq left (Term.Boolean false)
  let condMem := __eo_eq (__str_membership_re left) eps
  let condRightFalse := __eo_is_eq right (Term.Boolean false)
  let condSame := __eo_eq left right
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
    union
  let sameIte := __eo_ite condSame left fallback
  let rightIte := __eo_ite condRightFalse left sameIte
  let memIte := __eo_ite condMem rightIte fallback
  let whole := __eo_ite condLeftFalse right memIte
  constructor
  · intro side hSTy hUnionTy hSide hFalse ss rv hSEval hUnionEval pre suf
      hAppend
    rcases eval_re_union_parts_consume_local M hM c1 c2 rv hUnionTy
        hUnionEval with
      ⟨rv1, rv2, hC1Ty, hC2Ty, hC1Eval, hC2Eval, hRv⟩
    subst rv
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS
        hFuel]
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      have hSideStuck : side = Term.Stuck := by
        rw [hSideWhole, hBad]
      rw [hFalse] at hSideStuck
      cases hSideStuck
    rcases eo_ite_cases_of_ne_stuck condLeftFalse right memIte hWholeNe with
      hLeftFalseTrue | hLeftFalseFalse
    · have hSideRight : side = right := by
        rw [hSideWhole]
        simp [whole, hLeftFalseTrue, eo_ite_true]
      have hLeftEqFalse : left = Term.Boolean false :=
        eq_of_eo_is_eq_true_consume_local left (Term.Boolean false)
          (by simpa [condLeftFalse] using hLeftFalseTrue)
      have hRightFalse : right = Term.Boolean false := by
        rw [← hSideRight]
        exact hFalse
      exact
        native_str_in_re_re_union_false_of_no_split_local
          (native_unpack_string ss) rv1 rv2
          (fun pre suf hAppend =>
            ihLeft.1 left hSTy hC1Ty rfl hLeftEqFalse ss rv1 hSEval
              hC1Eval pre suf hAppend)
          (fun pre suf hAppend =>
            ihRight.1 right hSTy hC2Ty rfl hRightFalse ss rv2 hSEval
              hC2Eval pre suf hAppend)
          pre suf hAppend
    · have hMemIteNe : memIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLeftFalseFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condMem rightIte fallback
          hMemIteNe with hMemTrue | hMemFalse
      · have hRightIteNe : rightIte ≠ Term.Stuck := by
          intro hBad
          apply hMemIteNe
          simpa [memIte, hMemTrue, eo_ite_true] using hBad
        rcases eo_ite_cases_of_ne_stuck condRightFalse left sameIte
            hRightIteNe with hRightFalseTrue | hRightFalseFalse
        · have hSideLeft : side = left := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemTrue,
              eo_ite_true, rightIte, hRightFalseTrue]
          have hRightEqFalse : right = Term.Boolean false :=
            eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
              (by simpa [condRightFalse] using hRightFalseTrue)
          have hLeftFalse : left = Term.Boolean false := by
            rw [← hSideLeft]
            exact hFalse
          exact
            native_str_in_re_re_union_false_of_no_split_local
              (native_unpack_string ss) rv1 rv2
              (fun pre suf hAppend =>
                ihLeft.1 left hSTy hC1Ty rfl hLeftFalse ss rv1 hSEval
                  hC1Eval pre suf hAppend)
              (fun pre suf hAppend =>
                ihRight.1 right hSTy hC2Ty rfl hRightEqFalse ss rv2
                  hSEval hC2Eval pre suf hAppend)
              pre suf hAppend
        · have hSameIteNe : sameIte ≠ Term.Stuck := by
            intro hBad
            apply hRightIteNe
            simpa [rightIte, hRightFalseFalse, eo_ite_false] using hBad
          rcases eo_ite_cases_of_ne_stuck condSame left fallback
              hSameIteNe with hSameTrue | hSameFalse
          · have hSideLeft : side = left := by
              rw [hSideWhole]
              simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
                hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
                sameIte, hSameTrue]
            have hSameEq : left = right :=
              (eq_of_eo_eq_true left right
                (by simpa [condSame] using hSameTrue)).symm
            have hLeftFalse : left = Term.Boolean false := by
              rw [← hSideLeft]
              exact hFalse
            have hRightFalse : right = Term.Boolean false := by
              rw [← hSameEq]
              exact hLeftFalse
            exact
              native_str_in_re_re_union_false_of_no_split_local
                (native_unpack_string ss) rv1 rv2
                (fun pre suf hAppend =>
                  ihLeft.1 left hSTy hC1Ty rfl hLeftFalse ss rv1
                    hSEval hC1Eval pre suf hAppend)
                (fun pre suf hAppend =>
                  ihRight.1 right hSTy hC2Ty rfl hRightFalse ss rv2
                    hSEval hC2Eval pre suf hAppend)
                pre suf hAppend
          · have hSideFallback : side = fallback := by
              rw [hSideWhole]
              simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
                hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
                sameIte, hSameFalse]
            exfalso
            rw [hSideFallback] at hFalse
            simp [fallback] at hFalse
      · have hSideFallback : side = fallback := by
          rw [hSideWhole]
          simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemFalse]
        exfalso
        rw [hSideFallback] at hFalse
        simp [fallback] at hFalse
  · intro side hSTy hUnionTy hSide hMemEq
    have hUnionArgs :
        __smtx_typeof (__eo_to_smt c1) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt c2) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_union (__eo_to_smt c1) (__eo_to_smt c2)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt union) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt union) = SmtType.RegLan by
          simpa [union] using hUnionTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
        (typeof_re_union_eq (__eo_to_smt c1) (__eo_to_smt c2)) hNN
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS
        hFuel]
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      apply hSideNe
      rw [hSideWhole, hBad]
    rcases eo_ite_cases_of_ne_stuck condLeftFalse right memIte hWholeNe with
      hLeftFalseTrue | hLeftFalseFalse
    · have hSideRight : side = right := by
        rw [hSideWhole]
        simp [whole, hLeftFalseTrue, eo_ite_true]
      have hLeftEqFalse : left = Term.Boolean false :=
        eq_of_eo_is_eq_true_consume_local left (Term.Boolean false)
          (by simpa [condLeftFalse] using hLeftFalseTrue)
      have hRightResidual :=
        ihRight.2 side hSTy hUnionArgs.2 hSideRight hMemEq
      refine ⟨hRightResidual.1, ?_⟩
      intro q ss rv ss' qv hSEval hUnionEval hTailEval hQEval
      rcases eval_re_union_parts_consume_local M hM c1 c2 rv hUnionTy
          hUnionEval with
        ⟨rv1, rv2, hC1Ty, _hC2Ty, hC1Eval, hC2Eval, hRv⟩
      subst rv
      have hLeftNoPrefix :
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              native_str_in_re pre rv1 = false :=
        fun pre suf hAppend =>
          ihLeft.1 left hSTy hC1Ty rfl hLeftEqFalse ss rv1 hSEval
            hC1Eval pre suf hAppend
      calc
        native_str_in_re (native_unpack_string ss)
            (native_re_concat (native_re_union rv1 rv2) qv) =
          native_str_in_re (native_unpack_string ss)
            (native_re_concat rv2 qv) :=
            native_str_in_re_re_concat_union_left_no_prefix_local
              (native_unpack_string ss) rv1 rv2 qv hLeftNoPrefix
        _ = native_str_in_re (native_unpack_string ss') qv :=
            hRightResidual.2 q ss rv2 ss' qv hSEval hC2Eval hTailEval
              hQEval
    · have hMemIteNe : memIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLeftFalseFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condMem rightIte fallback
          hMemIteNe with hMemTrue | hMemFalse
      · have hRightIteNe : rightIte ≠ Term.Stuck := by
          intro hBad
          apply hMemIteNe
          simpa [memIte, hMemTrue, eo_ite_true] using hBad
        rcases eo_ite_cases_of_ne_stuck condRightFalse left sameIte
            hRightIteNe with hRightFalseTrue | hRightFalseFalse
        · have hSideLeft : side = left := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemTrue,
              eo_ite_true, rightIte, hRightFalseTrue]
          have hRightEqFalse : right = Term.Boolean false :=
            eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
              (by simpa [condRightFalse] using hRightFalseTrue)
          have hLeftResidual :=
            ihLeft.2 side hSTy hUnionArgs.1 hSideLeft hMemEq
          refine ⟨hLeftResidual.1, ?_⟩
          intro q ss rv ss' qv hSEval hUnionEval hTailEval hQEval
          rcases eval_re_union_parts_consume_local M hM c1 c2 rv hUnionTy
              hUnionEval with
            ⟨rv1, rv2, _hC1Ty, hC2Ty, hC1Eval, hC2Eval, hRv⟩
          subst rv
          have hRightNoPrefix :
              ∀ pre suf : native_String,
                pre ++ suf = native_unpack_string ss ->
                  native_str_in_re pre rv2 = false :=
            fun pre suf hAppend =>
              ihRight.1 right hSTy hC2Ty rfl hRightEqFalse ss rv2
                hSEval hC2Eval pre suf hAppend
          calc
            native_str_in_re (native_unpack_string ss)
                (native_re_concat (native_re_union rv1 rv2) qv) =
              native_str_in_re (native_unpack_string ss)
                (native_re_concat rv1 qv) :=
                native_str_in_re_re_concat_union_right_no_prefix_local
                  (native_unpack_string ss) rv1 rv2 qv hRightNoPrefix
            _ = native_str_in_re (native_unpack_string ss') qv :=
                hLeftResidual.2 q ss rv1 ss' qv hSEval hC1Eval
                  hTailEval hQEval
        · have hSameIteNe : sameIte ≠ Term.Stuck := by
            intro hBad
            apply hRightIteNe
            simpa [rightIte, hRightFalseFalse, eo_ite_false] using hBad
          rcases eo_ite_cases_of_ne_stuck condSame left fallback
              hSameIteNe with hSameTrue | hSameFalse
          · have hSideLeft : side = left := by
              rw [hSideWhole]
              simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
                hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
                sameIte, hSameTrue]
            have hSameEq : left = right :=
              (eq_of_eo_eq_true left right
                (by simpa [condSame] using hSameTrue)).symm
            have hSideRight : side = right := by
              rw [hSideLeft, hSameEq]
            have hLeftResidual :=
              ihLeft.2 side hSTy hUnionArgs.1 hSideLeft hMemEq
            have hRightResidual :=
              ihRight.2 side hSTy hUnionArgs.2 hSideRight hMemEq
            refine ⟨hLeftResidual.1, ?_⟩
            intro q ss rv ss' qv hSEval hUnionEval hTailEval hQEval
            rcases eval_re_union_parts_consume_local M hM c1 c2 rv hUnionTy
                hUnionEval with
              ⟨rv1, rv2, _hC1Ty, _hC2Ty, hC1Eval, hC2Eval, hRv⟩
            subst rv
            exact
              native_str_in_re_re_concat_union_same_residual_local
                (native_unpack_string ss) (native_unpack_string ss') rv1
                rv2 qv
                (hLeftResidual.2 q ss rv1 ss' qv hSEval hC1Eval
                  hTailEval hQEval)
                (hRightResidual.2 q ss rv2 ss' qv hSEval hC2Eval
                  hTailEval hQEval)
          · have hSideFallback : side = fallback := by
              rw [hSideWhole]
              simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
                hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
                sameIte, hSameFalse]
            exact str_re_consume_residual_side_str_in_re_local M hM s union
              side hSTy hUnionTy hSideFallback hMemEq
      · have hSideFallback : side = fallback := by
          rw [hSideWhole]
          simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemFalse]
        exact str_re_consume_residual_side_str_in_re_local M hM s union side
          hSTy hUnionTy hSideFallback hMemEq

theorem str_re_consume_inter_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_all)
    (ihLeft : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s c1 fuel)
    (ihRight : StrInReConsumeInternal.str_re_consume_inter_semantic_motive M s c2 fuel) :
    StrInReConsumeInternal.str_re_consume_inter_semantic_motive M s
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
      fuel := by
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2
  let left := __str_re_consume_rec s c1 fuel
  let right := __str_re_consume_inter s c2 fuel
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let condLeftFalse := __eo_is_eq left (Term.Boolean false)
  let condMem := __eo_eq (__str_membership_re left) eps
  let condRightFalse := __eo_is_eq right (Term.Boolean false)
  let condSame := __eo_eq left right
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
    inter
  let sameIte := __eo_ite condSame left fallback
  let rightIte := __eo_ite condRightFalse (Term.Boolean false) sameIte
  let rightFallbackIte := __eo_ite condRightFalse (Term.Boolean false)
    fallback
  let memIte := __eo_ite condMem rightIte rightFallbackIte
  let whole := __eo_ite condLeftFalse (Term.Boolean false) memIte
  constructor
  · intro side hSTy hInterTy hSide hFalse ss rv hSEval hInterEval pre suf
      hAppend
    rcases eval_re_inter_parts_consume_local M hM c1 c2 rv hInterTy
        hInterEval with
      ⟨rv1, rv2, hC1Ty, hC2Ty, hC1Eval, hC2Eval, hRv⟩
    subst rv
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS
        hFuel]
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      have hSideStuck : side = Term.Stuck := by
        rw [hSideWhole, hBad]
      rw [hFalse] at hSideStuck
      cases hSideStuck
    rcases eo_ite_cases_of_ne_stuck condLeftFalse (Term.Boolean false)
        memIte hWholeNe with hLeftFalseTrue | hLeftFalseFalse
    · have hLeftEqFalse : left = Term.Boolean false :=
        eq_of_eo_is_eq_true_consume_local left (Term.Boolean false)
          (by simpa [condLeftFalse] using hLeftFalseTrue)
      exact
        native_str_in_re_re_inter_false_of_left_no_split_local
          (native_unpack_string ss) rv1 rv2
          (fun pre suf hAppend =>
            ihLeft.1 left hSTy hC1Ty rfl hLeftEqFalse ss rv1 hSEval
              hC1Eval pre suf hAppend)
          pre suf hAppend
    · have hMemIteNe : memIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLeftFalseFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condMem rightIte rightFallbackIte
          hMemIteNe with hMemTrue | hMemFalse
      · have hRightIteNe : rightIte ≠ Term.Stuck := by
          intro hBad
          apply hMemIteNe
          simpa [memIte, hMemTrue, eo_ite_true] using hBad
        rcases eo_ite_cases_of_ne_stuck condRightFalse
            (Term.Boolean false) sameIte hRightIteNe with
          hRightFalseTrue | hRightFalseFalse
        · have hRightEqFalse : right = Term.Boolean false :=
            eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
              (by simpa [condRightFalse] using hRightFalseTrue)
          exact
            native_str_in_re_re_inter_false_of_right_no_split_local
              (native_unpack_string ss) rv1 rv2
              (fun pre suf hAppend =>
                ihRight.1 right hSTy hC2Ty rfl hRightEqFalse ss rv2
                  hSEval hC2Eval pre suf hAppend)
              pre suf hAppend
        · have hSameIteNe : sameIte ≠ Term.Stuck := by
            intro hBad
            apply hRightIteNe
            simpa [rightIte, hRightFalseFalse, eo_ite_false] using hBad
          rcases eo_ite_cases_of_ne_stuck condSame left fallback
              hSameIteNe with hSameTrue | hSameFalse
          · have hSideLeft : side = left := by
              rw [hSideWhole]
              simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
                hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
                sameIte, hSameTrue]
            have hLeftFalse : left = Term.Boolean false := by
              rw [← hSideLeft]
              exact hFalse
            exact
              native_str_in_re_re_inter_false_of_left_no_split_local
                (native_unpack_string ss) rv1 rv2
                (fun pre suf hAppend =>
                  ihLeft.1 left hSTy hC1Ty rfl hLeftFalse ss rv1
                    hSEval hC1Eval pre suf hAppend)
                pre suf hAppend
          · have hSideFallback : side = fallback := by
              rw [hSideWhole]
              simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
                hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
                sameIte, hSameFalse]
            exfalso
            rw [hSideFallback] at hFalse
            simp [fallback] at hFalse
      · have hRightFallbackIteNe : rightFallbackIte ≠ Term.Stuck := by
          intro hBad
          apply hMemIteNe
          simpa [memIte, hMemFalse, eo_ite_false] using hBad
        rcases eo_ite_cases_of_ne_stuck condRightFalse
            (Term.Boolean false) fallback hRightFallbackIteNe with
          hRightFalseTrue | hRightFalseFalse
        · have hRightEqFalse : right = Term.Boolean false :=
            eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
              (by simpa [condRightFalse] using hRightFalseTrue)
          exact
            native_str_in_re_re_inter_false_of_right_no_split_local
              (native_unpack_string ss) rv1 rv2
              (fun pre suf hAppend =>
                ihRight.1 right hSTy hC2Ty rfl hRightEqFalse ss rv2
                  hSEval hC2Eval pre suf hAppend)
              pre suf hAppend
        · have hSideFallback : side = fallback := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemFalse,
              rightFallbackIte, hRightFalseFalse, eo_ite_false]
          exfalso
          rw [hSideFallback] at hFalse
          simp [fallback] at hFalse
  · intro side hSTy hInterTy hSide hMemEq
    have hInterArgs :
        __smtx_typeof (__eo_to_smt c1) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt c2) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_inter (__eo_to_smt c1) (__eo_to_smt c2)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt inter) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt inter) = SmtType.RegLan by
          simpa [inter] using hInterTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
        (typeof_re_inter_eq (__eo_to_smt c1) (__eo_to_smt c2)) hNN
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS
        hFuel]
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      apply hSideNe
      rw [hSideWhole, hBad]
    rcases eo_ite_cases_of_ne_stuck condLeftFalse (Term.Boolean false)
        memIte hWholeNe with hLeftFalseTrue | hLeftFalseFalse
    · have hSideFalse : side = Term.Boolean false := by
        rw [hSideWhole]
        simp [whole, hLeftFalseTrue, eo_ite_true]
      exfalso
      rw [hSideFalse] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    · have hMemIteNe : memIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLeftFalseFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condMem rightIte rightFallbackIte
          hMemIteNe with hMemTrue | hMemFalse
      · have hRightIteNe : rightIte ≠ Term.Stuck := by
          intro hBad
          apply hMemIteNe
          simpa [memIte, hMemTrue, eo_ite_true] using hBad
        rcases eo_ite_cases_of_ne_stuck condRightFalse
            (Term.Boolean false) sameIte hRightIteNe with
          hRightFalseTrue | hRightFalseFalse
        · have hSideFalse : side = Term.Boolean false := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemTrue,
              eo_ite_true, rightIte, hRightFalseTrue]
          exfalso
          rw [hSideFalse] at hMemEq
          simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
        · have hSameIteNe : sameIte ≠ Term.Stuck := by
            intro hBad
            apply hRightIteNe
            simpa [rightIte, hRightFalseFalse, eo_ite_false] using hBad
          rcases eo_ite_cases_of_ne_stuck condSame left fallback
              hSameIteNe with hSameTrue | hSameFalse
          · have hSideLeft : side = left := by
              rw [hSideWhole]
              simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
                hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
                sameIte, hSameTrue]
            have hSameEq : left = right :=
              (eq_of_eo_eq_true left right
                (by simpa [condSame] using hSameTrue)).symm
            have hSideRight : side = right := by
              rw [hSideLeft, hSameEq]
            have hLeftResidual :=
              ihLeft.2 side hSTy hInterArgs.1 hSideLeft hMemEq
            have hRightResidual :=
              ihRight.2 side hSTy hInterArgs.2 hSideRight hMemEq
            refine ⟨hLeftResidual.1, ?_⟩
            intro q ss rv ss' qv hSEval hInterEval hTailEval hQEval
            rcases eval_re_inter_parts_consume_local M hM c1 c2 rv hInterTy
                hInterEval with
              ⟨rv1, rv2, _hC1Ty, _hC2Ty, hC1Eval, hC2Eval, hRv⟩
            subst rv
            have hTailEvalTy :
                __smtx_typeof_value
                    (__smtx_model_eval M
                      (__eo_to_smt (__str_membership_str side))) =
                  SmtType.Seq SmtType.Char :=
              calc
                __smtx_typeof_value
                    (__smtx_model_eval M
                      (__eo_to_smt (__str_membership_str side))) =
                  __smtx_typeof
                    (__eo_to_smt (__str_membership_str side)) :=
                    smt_model_eval_preserves_type_of_non_none M hM
                      (__eo_to_smt (__str_membership_str side)) (by
                        unfold term_has_non_none_type
                        rw [hLeftResidual.1]
                        simp)
                _ = SmtType.Seq SmtType.Char := hLeftResidual.1
            have hSeqValueTy :
                __smtx_typeof_value (SmtValue.Seq ss') =
                  SmtType.Seq SmtType.Char := by
              rw [← hTailEval]
              exact hTailEvalTy
            have hTailValid :
                native_string_valid (native_unpack_string ss') = true :=
              native_unpack_string_valid_of_typeof_seq_char hSeqValueTy
            let tailStr := native_unpack_string ss'
            let tailTerm :=
              Term.Apply (Term.UOp UserOp.str_to_re) (Term.String tailStr)
            have hTailTermEval :
                __smtx_model_eval M (__eo_to_smt tailTerm) =
                  SmtValue.RegLan (native_str_to_re tailStr) := by
              dsimp [tailTerm, tailStr]
              change __smtx_model_eval M
                  (SmtTerm.str_to_re
                    (SmtTerm.String (native_unpack_string ss'))) =
                SmtValue.RegLan
                  (native_str_to_re (native_unpack_string ss'))
              simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
               ]
            have hTailSelf :
                native_str_in_re tailStr (native_str_to_re tailStr) = true :=
              native_str_in_re_str_to_re_self_local tailStr hTailValid
            have hLeftTail :
                native_str_in_re (native_unpack_string ss)
                    (native_re_concat rv1 (native_str_to_re tailStr)) =
                  true := by
              have hEq :=
                hLeftResidual.2 tailTerm ss rv1 ss'
                  (native_str_to_re tailStr) hSEval hC1Eval hTailEval
                  hTailTermEval
              rw [hEq]
              exact hTailSelf
            have hRightTail :
                native_str_in_re (native_unpack_string ss)
                    (native_re_concat rv2 (native_str_to_re tailStr)) =
                  true := by
              have hEq :=
                hRightResidual.2 tailTerm ss rv2 ss'
                  (native_str_to_re tailStr) hSEval hC2Eval hTailEval
                  hTailTermEval
              rw [hEq]
              exact hTailSelf
            exact
              native_str_in_re_re_concat_inter_same_residual_local
                (native_unpack_string ss) tailStr rv1 rv2 qv hTailValid
                (hLeftResidual.2 q ss rv1 ss' qv hSEval hC1Eval
                  hTailEval hQEval)
                (hRightResidual.2 q ss rv2 ss' qv hSEval hC2Eval
                  hTailEval hQEval)
                hLeftTail hRightTail
          · have hSideFallback : side = fallback := by
              rw [hSideWhole]
              simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
                hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
                sameIte, hSameFalse]
            exact str_re_consume_residual_side_str_in_re_local M hM s inter
              side hSTy hInterTy hSideFallback hMemEq
      · have hRightFallbackIteNe : rightFallbackIte ≠ Term.Stuck := by
          intro hBad
          apply hMemIteNe
          simpa [memIte, hMemFalse, eo_ite_false] using hBad
        rcases eo_ite_cases_of_ne_stuck condRightFalse
            (Term.Boolean false) fallback hRightFallbackIteNe with
          hRightFalseTrue | hRightFalseFalse
        · have hSideFalse : side = Term.Boolean false := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemFalse,
              rightFallbackIte, hRightFalseTrue, eo_ite_true]
          exfalso
          rw [hSideFalse] at hMemEq
          simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
        · have hSideFallback : side = fallback := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemFalse,
              rightFallbackIte, hRightFalseFalse, eo_ite_false]
          exact str_re_consume_residual_side_str_in_re_local M hM s inter side
            hSTy hInterTy hSideFallback hMemEq

theorem str_re_consume_rec_str_concat_str_to_re_eq_true_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEq : __eo_eq s1 s3 = Term.Boolean true)
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s2 r fuel) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.UOp UserOp.str_to_re) s3))
        r)
      fuel := by
  have hS3Eq : s3 = s1 := eq_of_eo_eq_true s1 s3 hEq
  subst s3
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let head := Term.Apply (Term.UOp UserOp.str_to_re) s1
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) r
  have hEqRec :
      __str_re_consume_rec sConcat rConcat fuel =
        __str_re_consume_rec s2 r fuel := by
    simpa [sConcat, head, rConcat] using
      str_re_consume_rec_str_concat_str_to_re_eq_true_eq s1 s2 s1 r
        fuel hFuel hS3Ne hEq
  constructor
  · intro side hSTy hRTy hSide hFalse
    rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
        simpa [sConcat] using hSTy) with
      ⟨hS1Ty, hS2Ty⟩
    have hRConcatArgs :
        __smtx_typeof (__eo_to_smt head) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt head) (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt rConcat) =
            SmtType.RegLan by
          simpa [head, rConcat] using hRTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt head) (__eo_to_smt r)) hNN
    have hSideTail : side = __str_re_consume_rec s2 r fuel := by
      rw [hSide, hEqRec]
    have hTailFalse : __str_re_consume_rec s2 r fuel = Term.Boolean false := by
      rw [← hSideTail]
      exact hFalse
    exact
      str_re_consume_str_to_re_concat_no_prefix_of_tail_no_prefix_evals_local
        M hM s1 s2 r hS1Ty hS2Ty hRConcatArgs.2
        (fun ss rv hS2Eval hREval pre suf hAppend =>
          ih.1 (__str_re_consume_rec s2 r fuel) hS2Ty hRConcatArgs.2
            rfl hTailFalse ss rv hS2Eval hREval pre suf hAppend)
  · intro side hSTy hRTy hSide hMemEq
    rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
        simpa [sConcat] using hSTy) with
      ⟨hS1Ty, hS2Ty⟩
    have hRConcatArgs :
        __smtx_typeof (__eo_to_smt head) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt head) (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt rConcat) =
            SmtType.RegLan by
          simpa [head, rConcat] using hRTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt head) (__eo_to_smt r)) hNN
    have hSideTail : side = __str_re_consume_rec s2 r fuel := by
      rw [hSide, hEqRec]
    have hTailResidual :=
      ih.2 side hS2Ty hRConcatArgs.2 hSideTail hMemEq
    refine ⟨hTailResidual.1, ?_⟩
    exact
      str_re_consume_str_to_re_concat_residual_of_tail_residual_evals_local
        M hM s1 s2 r side hS1Ty hS2Ty hRConcatArgs.2
        hTailResidual.2

theorem str_re_consume_rec_str_concat_re_allchar_len_one_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen : __eo_is_eq (__eo_len s1) (Term.Numeral 1) =
      Term.Boolean true)
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s2 r fuel) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.UOp UserOp.re_allchar))
        r)
      fuel := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let allchar := Term.UOp UserOp.re_allchar
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    allchar) r
  have hEqRec :
      __str_re_consume_rec sConcat rConcat fuel =
        __str_re_consume_rec s2 r fuel := by
    simpa [sConcat, allchar, rConcat] using
      str_re_consume_rec_str_concat_re_allchar_len_one_eq s1 s2 r fuel
        hFuel hLen
  constructor
  · intro side hSTy hRTy hSide hFalse
    rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
        simpa [sConcat] using hSTy) with
      ⟨hS1Ty, hS2Ty⟩
    have hRConcatArgs :
        __smtx_typeof (__eo_to_smt allchar) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt allchar) (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt rConcat) =
            SmtType.RegLan by
          simpa [allchar, rConcat] using hRTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt allchar) (__eo_to_smt r))
        hNN
    have hSideTail : side = __str_re_consume_rec s2 r fuel := by
      rw [hSide, hEqRec]
    have hTailFalse : __str_re_consume_rec s2 r fuel = Term.Boolean false := by
      rw [← hSideTail]
      exact hFalse
    exact
      str_re_consume_allchar_concat_no_prefix_of_tail_no_prefix_evals_local
        M hM s1 s2 r hS1Ty hS2Ty hRConcatArgs.2 hLen
        (fun ss rv hS2Eval hREval pre suf hAppend =>
          ih.1 (__str_re_consume_rec s2 r fuel) hS2Ty hRConcatArgs.2
            rfl hTailFalse ss rv hS2Eval hREval pre suf hAppend)
  · intro side hSTy hRTy hSide hMemEq
    rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
        simpa [sConcat] using hSTy) with
      ⟨hS1Ty, hS2Ty⟩
    have hRConcatArgs :
        __smtx_typeof (__eo_to_smt allchar) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt allchar) (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt rConcat) =
            SmtType.RegLan by
          simpa [allchar, rConcat] using hRTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt allchar) (__eo_to_smt r))
        hNN
    have hSideTail : side = __str_re_consume_rec s2 r fuel := by
      rw [hSide, hEqRec]
    have hTailResidual :=
      ih.2 side hS2Ty hRConcatArgs.2 hSideTail hMemEq
    refine ⟨hTailResidual.1, ?_⟩
    exact
      str_re_consume_allchar_concat_residual_of_tail_residual_evals_local
        M hM s1 s2 r side hS1Ty hS2Ty hRConcatArgs.2 hLen
        hTailResidual.2

theorem str_re_consume_rec_str_concat_re_range_match_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
          (__eo_is_eq (__eo_len s5) (Term.Numeral 1))) =
        Term.Boolean true)
    (hMatch :
      __eo_requires (__eo_is_str s1) (Term.Boolean true)
          (__str_eval_str_in_re_rec
            (__str_flatten
              (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s1))
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        Term.Boolean true)
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s2 r fuel) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
        r)
      fuel := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let range := Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    range) r
  have hEqRec :
      __str_re_consume_rec sConcat rConcat fuel =
        __str_re_consume_rec s2 r fuel := by
    simpa [sConcat, range, rConcat] using
      str_re_consume_rec_str_concat_re_range_match_eq s1 s2 s3 s5 r
        fuel hFuel hLen hMatch
  constructor
  · intro side hSTy hRTy hSide hFalse
    rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
        simpa [sConcat] using hSTy) with
      ⟨hS1Ty, hS2Ty⟩
    have hRConcatArgs :
        __smtx_typeof (__eo_to_smt range) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt range) (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt rConcat) =
            SmtType.RegLan by
          simpa [range, rConcat] using hRTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt range) (__eo_to_smt r)) hNN
    have hRangeArgs :
        __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char ∧
          __smtx_typeof (__eo_to_smt s5) = SmtType.Seq SmtType.Char := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_range (__eo_to_smt s3) (__eo_to_smt s5)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt range) ≠ SmtType.None
        rw [hRConcatArgs.1]
        simp
      exact seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
        (typeof_re_range_eq (__eo_to_smt s3) (__eo_to_smt s5)) hNN
    have hSideTail : side = __str_re_consume_rec s2 r fuel := by
      rw [hSide, hEqRec]
    have hTailFalse : __str_re_consume_rec s2 r fuel = Term.Boolean false := by
      rw [← hSideTail]
      exact hFalse
    exact
      str_re_consume_range_concat_no_prefix_of_tail_no_prefix_evals_local
        M hM s1 s2 s3 s5 r hS1Ty hS2Ty hRangeArgs.1
        hRangeArgs.2 hRConcatArgs.2 hRConcatArgs.1 hLen hMatch
        (fun ss rv hS2Eval hREval pre suf hAppend =>
          ih.1 (__str_re_consume_rec s2 r fuel) hS2Ty hRConcatArgs.2
            rfl hTailFalse ss rv hS2Eval hREval pre suf hAppend)
  · intro side hSTy hRTy hSide hMemEq
    rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
        simpa [sConcat] using hSTy) with
      ⟨hS1Ty, hS2Ty⟩
    have hRConcatArgs :
        __smtx_typeof (__eo_to_smt range) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt range) (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt rConcat) =
            SmtType.RegLan by
          simpa [range, rConcat] using hRTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt range) (__eo_to_smt r)) hNN
    have hRangeArgs :
        __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char ∧
          __smtx_typeof (__eo_to_smt s5) = SmtType.Seq SmtType.Char := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_range (__eo_to_smt s3) (__eo_to_smt s5)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt range) ≠ SmtType.None
        rw [hRConcatArgs.1]
        simp
      exact seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
        (typeof_re_range_eq (__eo_to_smt s3) (__eo_to_smt s5)) hNN
    have hSideTail : side = __str_re_consume_rec s2 r fuel := by
      rw [hSide, hEqRec]
    have hTailResidual :=
      ih.2 side hS2Ty hRConcatArgs.2 hSideTail hMemEq
    refine ⟨hTailResidual.1, ?_⟩
    exact
      str_re_consume_range_concat_residual_of_tail_residual_evals_local
        M hM s1 s2 s3 s5 r side hS1Ty hS2Ty hRangeArgs.1
        hRangeArgs.2 hRConcatArgs.2 hRConcatArgs.1 hLen hMatch
        hTailResidual.2

theorem str_re_consume_rec_str_concat_str_to_re_len_mismatch_semantic
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEqFalse : __eo_eq s1 s3 = Term.Boolean false)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) =
        Term.Boolean true) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.UOp UserOp.str_to_re) s3))
        r)
      fuel := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let head := Term.Apply (Term.UOp UserOp.str_to_re) s3
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) r
  have hFalseEq :
      __str_re_consume_rec sConcat rConcat fuel = Term.Boolean false := by
    simpa [sConcat, head, rConcat] using
      str_re_consume_rec_str_concat_str_to_re_len_mismatch_eq s1 s2 s3
        r fuel hFuel hS3Ne hEqFalse hLen
  apply str_re_consume_rec_semantic_of_false_local M sConcat rConcat fuel
    hFalseEq
  intro hSTy hRTy ss rv hSEval hREval pre suf hAppend
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hSTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt head) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt head) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [show __smtx_typeof (__eo_to_smt rConcat) =
          SmtType.RegLan by
        simpa [head, rConcat] using hRTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt head) (__eo_to_smt r)) hNN
  have hS3Ty :
      __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char := by
    have hNN : term_has_non_none_type
        (SmtTerm.str_to_re (__eo_to_smt s3)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt head) ≠ SmtType.None
      rw [hRConcatArgs.1]
      simp
    exact seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
      (typeof_str_to_re_eq (__eo_to_smt s3)) hNN
  rcases eo_and_eq_true_local
      (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
      (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) hLen with
    ⟨hS1Len, hS3Len⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s1 hS1Ty
      hS1Len with
    ⟨c, hS1Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s3 hS3Ty
      hS3Len with
    ⟨d, hS3Eq⟩
  subst s1
  subst s3
  have hCharNe : c ≠ d := by
    intro hcd
    subst d
    simp [__eo_eq, native_teq] at hEqFalse
  exact
    str_re_consume_str_to_re_singleton_no_prefix_of_evals_local M hM
      s2 r c d hS2Ty hRConcatArgs.2 hCharNe ss rv hSEval hREval
      pre suf hAppend

theorem str_re_consume_rec_str_concat_re_range_mismatch_semantic
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
          (__eo_is_eq (__eo_len s5) (Term.Numeral 1))) =
        Term.Boolean true)
    (hMatch :
      __eo_requires (__eo_is_str s1) (Term.Boolean true)
          (__str_eval_str_in_re_rec
            (__str_flatten
              (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s1))
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        Term.Boolean false) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
        r)
      fuel := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let range := Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    range) r
  have hFalseEq :
      __str_re_consume_rec sConcat rConcat fuel = Term.Boolean false := by
    simpa [sConcat, range, rConcat] using
      str_re_consume_rec_str_concat_re_range_mismatch_eq s1 s2 s3 s5 r
        fuel hFuel hLen hMatch
  apply str_re_consume_rec_semantic_of_false_local M sConcat rConcat fuel
    hFalseEq
  intro hSTy hRTy ss rv hSEval hREval pre suf hAppend
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hSTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt range) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt range) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [show __smtx_typeof (__eo_to_smt rConcat) =
          SmtType.RegLan by
        simpa [range, rConcat] using hRTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt range) (__eo_to_smt r)) hNN
  have hRangeArgs :
      __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char ∧
        __smtx_typeof (__eo_to_smt s5) = SmtType.Seq SmtType.Char := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_range (__eo_to_smt s3) (__eo_to_smt s5)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt range) ≠ SmtType.None
      rw [hRConcatArgs.1]
      simp
    exact seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
      (typeof_re_range_eq (__eo_to_smt s3) (__eo_to_smt s5)) hNN
  rcases eo_and_eq_true_local
      (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
      (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
        (__eo_is_eq (__eo_len s5) (Term.Numeral 1))) hLen with
    ⟨hS1Len, hRangeLens⟩
  rcases eo_and_eq_true_local
      (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
      (__eo_is_eq (__eo_len s5) (Term.Numeral 1)) hRangeLens with
    ⟨hS3Len, hS5Len⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s1 hS1Ty
      hS1Len with
    ⟨c, hS1Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s3
      hRangeArgs.1 hS3Len with
    ⟨lo, hS3Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s5
      hRangeArgs.2 hS5Len with
    ⟨hi, hS5Eq⟩
  have hCValidString : native_string_valid [c] = true := by
    have hStringTy :
        __smtx_typeof (__eo_to_smt (Term.String [c])) =
          SmtType.Seq SmtType.Char := by
      simpa [hS1Eq] using hS1Ty
    exact native_string_valid_of_smtx_typeof_eo_string [c] hStringTy
  subst s1
  subst s3
  subst s5
  have hHeadFalse :
      native_str_in_re [c] (native_re_range [lo] [hi]) = false :=
    str_re_consume_range_head_native_eq_of_match_local M hM c lo hi false
      hCValidString (by simpa using hRConcatArgs.1) (by simpa using hMatch)
  exact
    str_re_consume_range_singleton_no_prefix_of_evals_local M hM s2 r c
      lo hi hS2Ty hRConcatArgs.2 hHeadFalse ss rv hSEval hREval pre suf
      hAppend

theorem str_re_consume_rec_str_concat_re_allchar_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s2 r fuel) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.UOp UserOp.re_allchar))
        r)
      fuel := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let allchar := Term.UOp UserOp.re_allchar
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    allchar) r
  let reduced := __str_re_consume_rec s2 r fuel
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
    sConcat) rConcat
  let cond := __eo_is_eq (__eo_len s1) (Term.Numeral 1)
  let whole := __eo_ite cond reduced fallback
  constructor
  · intro side hSTy hRTy hSide hFalse
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_7 fuel s1 s2 r hFuel]
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      have hSideStuck : side = Term.Stuck := by
        rw [hSideWhole, hBad]
      rw [hFalse] at hSideStuck
      cases hSideStuck
    rcases eo_ite_cases_of_ne_stuck cond reduced fallback hWholeNe with
      hLenTrue | hLenFalse
    · exact
        (str_re_consume_rec_str_concat_re_allchar_len_one_semantic_from_ih
          M hM s1 s2 r fuel hFuel
          (by simpa [cond] using hLenTrue) ih).1
          side hSTy hRTy hSide hFalse
    · exact
        (str_re_consume_rec_semantic_of_side_eq_str_in_re_local M hM
          sConcat rConcat fuel
          (by
            simpa [sConcat, allchar, rConcat] using
              str_re_consume_rec_str_concat_re_allchar_len_mismatch_eq
                s1 s2 r fuel hFuel (by simpa [cond] using hLenFalse))).1
          side hSTy hRTy hSide hFalse
  · intro side hSTy hRTy hSide hMemEq
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_7 fuel s1 s2 r hFuel]
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      apply hSideNe
      rw [hSideWhole, hBad]
    rcases eo_ite_cases_of_ne_stuck cond reduced fallback hWholeNe with
      hLenTrue | hLenFalse
    · exact
        (str_re_consume_rec_str_concat_re_allchar_len_one_semantic_from_ih
          M hM s1 s2 r fuel hFuel
          (by simpa [cond] using hLenTrue) ih).2
          side hSTy hRTy hSide hMemEq
    · exact
        (str_re_consume_rec_semantic_of_side_eq_str_in_re_local M hM
          sConcat rConcat fuel
          (by
            simpa [sConcat, allchar, rConcat] using
              str_re_consume_rec_str_concat_re_allchar_len_mismatch_eq
                s1 s2 r fuel hFuel (by simpa [cond] using hLenFalse))).2
          side hSTy hRTy hSide hMemEq

theorem str_re_consume_rec_str_concat_str_to_re_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s2 r fuel) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.UOp UserOp.str_to_re) s3))
        r)
      fuel := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let head := Term.Apply (Term.UOp UserOp.str_to_re) s3
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    head) r
  let reduced := __str_re_consume_rec s2 r fuel
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
    sConcat) rConcat
  let condEq := __eo_eq s1 s3
  let condLen := __eo_and
    (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
    (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
  let lenIte := __eo_ite condLen (Term.Boolean false) fallback
  let whole := __eo_ite condEq reduced lenIte
  constructor
  · intro side hSTy hRTy hSide hFalse
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_5 fuel s1 s2 s3 r hS3Ne
        hFuel]
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      have hSideStuck : side = Term.Stuck := by
        rw [hSideWhole, hBad]
      rw [hFalse] at hSideStuck
      cases hSideStuck
    rcases eo_ite_cases_of_ne_stuck condEq reduced lenIte hWholeNe with
      hEqTrue | hEqFalse
    · exact
        (str_re_consume_rec_str_concat_str_to_re_eq_true_semantic_from_ih
          M hM s1 s2 s3 r fuel hFuel hS3Ne
          (by simpa [condEq] using hEqTrue) ih).1
          side hSTy hRTy hSide hFalse
    · have hLenIteNe : lenIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hEqFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condLen (Term.Boolean false)
          fallback hLenIteNe with hLenTrue | hLenFalse
      · exact
          (str_re_consume_rec_str_concat_str_to_re_len_mismatch_semantic
            M hM s1 s2 s3 r fuel hFuel hS3Ne
            (by simpa [condEq] using hEqFalse)
            (by simpa [condLen] using hLenTrue)).1
            side hSTy hRTy hSide hFalse
      · exact
          (str_re_consume_rec_semantic_of_side_eq_str_in_re_local M hM
            sConcat rConcat fuel
            (by
              simpa [sConcat, head, rConcat] using
                str_re_consume_rec_str_concat_str_to_re_no_match_eq
                  s1 s2 s3 r fuel hFuel hS3Ne
                  (by simpa [condEq] using hEqFalse)
                  (by simpa [condLen] using hLenFalse))).1
            side hSTy hRTy hSide hFalse
  · intro side hSTy hRTy hSide hMemEq
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_5 fuel s1 s2 s3 r hS3Ne
        hFuel]
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      apply hSideNe
      rw [hSideWhole, hBad]
    rcases eo_ite_cases_of_ne_stuck condEq reduced lenIte hWholeNe with
      hEqTrue | hEqFalse
    · exact
        (str_re_consume_rec_str_concat_str_to_re_eq_true_semantic_from_ih
          M hM s1 s2 s3 r fuel hFuel hS3Ne
          (by simpa [condEq] using hEqTrue) ih).2
          side hSTy hRTy hSide hMemEq
    · have hLenIteNe : lenIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hEqFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condLen (Term.Boolean false)
          fallback hLenIteNe with hLenTrue | hLenFalse
      · exact
          (str_re_consume_rec_str_concat_str_to_re_len_mismatch_semantic
            M hM s1 s2 s3 r fuel hFuel hS3Ne
            (by simpa [condEq] using hEqFalse)
            (by simpa [condLen] using hLenTrue)).2
            side hSTy hRTy hSide hMemEq
      · exact
          (str_re_consume_rec_semantic_of_side_eq_str_in_re_local M hM
            sConcat rConcat fuel
            (by
              simpa [sConcat, head, rConcat] using
                str_re_consume_rec_str_concat_str_to_re_no_match_eq
                  s1 s2 s3 r fuel hFuel hS3Ne
                  (by simpa [condEq] using hEqFalse)
                  (by simpa [condLen] using hLenFalse))).2
            side hSTy hRTy hSide hMemEq

theorem str_re_consume_rec_str_concat_re_range_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s2 r fuel) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
        r)
      fuel := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let range := Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    range) r
  let reduced := __str_re_consume_rec s2 r fuel
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
    sConcat) rConcat
  let condLen := __eo_and
    (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
    (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
      (__eo_is_eq (__eo_len s5) (Term.Numeral 1)))
  let condMatch :=
    __eo_requires (__eo_is_str s1) (Term.Boolean true)
      (__str_eval_str_in_re_rec
        (__str_flatten
          (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s1))
        range)
  let matchIte := __eo_ite condMatch reduced (Term.Boolean false)
  let whole := __eo_ite condLen matchIte fallback
  constructor
  · intro side hSTy hRTy hSide hFalse
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r hFuel]
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      have hSideStuck : side = Term.Stuck := by
        rw [hSideWhole, hBad]
      rw [hFalse] at hSideStuck
      cases hSideStuck
    rcases eo_ite_cases_of_ne_stuck condLen matchIte fallback hWholeNe with
      hLenTrue | hLenFalse
    · have hMatchIteNe : matchIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLenTrue, eo_ite_true] using hBad
      rcases eo_ite_cases_of_ne_stuck condMatch reduced
          (Term.Boolean false) hMatchIteNe with hMatchTrue | hMatchFalse
      · exact
          (str_re_consume_rec_str_concat_re_range_match_semantic_from_ih
            M hM s1 s2 s3 s5 r fuel hFuel
            (by simpa [condLen] using hLenTrue)
            (by simpa [condMatch, range] using hMatchTrue) ih).1
            side hSTy hRTy hSide hFalse
      · exact
          (str_re_consume_rec_str_concat_re_range_mismatch_semantic
            M hM s1 s2 s3 s5 r fuel hFuel
            (by simpa [condLen] using hLenTrue)
            (by simpa [condMatch, range] using hMatchFalse)).1
            side hSTy hRTy hSide hFalse
    · exact
        (str_re_consume_rec_semantic_of_side_eq_str_in_re_local M hM
          sConcat rConcat fuel
          (by
            simpa [sConcat, range, rConcat] using
              str_re_consume_rec_str_concat_re_range_len_mismatch_eq
                s1 s2 s3 s5 r fuel hFuel
                (by simpa [condLen] using hLenFalse))).1
          side hSTy hRTy hSide hFalse
  · intro side hSTy hRTy hSide hMemEq
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r hFuel]
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      apply hSideNe
      rw [hSideWhole, hBad]
    rcases eo_ite_cases_of_ne_stuck condLen matchIte fallback hWholeNe with
      hLenTrue | hLenFalse
    · have hMatchIteNe : matchIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLenTrue, eo_ite_true] using hBad
      rcases eo_ite_cases_of_ne_stuck condMatch reduced
          (Term.Boolean false) hMatchIteNe with hMatchTrue | hMatchFalse
      · exact
          (str_re_consume_rec_str_concat_re_range_match_semantic_from_ih
            M hM s1 s2 s3 s5 r fuel hFuel
            (by simpa [condLen] using hLenTrue)
            (by simpa [condMatch, range] using hMatchTrue) ih).2
            side hSTy hRTy hSide hMemEq
      · exact
          (str_re_consume_rec_str_concat_re_range_mismatch_semantic
            M hM s1 s2 s3 s5 r fuel hFuel
            (by simpa [condLen] using hLenTrue)
            (by simpa [condMatch, range] using hMatchFalse)).2
            side hSTy hRTy hSide hMemEq
    · exact
        (str_re_consume_rec_semantic_of_side_eq_str_in_re_local M hM
          sConcat rConcat fuel
          (by
            simpa [sConcat, range, rConcat] using
              str_re_consume_rec_str_concat_re_range_len_mismatch_eq
                s1 s2 s3 s5 r fuel hFuel
                (by simpa [condLen] using hLenFalse))).2
          side hSTy hRTy hSide hMemEq

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r3 r2 fc fr : Term)
    (ihLeft :
      StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        r3
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
    (ihRight :
      StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        r2
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
    (ihResidual :
      StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
        (__str_membership_str
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr)))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2)
        fr) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.UOp UserOp.re_mult) r3))
        r2)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr) := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let fuelConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr
  let rStar := Term.Apply (Term.UOp UserOp.re_mult) r3
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) rStar) r2
  let left := __str_re_consume_rec sConcat r3 fuelConcat
  let right := __str_re_consume_rec sConcat r2 fuelConcat
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
    sConcat) rConcat
  let condLeftFalse := __eo_eq left (Term.Boolean false)
  let condMem :=
    __eo_eq (__str_membership_re left)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let condRightFalse := __eo_is_eq right (Term.Boolean false)
  let condSame := __eo_eq sConcat (__str_membership_str left)
  let residual := __str_re_consume_rec (__str_membership_str left) rConcat fr
  let sameIte := __eo_ite condSame fallback residual
  let rightFalseIte := __eo_ite condRightFalse sameIte fallback
  let memIte := __eo_ite condMem rightFalseIte fallback
  let whole := __eo_ite condLeftFalse right memIte
  constructor
  · intro side hSTy hRTy hSide hFalse ss rv hSEval hRConcatEval pre suf
      hAppend
    rcases eval_re_concat_parts_consume_local M hM rStar r2 rv
        (by simpa [rStar, rConcat] using hRTy)
        (by simpa [rStar, rConcat] using hRConcatEval) with
      ⟨starRv, rv2, hStarTy, hR2Ty, hStarEval, hR2Eval, hRv⟩
    subst rv
    have hR3Ty :
        __smtx_typeof (__eo_to_smt r3) = SmtType.RegLan :=
      RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan r3
        (by simpa [rStar] using hStarTy)
    rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
        (__eo_to_smt r3) hR3Ty with
      ⟨rv3, hR3Eval⟩
    have hStarNative :
        SmtValue.RegLan (native_re_mult rv3) = SmtValue.RegLan starRv := by
      change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt r3)) =
        SmtValue.RegLan starRv at hStarEval
      simpa [__smtx_model_eval, __smtx_model_eval_re_mult, hR3Eval] using
        hStarEval
    cases hStarNative
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr]
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      have hSideStuck : side = Term.Stuck := by
        rw [hSideWhole, hBad]
      rw [hFalse] at hSideStuck
      cases hSideStuck
    rcases eo_ite_cases_of_ne_stuck condLeftFalse right memIte hWholeNe with
      hLeftFalse | hLeftNotFalse
    · have hSideRight : side = right := by
        rw [hSideWhole]
        simp [whole, hLeftFalse, eo_ite_true]
      have hLeftEqFalse : left = Term.Boolean false :=
        (eq_of_eo_eq_true left (Term.Boolean false)
          (by simpa [condLeftFalse] using hLeftFalse)).symm
      have hRightFalse : right = Term.Boolean false := by
        rw [← hSideRight]
        exact hFalse
      exact
        native_str_in_re_re_mult_concat_no_prefix_local
          (native_unpack_string ss) rv3 rv2
          (fun splitPre splitSuf hSplit =>
            ihRight.1 right hSTy hR2Ty rfl hRightFalse ss rv2 hSEval
              hR2Eval splitPre splitSuf hSplit)
          (fun splitPre splitSuf hSplit =>
            native_str_in_re_re_concat_false_of_no_split_local splitPre rv3
              (native_re_concat (native_re_mult rv3) rv2)
              (fun head rest hHeadSplit =>
                ihLeft.1 left hSTy hR3Ty rfl hLeftEqFalse ss rv3
                  hSEval hR3Eval head (rest ++ splitSuf) (by
                    rw [← List.append_assoc, hHeadSplit, hSplit])))
          pre suf hAppend
    · have hMemIteNe : memIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLeftNotFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condMem rightFalseIte fallback
          hMemIteNe with hMemEps | hMemNotEps
      · have hRightFalseIteNe : rightFalseIte ≠ Term.Stuck := by
          intro hBad
          apply hMemIteNe
          simpa [memIte, hMemEps, eo_ite_true] using hBad
        rcases eo_ite_cases_of_ne_stuck condRightFalse sameIte fallback
            hRightFalseIteNe with hRightFalse | hRightNotFalse
        · have hSameIteNe : sameIte ≠ Term.Stuck := by
            intro hBad
            apply hRightFalseIteNe
            simpa [rightFalseIte, hRightFalse, eo_ite_true] using hBad
          rcases eo_ite_cases_of_ne_stuck condSame fallback residual
              hSameIteNe with hSame | hDifferent
          · have hSideFallback : side = fallback := by
              rw [hSideWhole]
              simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
                eo_ite_true, rightFalseIte, hRightFalse, sameIte, hSame,
                fallback]
            exfalso
            rw [hSideFallback] at hFalse
            simp [fallback] at hFalse
          · have hSideResidual : side = residual := by
              rw [hSideWhole]
              simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
                eo_ite_true, rightFalseIte, hRightFalse, sameIte, hDifferent,
                residual]
            have hResidualFalse : residual = Term.Boolean false := by
              rw [← hSideResidual]
              exact hFalse
            have hLeftMemEq :
                __str_membership_re left =
                  Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) :=
              (eq_of_eo_eq_true (__str_membership_re left)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
                (by simpa [condMem] using hMemEps)).symm
            have hLeftResidual :=
              ihLeft.2 left hSTy hR3Ty rfl (StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local hLeftMemEq)
            rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
                (__eo_to_smt (__str_membership_str left)) hLeftResidual.1 with
              ⟨ssTail, hTailEval⟩
            have hSEvalTy :
                __smtx_typeof_value
                    (__smtx_model_eval M (__eo_to_smt sConcat)) =
                  SmtType.Seq SmtType.Char := by
              calc
                __smtx_typeof_value
                    (__smtx_model_eval M (__eo_to_smt sConcat)) =
                  __smtx_typeof (__eo_to_smt sConcat) :=
                    smt_model_eval_preserves_type_of_non_none M hM
                      (__eo_to_smt sConcat) (by
                        unfold term_has_non_none_type
                        rw [hSTy]
                        simp)
                _ = SmtType.Seq SmtType.Char := hSTy
            have hSeqValueTy :
                __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
              change __smtx_typeof_value (SmtValue.Seq ss) =
                SmtType.Seq SmtType.Char
              rw [← hSEval]
              exact hSEvalTy
            have hXsValid :
                native_string_valid (native_unpack_string ss) = true :=
              native_unpack_string_valid_of_typeof_seq_char hSeqValueTy
            have hRightEqFalse : right = Term.Boolean false :=
              eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
                (by simpa [condRightFalse] using hRightFalse)
            exact
              native_str_in_re_re_mult_concat_no_prefix_local
                (native_unpack_string ss) rv3 rv2
                (fun splitPre splitSuf hSplit =>
                  ihRight.1 right hSTy hR2Ty rfl hRightEqFalse ss rv2
                    hSEval hR2Eval splitPre splitSuf hSplit)
                (native_str_in_re_re_concat_no_prefix_of_residual_suffix_local
                  (native_unpack_string ss) (native_unpack_string ssTail) rv3
                  (native_re_concat (native_re_mult rv3) rv2) hXsValid
                  (fun suf0 _hSufValid => by
                    let qTail :=
                      Term.Apply
                        (Term.Apply (Term.UOp UserOp.re_concat) rConcat)
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String suf0))
                    have hQTailEval :
                        __smtx_model_eval M (__eo_to_smt qTail) =
                          SmtValue.RegLan
                            (native_re_concat
                              (native_re_concat (native_re_mult rv3) rv2)
                              (native_str_to_re suf0)) := by
                      dsimp [qTail, rStar, rConcat]
                      change __smtx_model_eval M
                          (SmtTerm.re_concat
                            (SmtTerm.re_concat
                              (SmtTerm.re_mult (__eo_to_smt r3))
                              (__eo_to_smt r2))
                            (SmtTerm.str_to_re (SmtTerm.String suf0))) =
                        SmtValue.RegLan
                          (native_re_concat
                            (native_re_concat (native_re_mult rv3) rv2)
                            (native_str_to_re suf0))
                      simp [__smtx_model_eval, __smtx_model_eval_re_concat,
                        __smtx_model_eval_re_mult,
                        __smtx_model_eval_str_to_re, hR3Eval, hR2Eval,
                       ]
                    exact hLeftResidual.2 qTail ss rv3 ssTail
                      (native_re_concat
                        (native_re_concat (native_re_mult rv3) rv2)
                        (native_str_to_re suf0))
                      hSEval hR3Eval hTailEval hQTailEval)
                  (fun tailPre tailSuf hTailAppend =>
                    ihResidual.1 residual hLeftResidual.1 hRTy rfl
                      hResidualFalse ssTail
                      (native_re_concat (native_re_mult rv3) rv2) hTailEval
                      (by simpa [rStar, rConcat] using hRConcatEval)
                      tailPre tailSuf hTailAppend))
                pre suf hAppend
        · have hSideFallback : side = fallback := by
            rw [hSideWhole]
            simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
              eo_ite_true, rightFalseIte, hRightNotFalse, eo_ite_false,
              fallback]
          exfalso
          rw [hSideFallback] at hFalse
          simp [fallback] at hFalse
      · have hSideFallback : side = fallback := by
          rw [hSideWhole]
          simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemNotEps,
            eo_ite_false, fallback]
        exfalso
        rw [hSideFallback] at hFalse
        simp [fallback] at hFalse
  · intro side hSTy hRTy hSide hMemEq
    have hRConcatArgs :
        __smtx_typeof (__eo_to_smt rStar) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt rStar) (__eo_to_smt r2)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt rConcat) = SmtType.RegLan by
          simpa [rConcat] using hRTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt rStar) (__eo_to_smt r2)) hNN
    have hR3Ty :
        __smtx_typeof (__eo_to_smt r3) = SmtType.RegLan :=
      RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan r3
        (by simpa [rStar] using hRConcatArgs.1)
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr]
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      apply hSideNe
      rw [hSideWhole, hBad]
    rcases eo_ite_cases_of_ne_stuck condLeftFalse right memIte hWholeNe with
      hLeftFalse | hLeftNotFalse
    · have hSideRight : side = right := by
        rw [hSideWhole]
        simp [whole, hLeftFalse, eo_ite_true]
      have hLeftEqFalse : left = Term.Boolean false :=
        (eq_of_eo_eq_true left (Term.Boolean false)
          (by simpa [condLeftFalse] using hLeftFalse)).symm
      have hRightResidual :=
        ihRight.2 side hSTy hRConcatArgs.2 hSideRight hMemEq
      refine ⟨hRightResidual.1, ?_⟩
      intro q ss rv ss' qv hSEval hRConcatEval hTailEval hQEval
      rcases eval_re_concat_parts_consume_local M hM rStar r2 rv
          (by simpa [rStar, rConcat] using hRTy)
          (by simpa [rStar, rConcat] using hRConcatEval) with
        ⟨starRv, rv2, hStarTy, _hR2Ty, hStarEval, hR2Eval, hRv⟩
      subst rv
      rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
          (__eo_to_smt r3) hR3Ty with
        ⟨rv3, hR3Eval⟩
      have hStarNative :
          SmtValue.RegLan (native_re_mult rv3) = SmtValue.RegLan starRv := by
        change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt r3)) =
          SmtValue.RegLan starRv at hStarEval
        simpa [__smtx_model_eval, __smtx_model_eval_re_mult, hR3Eval] using
          hStarEval
      cases hStarNative
      have hNoNonemptyPrefix :
          ∀ splitPre splitSuf : native_String,
            splitPre ++ splitSuf = native_unpack_string ss ->
            splitPre ≠ [] ->
              native_str_in_re splitPre rv3 = false := by
        intro splitPre splitSuf hSplit _hNe
        exact ihLeft.1 left hSTy hR3Ty rfl hLeftEqFalse ss rv3 hSEval
          hR3Eval splitPre splitSuf hSplit
      calc
        native_str_in_re (native_unpack_string ss)
            (native_re_concat
              (native_re_concat (native_re_mult rv3) rv2) qv) =
          native_str_in_re (native_unpack_string ss)
            (native_re_concat (native_re_mult rv3)
              (native_re_concat rv2 qv)) := by
            rw [native_str_in_re_re_concat_assoc_consume_local]
        _ = native_str_in_re (native_unpack_string ss)
            (native_re_concat rv2 qv) :=
            native_str_in_re_re_mult_concat_eq_tail_of_no_prefix_local
              (native_unpack_string ss) rv3 (native_re_concat rv2 qv)
              hNoNonemptyPrefix
        _ = native_str_in_re (native_unpack_string ss') qv :=
            hRightResidual.2 q ss rv2 ss' qv hSEval hR2Eval hTailEval
              hQEval
    · have hMemIteNe : memIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLeftNotFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condMem rightFalseIte fallback
          hMemIteNe with hMemEps | hMemNotEps
      · have hRightFalseIteNe : rightFalseIte ≠ Term.Stuck := by
          intro hBad
          apply hMemIteNe
          simpa [memIte, hMemEps, eo_ite_true] using hBad
        rcases eo_ite_cases_of_ne_stuck condRightFalse sameIte fallback
            hRightFalseIteNe with hRightFalse | hRightNotFalse
        · have hSameIteNe : sameIte ≠ Term.Stuck := by
            intro hBad
            apply hRightFalseIteNe
            simpa [rightFalseIte, hRightFalse, eo_ite_true] using hBad
          rcases eo_ite_cases_of_ne_stuck condSame fallback residual
              hSameIteNe with hSame | hDifferent
          · have hSideFallback : side = fallback := by
              rw [hSideWhole]
              simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
                eo_ite_true, rightFalseIte, hRightFalse, sameIte, hSame,
                fallback]
            exact str_re_consume_residual_side_str_in_re_local M hM sConcat
              rConcat side hSTy hRTy hSideFallback hMemEq
          · have hSideResidual : side = residual := by
              rw [hSideWhole]
              simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
                eo_ite_true, rightFalseIte, hRightFalse, sameIte, hDifferent,
                residual]
            have hLeftMemEq :
                __str_membership_re left =
                  Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) :=
              (eq_of_eo_eq_true (__str_membership_re left)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
                (by simpa [condMem] using hMemEps)).symm
            have hLeftResidual :=
              ihLeft.2 left hSTy hR3Ty rfl (StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local hLeftMemEq)
            have hTailResidual :=
              ihResidual.2 side hLeftResidual.1 hRTy hSideResidual hMemEq
            refine ⟨hTailResidual.1, ?_⟩
            intro q ss rv ss' qv hSEval hRConcatEval hFinalTailEval hQEval
            rcases eval_re_concat_parts_consume_local M hM rStar r2 rv
                (by simpa [rStar, rConcat] using hRTy)
                (by simpa [rStar, rConcat] using hRConcatEval) with
              ⟨starRv, rv2, hStarTy, _hR2Ty, hStarEval, hR2Eval, hRv⟩
            subst rv
            rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
                (__eo_to_smt r3) hR3Ty with
              ⟨rv3, hR3Eval⟩
            have hStarNative :
                SmtValue.RegLan (native_re_mult rv3) =
                  SmtValue.RegLan starRv := by
              change __smtx_model_eval M
                  (SmtTerm.re_mult (__eo_to_smt r3)) =
                SmtValue.RegLan starRv at hStarEval
              simpa [__smtx_model_eval, __smtx_model_eval_re_mult, hR3Eval]
                using hStarEval
            cases hStarNative
            rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
                (__eo_to_smt (__str_membership_str left)) hLeftResidual.1 with
              ⟨ssTail, hLeftTailEval⟩
            have hRightEqFalse : right = Term.Boolean false :=
              eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
                (by simpa [condRightFalse] using hRightFalse)
            have hRightNoPrefix :
                ∀ splitPre splitSuf : native_String,
                  splitPre ++ splitSuf = native_unpack_string ss ->
                    native_str_in_re splitPre rv2 = false :=
              fun splitPre splitSuf hSplit =>
                ihRight.1 right hSTy hRConcatArgs.2 rfl hRightEqFalse ss rv2
                  hSEval hR2Eval splitPre splitSuf hSplit
            have hTailFalse :
                native_str_in_re (native_unpack_string ss)
                  (native_re_concat rv2 qv) = false :=
              native_str_in_re_re_concat_false_of_no_split_local
                (native_unpack_string ss) rv2 qv hRightNoPrefix
            let qTail :=
              Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat) rStar)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r2) q)
            have hQTailEval :
                __smtx_model_eval M (__eo_to_smt qTail) =
                  SmtValue.RegLan
                    (native_re_concat (native_re_mult rv3)
                      (native_re_concat rv2 qv)) := by
              dsimp [qTail, rStar]
              change __smtx_model_eval M
                  (SmtTerm.re_concat
                    (SmtTerm.re_mult (__eo_to_smt r3))
                    (SmtTerm.re_concat (__eo_to_smt r2) (__eo_to_smt q))) =
                SmtValue.RegLan
                  (native_re_concat (native_re_mult rv3)
                    (native_re_concat rv2 qv))
              simp [__smtx_model_eval, __smtx_model_eval_re_concat,
                __smtx_model_eval_re_mult, hR3Eval, hR2Eval, hQEval]
            have hResidualNative :
                native_str_in_re (native_unpack_string ss)
                    (native_re_concat rv3
                      (native_re_concat (native_re_mult rv3)
                        (native_re_concat rv2 qv))) =
                  native_str_in_re (native_unpack_string ssTail)
                    (native_re_concat (native_re_mult rv3)
                      (native_re_concat rv2 qv)) :=
              hLeftResidual.2 qTail ss rv3 ssTail
                (native_re_concat (native_re_mult rv3)
                  (native_re_concat rv2 qv))
                hSEval hR3Eval hLeftTailEval hQTailEval
            calc
              native_str_in_re (native_unpack_string ss)
                  (native_re_concat
                    (native_re_concat (native_re_mult rv3) rv2) qv) =
                native_str_in_re (native_unpack_string ss)
                  (native_re_concat (native_re_mult rv3)
                    (native_re_concat rv2 qv)) := by
                  rw [native_str_in_re_re_concat_assoc_consume_local]
              _ = native_str_in_re (native_unpack_string ssTail)
                  (native_re_concat (native_re_mult rv3)
                    (native_re_concat rv2 qv)) :=
                  native_str_in_re_re_mult_concat_residual_eq_local
                    (native_unpack_string ss) (native_unpack_string ssTail)
                    rv3 (native_re_concat rv2 qv) hTailFalse
                    hResidualNative
              _ = native_str_in_re (native_unpack_string ssTail)
                  (native_re_concat
                    (native_re_concat (native_re_mult rv3) rv2) qv) := by
                  rw [native_str_in_re_re_concat_assoc_consume_local]
              _ = native_str_in_re (native_unpack_string ss') qv :=
                  hTailResidual.2 q ssTail
                    (native_re_concat (native_re_mult rv3) rv2) ss' qv
                    hLeftTailEval
                    (by simpa [rStar, rConcat] using hRConcatEval)
                    hFinalTailEval hQEval
        · have hSideFallback : side = fallback := by
            rw [hSideWhole]
            simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
              eo_ite_true, rightFalseIte, hRightNotFalse, eo_ite_false,
              fallback]
          exact str_re_consume_residual_side_str_in_re_local M hM sConcat
            rConcat side hSTy hRTy hSideFallback hMemEq
      · have hSideFallback : side = fallback := by
          rw [hSideWhole]
          simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemNotEps,
            eo_ite_false, fallback]
        exact str_re_consume_residual_side_str_in_re_local M hM sConcat rConcat
          side hSTy hRTy hSideFallback hMemEq

theorem str_re_consume_rec_str_concat_re_concat_semantic_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r1 r2 fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hR1Empty :
      r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    (hR1StrToRe :
      ∀ s3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) s3)
    (hR1Range :
      ∀ s3 s5 : Term,
        r1 ≠ Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
    (hR1Allchar : r1 ≠ Term.UOp UserOp.re_allchar)
    (hFuelMult :
      ∀ r3 fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        r1 = Term.Apply (Term.UOp UserOp.re_mult) r3 ->
        False)
    (hR1Mult :
      ∀ r3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.re_mult) r3)
    (ihLeft :
      StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        r1 fuel)
    (ihResidual :
      StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
        (__str_membership_str
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r1 fuel))
        r2 fuel) :
    StrInReConsumeInternal.str_re_consume_rec_semantic_motive M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
      fuel := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2
  let left := __str_re_consume_rec sConcat r1 fuel
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
    sConcat) rConcat
  let condLeftFalse := __eo_is_eq left (Term.Boolean false)
  let condMem :=
    __eo_is_eq (__str_membership_re left)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let residual := __str_re_consume_rec (__str_membership_str left) r2 fuel
  let memIte := __eo_ite condMem residual fallback
  let whole := __eo_ite condLeftFalse (Term.Boolean false) memIte
  constructor
  · intro side hSTy hRTy hSide hFalse ss rv hSEval hRConcatEval pre suf
      hAppend
    rcases eval_re_concat_parts_consume_local M hM r1 r2 rv
        (by simpa [rConcat] using hRTy)
        (by simpa [rConcat] using hRConcatEval) with
      ⟨rv1, rv2, hR1Ty, hR2Ty, hR1Eval, hR2Eval, hRv⟩
    subst rv
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_10 fuel s1 s2 r1 r2
        hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel
        hFuelMult]
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      have hSideStuck : side = Term.Stuck := by
        rw [hSideWhole, hBad]
      rw [hFalse] at hSideStuck
      cases hSideStuck
    rcases eo_ite_cases_of_ne_stuck condLeftFalse (Term.Boolean false)
        memIte hWholeNe with hLeftFalse | hLeftNotFalse
    · have hLeftEqFalse : left = Term.Boolean false :=
        eq_of_eo_is_eq_true_consume_local left (Term.Boolean false)
          (by simpa [condLeftFalse] using hLeftFalse)
      exact
        native_str_in_re_re_concat_false_of_no_split_local pre rv1 rv2
          (fun splitPre splitSuf hSplit =>
            ihLeft.1 left hSTy hR1Ty rfl hLeftEqFalse ss rv1 hSEval
              hR1Eval splitPre (splitSuf ++ suf) (by
                rw [← List.append_assoc, hSplit, hAppend]))
    · have hMemIteNe : memIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLeftNotFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condMem residual fallback hMemIteNe with
        hMemEps | hMemNotEps
      · have hSideResidual : side = residual := by
          rw [hSideWhole]
          simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
            eo_ite_true, residual]
        have hResidualFalse : residual = Term.Boolean false := by
          rw [← hSideResidual]
          exact hFalse
        have hLeftMemEq :
            __str_membership_re left =
              Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) :=
          eq_of_eo_is_eq_true_consume_local (__str_membership_re left)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
            (by simpa [left, condMem] using hMemEps)
        have hLeftResidual :=
          ihLeft.2 left hSTy hR1Ty rfl (StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local hLeftMemEq)
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
            (__eo_to_smt (__str_membership_str left)) hLeftResidual.1 with
          ⟨ssTail, hTailEval⟩
        have hSEvalTy :
            __smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt sConcat)) =
              SmtType.Seq SmtType.Char := by
          calc
            __smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt sConcat)) =
              __smtx_typeof (__eo_to_smt sConcat) :=
                smt_model_eval_preserves_type_of_non_none M hM
                  (__eo_to_smt sConcat) (by
                    unfold term_has_non_none_type
                    rw [hSTy]
                    simp)
            _ = SmtType.Seq SmtType.Char := hSTy
        have hSeqValueTy :
            __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
          change __smtx_typeof_value (SmtValue.Seq ss) =
            SmtType.Seq SmtType.Char
          rw [← hSEval]
          exact hSEvalTy
        have hXsValid :
            native_string_valid (native_unpack_string ss) = true :=
          native_unpack_string_valid_of_typeof_seq_char hSeqValueTy
        exact
          native_str_in_re_re_concat_no_prefix_of_residual_suffix_local
            (native_unpack_string ss) (native_unpack_string ssTail) rv1 rv2
            hXsValid
            (fun suf0 _hSufValid => by
              let qTerm :=
                Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r2)
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String suf0))
              have hQEval :
                  __smtx_model_eval M (__eo_to_smt qTerm) =
                    SmtValue.RegLan
                      (native_re_concat rv2 (native_str_to_re suf0)) := by
                dsimp [qTerm]
                change __smtx_model_eval M
                    (SmtTerm.re_concat (__eo_to_smt r2)
                      (SmtTerm.str_to_re (SmtTerm.String suf0))) =
                  SmtValue.RegLan
                    (native_re_concat rv2 (native_str_to_re suf0))
                simp [__smtx_model_eval, __smtx_model_eval_re_concat,
                  __smtx_model_eval_str_to_re, hR2Eval,
                 ]
              exact hLeftResidual.2 qTerm ss rv1 ssTail
                (native_re_concat rv2 (native_str_to_re suf0)) hSEval
                hR1Eval hTailEval hQEval)
            (fun tailPre tailSuf hTailAppend =>
              ihResidual.1 residual hLeftResidual.1 hR2Ty rfl
                hResidualFalse ssTail rv2 hTailEval hR2Eval tailPre
                tailSuf hTailAppend)
            pre suf hAppend
      · have hSideFallback : side = fallback := by
          rw [hSideWhole]
          simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemNotEps,
            eo_ite_false, fallback]
        exfalso
        rw [hSideFallback] at hFalse
        simp [fallback] at hFalse
  · intro side hSTy hRTy hSide hMemEq
    have hRConcatArgs :
        __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt r1) (__eo_to_smt r2)) := by
        unfold term_has_non_none_type
        change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
        rw [show __smtx_typeof (__eo_to_smt rConcat) = SmtType.RegLan by
          simpa [rConcat] using hRTy]
        simp
      exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
        (typeof_re_concat_eq (__eo_to_smt r1) (__eo_to_smt r2)) hNN
    have hSideWhole : side = whole := by
      rw [hSide, __str_re_consume_rec.eq_10 fuel s1 s2 r1 r2
        hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel
        hFuelMult]
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    have hWholeNe : whole ≠ Term.Stuck := by
      intro hBad
      apply hSideNe
      rw [hSideWhole, hBad]
    rcases eo_ite_cases_of_ne_stuck condLeftFalse (Term.Boolean false)
        memIte hWholeNe with hLeftFalse | hLeftNotFalse
    · have hSideFalse : side = Term.Boolean false := by
        rw [hSideWhole]
        simp [whole, hLeftFalse, eo_ite_true]
      exfalso
      rw [hSideFalse] at hMemEq
      simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    · have hMemIteNe : memIte ≠ Term.Stuck := by
        intro hBad
        apply hWholeNe
        simpa [whole, hLeftNotFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condMem residual fallback hMemIteNe with
        hMemEps | hMemNotEps
      · have hSideResidual : side = residual := by
          rw [hSideWhole]
          simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
            eo_ite_true, residual]
        have hLeftMemEq :
            __str_membership_re left =
              Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) :=
          eq_of_eo_is_eq_true_consume_local (__str_membership_re left)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
            (by simpa [left, condMem] using hMemEps)
        have hLeftResidual :=
          ihLeft.2 left hSTy hRConcatArgs.1 rfl (StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local hLeftMemEq)
        have hTailResidual :=
          ihResidual.2 side hLeftResidual.1 hRConcatArgs.2 hSideResidual
            hMemEq
        refine ⟨hTailResidual.1, ?_⟩
        intro q ss rv ss' qv hSEval hRConcatEval hFinalTailEval hQEval
        rcases eval_re_concat_parts_consume_local M hM r1 r2 rv
            (by simpa [rConcat] using hRTy)
            (by simpa [rConcat] using hRConcatEval) with
          ⟨rv1, rv2, _hR1Ty, _hR2Ty, hR1Eval, hR2Eval, hRv⟩
        subst rv
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
            (__eo_to_smt (__str_membership_str left)) hLeftResidual.1 with
          ⟨ssLeft, hLeftTailEval⟩
        let qConcat :=
          Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r2) q
        have hQConcatEval :
            __smtx_model_eval M (__eo_to_smt qConcat) =
              SmtValue.RegLan (native_re_concat rv2 qv) := by
          dsimp [qConcat]
          change __smtx_model_eval M
              (SmtTerm.re_concat (__eo_to_smt r2) (__eo_to_smt q)) =
            SmtValue.RegLan (native_re_concat rv2 qv)
          simp [__smtx_model_eval, __smtx_model_eval_re_concat, hR2Eval,
            hQEval]
        have hLeftNative :=
          hLeftResidual.2 qConcat ss rv1 ssLeft
            (native_re_concat rv2 qv) hSEval hR1Eval hLeftTailEval
            hQConcatEval
        have hTailNative :=
          hTailResidual.2 q ssLeft rv2 ss' qv hLeftTailEval hR2Eval
            hFinalTailEval hQEval
        calc
          native_str_in_re (native_unpack_string ss)
              (native_re_concat (native_re_concat rv1 rv2) qv) =
            native_str_in_re (native_unpack_string ss)
              (native_re_concat rv1 (native_re_concat rv2 qv)) := by
              rw [native_str_in_re_re_concat_assoc_consume_local]
          _ = native_str_in_re (native_unpack_string ssLeft)
              (native_re_concat rv2 qv) := hLeftNative
          _ = native_str_in_re (native_unpack_string ss') qv := hTailNative
      · have hSideFallback : side = fallback := by
          rw [hSideWhole]
          simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemNotEps,
            eo_ite_false, fallback]
        exact str_re_consume_residual_side_str_in_re_local M hM sConcat
          rConcat side hSTy hRTy hSideFallback hMemEq

theorem str_re_consume_residual_boolean_false_absurd_local
    (side : Term)
    (hSide : side = Term.Boolean false)
    (hMemEq :
      __str_membership_re side =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) :
    False := by
  subst side
  simp [__str_membership_re] at hMemEq

theorem str_re_consume_rec_model_rel_from_ih_of_types
    (M : SmtModel)
    (s r fuel : Term)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s r fuel)
    (hSTy :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hSideTy :
      __smtx_typeof (__eo_to_smt (__str_re_consume_rec s r fuel)) =
        SmtType.Bool)
    (hSideNe : __str_re_consume_rec s r fuel ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M
        (__eo_to_smt (__str_re_consume_rec s r fuel))) := by
  have hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          (__str_re_consume_rec s r fuel)) :=
    str_re_consume_eq_translation_of_types s r
      (__str_re_consume_rec s r fuel) hSTy hRTy hSideTy
  exact ih (__str_re_consume_rec s r fuel) hTrans rfl hSideNe

theorem StrInReConsumeInternal.str_re_consume_rec_type_of_translation_local
    (s r fuel : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          (__str_re_consume_rec s r fuel))) :
    __smtx_typeof (__eo_to_smt (__str_re_consume_rec s r fuel)) =
      SmtType.Bool :=
  str_re_consume_side_smt_type s r (__str_re_consume_rec s r fuel)
    hEqTrans

theorem str_re_consume_rec_native_false_of_ih_false
    (M : SmtModel) (hM : model_wf M)
    (s r fuel : Term)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s r fuel)
    (hFalse :
      __str_re_consume_rec s r fuel = Term.Boolean false)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          (Term.Boolean false))) :
    ∀ ss rv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      native_str_in_re (native_unpack_string ss) rv = false := by
  intro ss rv hSEval hREval
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt (Term.Boolean false))) :=
    ih (Term.Boolean false) hEqTrans hFalse.symm (by simp)
  rcases str_re_consume_input_eval M hM s r (Term.Boolean false)
      hEqTrans with ⟨ss0, rv0, hSEval0, hREval0, hStrInEval⟩
  have hSs : ss0 = ss := by
    rw [hSEval] at hSEval0
    cases hSEval0
    rfl
  have hRv : rv0 = rv := by
    rw [hREval] at hREval0
    cases hREval0
    rfl
  subst ss0
  subst rv0
  rw [hStrInEval] at hRel
  change RuleProofs.smt_value_rel
      (SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv))
      (__smtx_model_eval M (SmtTerm.Boolean false)) at hRel
  rw [__smtx_model_eval.eq_1] at hRel
  exact smt_value_rel_boolean_eq_consume_local hRel

theorem str_re_consume_rec_native_eq_of_ih_residual
    (M : SmtModel) (hM : model_wf M)
    (s r fuel s' r' : Term)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s r fuel)
    (hResidual :
      __str_re_consume_rec s r fuel =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r')
    (hResidualNe :
      Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r' ≠
        Term.Stuck)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r'))) :
    ∀ ss rv ss' rv',
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __smtx_model_eval M (__eo_to_smt s') = SmtValue.Seq ss' ->
      __smtx_model_eval M (__eo_to_smt r') = SmtValue.RegLan rv' ->
      native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string ss') rv' := by
  intro ss rv ss' rv' hSEval hREval hSEval' hREval'
  rcases str_re_consume_translation_facts s r
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r') hEqTrans with
    ⟨_hStrInTrans, hResidualTrans, hSTy, _hRTy, _hEqBool⟩
  rcases str_in_re_args_smt_types_of_has_translation s' r' hResidualTrans with
    ⟨hS'Ty, _hR'Ty⟩
  have hSsTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hSs'Ty :
      __smtx_typeof_value (SmtValue.Seq ss') =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval']
    simpa [hS'Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s') (by
        unfold term_has_non_none_type
        rw [hS'Ty]
        simp)
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r'))) :=
    ih (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r')
      hEqTrans hResidual.symm hResidualNe
  change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s') (__eo_to_smt r'))) at hRel
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval, hREval,
    hSEval', hREval'] at hRel
  rw [model_str_in_re_unpack_eq_string_of_value_type ss rv hSsTy,
    model_str_in_re_unpack_eq_string_of_value_type ss' rv' hSs'Ty] at hRel
  exact smt_value_rel_boolean_eq_consume_local hRel

theorem str_re_consume_tail_model_rel_from_ih
    (M : SmtModel)
    (s1 s2 head r2 fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat) head) r2)))
          side))
    (hSideRec : side = __str_re_consume_rec s2 r2 fuel)
    (hSideNe : side ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s2 r2 fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r2)))
      (__smtx_model_eval M
        (__eo_to_smt (__str_re_consume_rec s2 r2 fuel))) := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) r2
  rcases str_re_consume_translation_facts sConcat rConcat side (by
      simpa [sConcat, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hConcatTy, hRConcatTy, _hEqBool⟩
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hConcatTy) with
    ⟨_hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt head) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt head) (__eo_to_smt r2)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [hRConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt head) (__eo_to_smt r2)) hNN
  have hReducedSideTy :
      __smtx_typeof (__eo_to_smt (__str_re_consume_rec s2 r2 fuel)) =
        SmtType.Bool := by
    have hSideTy := str_re_consume_side_smt_type sConcat rConcat side (by
      simpa [sConcat, rConcat] using hEqTrans)
    rw [hSideRec] at hSideTy
    exact hSideTy
  have hReducedTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r2))
          (__str_re_consume_rec s2 r2 fuel)) :=
    str_re_consume_eq_translation_of_types s2 r2
      (__str_re_consume_rec s2 r2 fuel) hS2Ty hRConcatArgs.2
      hReducedSideTy
  have hReducedNe : __str_re_consume_rec s2 r2 fuel ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideRec, hBad]
  exact ih (__str_re_consume_rec s2 r2 fuel) hReducedTrans rfl
    hReducedNe

theorem str_re_consume_rec_re_concat_empty_left_model_rel_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
            r)
          fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s r fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let concat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) eps) r
  rcases str_re_consume_translation_facts s concat side (by
      simpa [eps, concat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hConcatTy, _hEqBool⟩
  have hConcatArgs :
      __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt eps) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt concat) ≠ SmtType.None
      rw [hConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt eps) (__eo_to_smt r)) hNN
  have hReducedSideTy :
      __smtx_typeof (__eo_to_smt (__str_re_consume_rec s r fuel)) =
        SmtType.Bool := by
    have hSideTy := str_re_consume_side_smt_type s concat side (by
      simpa [eps, concat] using hEqTrans)
    rw [hSide,
      str_re_consume_rec_re_concat_empty_left_eq s r fuel hS hFuel]
      at hSideTy
    exact hSideTy
  have hReducedTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          (__str_re_consume_rec s r fuel)) :=
    str_re_consume_eq_translation_of_types s r
      (__str_re_consume_rec s r fuel) hSTy hConcatArgs.2 hReducedSideTy
  have hReducedNe :
      __str_re_consume_rec s r fuel ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSide,
      str_re_consume_rec_re_concat_empty_left_eq s r fuel hS hFuel,
      hBad]
  have hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel))) :=
    ih (__str_re_consume_rec s r fuel) hReducedTrans rfl hReducedNe
  exact str_re_consume_rec_re_concat_empty_left_model_rel M hM s r fuel side
    (by simpa [eps, concat] using hEqTrans) hSide hS hFuel hReducedRel

theorem str_re_consume_union_re_none_model_rel_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) r)
                (Term.UOp UserOp.re_none))))
          side))
    (hSide :
      side =
        __str_re_consume_union s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union) r)
            (Term.UOp UserOp.re_none))
          fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s r fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) r)
              (Term.UOp UserOp.re_none)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let none := Term.UOp UserOp.re_none
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) none
  rcases str_re_consume_translation_facts s union side (by
      simpa [none, union] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hUnionTy, _hEqBool⟩
  have hUnionArgs :
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt none) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_union (__eo_to_smt r) (__eo_to_smt none)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt union) ≠ SmtType.None
      rw [hUnionTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
      (typeof_re_union_eq (__eo_to_smt r) (__eo_to_smt none)) hNN
  have hReducedSideTy :
      __smtx_typeof (__eo_to_smt (__str_re_consume_rec s r fuel)) =
        SmtType.Bool := by
    have hSideTy := str_re_consume_side_smt_type s union side (by
      simpa [none, union] using hEqTrans)
    rw [hSide, str_re_consume_union_re_none_eq s r fuel hS hFuel]
      at hSideTy
    exact hSideTy
  have hReducedTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          (__str_re_consume_rec s r fuel)) :=
    str_re_consume_eq_translation_of_types s r
      (__str_re_consume_rec s r fuel) hSTy hUnionArgs.1 hReducedSideTy
  have hReducedNe :
      __str_re_consume_rec s r fuel ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSide, str_re_consume_union_re_none_eq s r fuel hS hFuel,
      hBad]
  have hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel))) :=
    ih (__str_re_consume_rec s r fuel) hReducedTrans rfl hReducedNe
  exact str_re_consume_union_re_none_model_rel M hM s r fuel side
    (by simpa [none, union] using hEqTrans) hSide hS hFuel hReducedRel

theorem str_re_consume_union_model_rel_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) c1) c2)))
          side))
    (hSide :
      side =
        __str_re_consume_union s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
          fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_none)
    (ihLeft : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s c1 fuel)
    (ihRight : StrInReConsumeInternal.str_re_consume_union_model_rel_motive M s c2 fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) c1) c2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2
  let left := __str_re_consume_rec s c1 fuel
  let right := __str_re_consume_union s c2 fuel
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let condLeftFalse := __eo_is_eq left (Term.Boolean false)
  let condMem := __eo_eq (__str_membership_re left) eps
  let condRightFalse := __eo_is_eq right (Term.Boolean false)
  let condSame := __eo_eq left right
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
    union
  let sameIte := __eo_ite condSame left fallback
  let rightIte := __eo_ite condRightFalse left sameIte
  let memIte := __eo_ite condMem rightIte fallback
  let whole := __eo_ite condLeftFalse right memIte
  rcases str_re_consume_translation_facts s union side (by
      simpa [union] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hUnionTy, _hEqBool⟩
  have hUnionArgs :
      __smtx_typeof (__eo_to_smt c1) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt c2) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_union (__eo_to_smt c1) (__eo_to_smt c2)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt union) ≠ SmtType.None
      rw [hUnionTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
      (typeof_re_union_eq (__eo_to_smt c1) (__eo_to_smt c2)) hNN
  have hSideTy :
      __smtx_typeof (__eo_to_smt side) = SmtType.Bool :=
    str_re_consume_side_smt_type s union side (by
      simpa [union] using hEqTrans)
  have hSideWhole : side = whole := by
    rw [hSide, __str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS
      hFuel]
  have hWholeNe : whole ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideWhole, hBad]
  rcases eo_ite_cases_of_ne_stuck condLeftFalse right memIte hWholeNe with
    hLeftFalseTrue | hLeftFalseFalse
  · have hSideRight : side = right := by
      rw [hSideWhole]
      simp [whole, hLeftFalseTrue, eo_ite_true]
    have hLeftEqFalse : left = Term.Boolean false :=
      eq_of_eo_is_eq_true_consume_local left (Term.Boolean false)
        (by simpa [condLeftFalse] using hLeftFalseTrue)
    have hLeftTy :
        __smtx_typeof (__eo_to_smt left) = SmtType.Bool := by
      rw [hLeftEqFalse]
      change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
      rw [__smtx_typeof.eq_1]
    have hRightTy :
        __smtx_typeof (__eo_to_smt right) = SmtType.Bool := by
      simpa [hSideRight] using hSideTy
    have hLeftTrans :
        RuleProofs.eo_has_smt_translation
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1))
            left) :=
      str_re_consume_eq_translation_of_types s c1 left hSTy
        hUnionArgs.1 hLeftTy
    have hRightTrans :
        RuleProofs.eo_has_smt_translation
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2))
            right) :=
      str_re_consume_eq_translation_of_types s c2 right hSTy
        hUnionArgs.2 hRightTy
    have hLeftNe : left ≠ Term.Stuck := by
      rw [hLeftEqFalse]
      simp
    have hRightNe : right ≠ Term.Stuck := by
      intro hBad
      apply hSideNe
      rw [hSideRight, hBad]
    have hLeftRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
          (__smtx_model_eval M (__eo_to_smt left)) :=
      ihLeft left hLeftTrans rfl hLeftNe
    have hRightRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
          (__smtx_model_eval M (__eo_to_smt side)) := by
      simpa [hSideRight] using ihRight right hRightTrans rfl hRightNe
    have hLeftEval :
        __smtx_model_eval M (__eo_to_smt left) =
          SmtValue.Boolean false := by
      rw [hLeftEqFalse]
      change __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false
      rw [__smtx_model_eval.eq_1]
    exact str_re_consume_model_rel_of_re_union_left_false M hM s c1 c2
      left side (by simpa [union] using hEqTrans) hLeftRel hLeftEval
      hRightRel
  · have hMemIteNe : memIte ≠ Term.Stuck := by
      intro hBad
      apply hWholeNe
      simpa [whole, hLeftFalseFalse, eo_ite_false] using hBad
    rcases eo_ite_cases_of_ne_stuck condMem rightIte fallback
        hMemIteNe with hMemTrue | hMemFalse
    · have hRightIteNe : rightIte ≠ Term.Stuck := by
        intro hBad
        apply hMemIteNe
        simpa [memIte, hMemTrue, eo_ite_true] using hBad
      rcases eo_ite_cases_of_ne_stuck condRightFalse left sameIte
          hRightIteNe with hRightFalseTrue | hRightFalseFalse
      · have hSideLeft : side = left := by
          rw [hSideWhole]
          simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemTrue,
            eo_ite_true, rightIte, hRightFalseTrue]
        have hRightEqFalse : right = Term.Boolean false :=
          eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
            (by simpa [condRightFalse] using hRightFalseTrue)
        have hLeftTy :
            __smtx_typeof (__eo_to_smt left) = SmtType.Bool := by
          simpa [hSideLeft] using hSideTy
        have hRightTy :
            __smtx_typeof (__eo_to_smt right) = SmtType.Bool := by
          rw [hRightEqFalse]
          change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
          rw [__smtx_typeof.eq_1]
        have hLeftTrans :
            RuleProofs.eo_has_smt_translation
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) s) c1))
                left) :=
          str_re_consume_eq_translation_of_types s c1 left hSTy
            hUnionArgs.1 hLeftTy
        have hRightTrans :
            RuleProofs.eo_has_smt_translation
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) s) c2))
                right) :=
          str_re_consume_eq_translation_of_types s c2 right hSTy
            hUnionArgs.2 hRightTy
        have hLeftRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
              (__smtx_model_eval M (__eo_to_smt side)) := by
          have hLeftNe : left ≠ Term.Stuck := by
            intro hBad
            apply hSideNe
            rw [hSideLeft, hBad]
          simpa [hSideLeft] using ihLeft left hLeftTrans rfl hLeftNe
        have hRightRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
              (__smtx_model_eval M (__eo_to_smt right)) :=
          ihRight right hRightTrans rfl (by
            rw [hRightEqFalse]
            simp)
        have hRightEval :
            __smtx_model_eval M (__eo_to_smt right) =
              SmtValue.Boolean false := by
          rw [hRightEqFalse]
          change __smtx_model_eval M (SmtTerm.Boolean false) =
            SmtValue.Boolean false
          rw [__smtx_model_eval.eq_1]
        exact str_re_consume_model_rel_of_re_union_right_false M hM s c1
          c2 right side (by simpa [union] using hEqTrans) hLeftRel
          hRightRel hRightEval
      · have hSameIteNe : sameIte ≠ Term.Stuck := by
          intro hBad
          apply hRightIteNe
          simpa [rightIte, hRightFalseFalse, eo_ite_false] using hBad
        rcases eo_ite_cases_of_ne_stuck condSame left fallback
            hSameIteNe with hSameTrue | hSameFalse
        · have hSideLeft : side = left := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
              hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
              sameIte, hSameTrue]
          have hSameEq : left = right :=
            (eq_of_eo_eq_true left right
              (by simpa [condSame] using hSameTrue)).symm
          have hLeftTy :
              __smtx_typeof (__eo_to_smt left) = SmtType.Bool := by
            simpa [hSideLeft] using hSideTy
          have hRightTy :
              __smtx_typeof (__eo_to_smt right) = SmtType.Bool := by
            simpa [hSameEq] using hLeftTy
          have hLeftTrans :
              RuleProofs.eo_has_smt_translation
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.eq)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) s) c1))
                  left) :=
            str_re_consume_eq_translation_of_types s c1 left hSTy
              hUnionArgs.1 hLeftTy
          have hRightTrans :
              RuleProofs.eo_has_smt_translation
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.eq)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) s) c2))
                  right) :=
            str_re_consume_eq_translation_of_types s c2 right hSTy
              hUnionArgs.2 hRightTy
          have hLeftNe : left ≠ Term.Stuck := by
            intro hBad
            apply hSideNe
            rw [hSideLeft, hBad]
          have hRightNe : right ≠ Term.Stuck := by
            intro hBad
            apply hSideNe
            rw [hSideLeft, hSameEq, hBad]
          have hLeftRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
                (__smtx_model_eval M (__eo_to_smt left)) :=
            ihLeft left hLeftTrans rfl hLeftNe
          have hRightRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
                (__smtx_model_eval M (__eo_to_smt right)) :=
            ihRight right hRightTrans rfl hRightNe
          exact str_re_consume_model_rel_of_re_union_same_branches M hM s
            c1 c2 left right side (by simpa [union] using hEqTrans)
            hLeftRel hRightRel hSideLeft hSameEq
        · have hSideFallback : side = fallback := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
              hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
              sameIte, hSameFalse]
          exact str_re_consume_model_rel_of_side_eq_str_in_re M s union side
            (by simpa [fallback] using hSideFallback)
    · have hSideFallback : side = fallback := by
        rw [hSideWhole]
        simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemFalse]
      exact str_re_consume_model_rel_of_side_eq_str_in_re M s union side
        (by simpa [fallback] using hSideFallback)

theorem str_re_consume_inter_re_all_model_rel_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) r)
                (Term.UOp UserOp.re_all))))
          side))
    (hSide :
      side =
        __str_re_consume_inter s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter) r)
            (Term.UOp UserOp.re_all))
          fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s r fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) r)
              (Term.UOp UserOp.re_all)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let all := Term.UOp UserOp.re_all
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) all
  rcases str_re_consume_translation_facts s inter side (by
      simpa [all, inter] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hInterTy, _hEqBool⟩
  have hInterArgs :
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt all) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_inter (__eo_to_smt r) (__eo_to_smt all)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt inter) ≠ SmtType.None
      rw [hInterTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
      (typeof_re_inter_eq (__eo_to_smt r) (__eo_to_smt all)) hNN
  have hReducedSideTy :
      __smtx_typeof (__eo_to_smt (__str_re_consume_rec s r fuel)) =
        SmtType.Bool := by
    have hSideTy := str_re_consume_side_smt_type s inter side (by
      simpa [all, inter] using hEqTrans)
    rw [hSide, str_re_consume_inter_re_all_eq s r fuel hS hFuel]
      at hSideTy
    exact hSideTy
  have hReducedTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          (__str_re_consume_rec s r fuel)) :=
    str_re_consume_eq_translation_of_types s r
      (__str_re_consume_rec s r fuel) hSTy hInterArgs.1 hReducedSideTy
  have hReducedNe :
      __str_re_consume_rec s r fuel ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSide, str_re_consume_inter_re_all_eq s r fuel hS hFuel,
      hBad]
  have hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel))) :=
    ih (__str_re_consume_rec s r fuel) hReducedTrans rfl hReducedNe
  exact str_re_consume_inter_re_all_model_rel M hM s r fuel side
    (by simpa [all, inter] using hEqTrans) hSide hS hFuel hReducedRel

theorem str_re_consume_inter_model_rel_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)))
          side))
    (hSide :
      side =
        __str_re_consume_inter s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
          fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_all)
    (ihLeft : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s c1 fuel)
    (ihRight : StrInReConsumeInternal.str_re_consume_inter_model_rel_motive M s c2 fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) c1) c2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2
  let left := __str_re_consume_rec s c1 fuel
  let right := __str_re_consume_inter s c2 fuel
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let condLeftFalse := __eo_is_eq left (Term.Boolean false)
  let condMem := __eo_eq (__str_membership_re left) eps
  let condRightFalse := __eo_is_eq right (Term.Boolean false)
  let condSame := __eo_eq left right
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
    inter
  let sameIte := __eo_ite condSame left fallback
  let rightIte := __eo_ite condRightFalse (Term.Boolean false) sameIte
  let rightFallbackIte := __eo_ite condRightFalse (Term.Boolean false)
    fallback
  let memIte := __eo_ite condMem rightIte rightFallbackIte
  let whole := __eo_ite condLeftFalse (Term.Boolean false) memIte
  rcases str_re_consume_translation_facts s inter side (by
      simpa [inter] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hInterTy, _hEqBool⟩
  have hInterArgs :
      __smtx_typeof (__eo_to_smt c1) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt c2) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_inter (__eo_to_smt c1) (__eo_to_smt c2)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt inter) ≠ SmtType.None
      rw [hInterTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
      (typeof_re_inter_eq (__eo_to_smt c1) (__eo_to_smt c2)) hNN
  have hSideTy :
      __smtx_typeof (__eo_to_smt side) = SmtType.Bool :=
    str_re_consume_side_smt_type s inter side (by
      simpa [inter] using hEqTrans)
  have hSideWhole : side = whole := by
    rw [hSide, __str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS
      hFuel]
  have hWholeNe : whole ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideWhole, hBad]
  rcases eo_ite_cases_of_ne_stuck condLeftFalse (Term.Boolean false)
      memIte hWholeNe with hLeftFalseTrue | hLeftFalseFalse
  · have hSideFalse : side = Term.Boolean false := by
      rw [hSideWhole]
      simp [whole, hLeftFalseTrue, eo_ite_true]
    have hLeftEqFalse : left = Term.Boolean false :=
      eq_of_eo_is_eq_true_consume_local left (Term.Boolean false)
        (by simpa [condLeftFalse] using hLeftFalseTrue)
    have hLeftTy :
        __smtx_typeof (__eo_to_smt left) = SmtType.Bool := by
      rw [hLeftEqFalse]
      change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
      rw [__smtx_typeof.eq_1]
    have hLeftTrans :
        RuleProofs.eo_has_smt_translation
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1))
            left) :=
      str_re_consume_eq_translation_of_types s c1 left hSTy
        hInterArgs.1 hLeftTy
    have hLeftRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
          (__smtx_model_eval M (__eo_to_smt left)) :=
      ihLeft left hLeftTrans rfl (by
        rw [hLeftEqFalse]
        simp)
    have hLeftEval :
        __smtx_model_eval M (__eo_to_smt left) =
          SmtValue.Boolean false := by
      rw [hLeftEqFalse]
      change __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false
      rw [__smtx_model_eval.eq_1]
    exact str_re_consume_model_rel_of_re_inter_left_false M hM s c1 c2
      left side (by simpa [inter] using hEqTrans) hLeftRel hLeftEval
      hSideFalse
  · have hMemIteNe : memIte ≠ Term.Stuck := by
      intro hBad
      apply hWholeNe
      simpa [whole, hLeftFalseFalse, eo_ite_false] using hBad
    rcases eo_ite_cases_of_ne_stuck condMem rightIte rightFallbackIte
        hMemIteNe with hMemTrue | hMemFalse
    · have hRightIteNe : rightIte ≠ Term.Stuck := by
        intro hBad
        apply hMemIteNe
        simpa [memIte, hMemTrue, eo_ite_true] using hBad
      rcases eo_ite_cases_of_ne_stuck condRightFalse
          (Term.Boolean false) sameIte hRightIteNe with
        hRightFalseTrue | hRightFalseFalse
      · have hSideFalse : side = Term.Boolean false := by
          rw [hSideWhole]
          simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemTrue,
            eo_ite_true, rightIte, hRightFalseTrue]
        have hRightEqFalse : right = Term.Boolean false :=
          eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
            (by simpa [condRightFalse] using hRightFalseTrue)
        have hRightTy :
            __smtx_typeof (__eo_to_smt right) = SmtType.Bool := by
          rw [hRightEqFalse]
          change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
          rw [__smtx_typeof.eq_1]
        have hRightTrans :
            RuleProofs.eo_has_smt_translation
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) s) c2))
                right) :=
          str_re_consume_eq_translation_of_types s c2 right hSTy
            hInterArgs.2 hRightTy
        have hRightRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
              (__smtx_model_eval M (__eo_to_smt right)) :=
          ihRight right hRightTrans rfl (by
            rw [hRightEqFalse]
            simp)
        have hRightEval :
            __smtx_model_eval M (__eo_to_smt right) =
              SmtValue.Boolean false := by
          rw [hRightEqFalse]
          change __smtx_model_eval M (SmtTerm.Boolean false) =
            SmtValue.Boolean false
          rw [__smtx_model_eval.eq_1]
        exact str_re_consume_model_rel_of_re_inter_right_false M hM s c1
          c2 right side (by simpa [inter] using hEqTrans) hRightRel
          hRightEval hSideFalse
      · have hSameIteNe : sameIte ≠ Term.Stuck := by
          intro hBad
          apply hRightIteNe
          simpa [rightIte, hRightFalseFalse, eo_ite_false] using hBad
        rcases eo_ite_cases_of_ne_stuck condSame left fallback
            hSameIteNe with hSameTrue | hSameFalse
        · have hSideLeft : side = left := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
              hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
              sameIte, hSameTrue]
          have hSameEq : left = right :=
            (eq_of_eo_eq_true left right
              (by simpa [condSame] using hSameTrue)).symm
          have hLeftTy :
              __smtx_typeof (__eo_to_smt left) = SmtType.Bool := by
            simpa [hSideLeft] using hSideTy
          have hRightTy :
              __smtx_typeof (__eo_to_smt right) = SmtType.Bool := by
            simpa [hSameEq] using hLeftTy
          have hLeftTrans :
              RuleProofs.eo_has_smt_translation
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.eq)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) s) c1))
                  left) :=
            str_re_consume_eq_translation_of_types s c1 left hSTy
              hInterArgs.1 hLeftTy
          have hRightTrans :
              RuleProofs.eo_has_smt_translation
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.eq)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) s) c2))
                  right) :=
            str_re_consume_eq_translation_of_types s c2 right hSTy
              hInterArgs.2 hRightTy
          have hLeftNe : left ≠ Term.Stuck := by
            intro hBad
            apply hSideNe
            rw [hSideLeft, hBad]
          have hRightNe : right ≠ Term.Stuck := by
            intro hBad
            apply hSideNe
            rw [hSideLeft, hSameEq, hBad]
          have hLeftRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
                (__smtx_model_eval M (__eo_to_smt left)) :=
            ihLeft left hLeftTrans rfl hLeftNe
          have hRightRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
                (__smtx_model_eval M (__eo_to_smt right)) :=
            ihRight right hRightTrans rfl hRightNe
          exact str_re_consume_model_rel_of_re_inter_same_branches M hM s
            c1 c2 left right side (by simpa [inter] using hEqTrans)
            hLeftRel hRightRel hSideLeft hSameEq
        · have hSideFallback : side = fallback := by
            rw [hSideWhole]
            simp [whole, hLeftFalseFalse, eo_ite_false, memIte,
              hMemTrue, eo_ite_true, rightIte, hRightFalseFalse,
              sameIte, hSameFalse]
          exact str_re_consume_model_rel_of_side_eq_str_in_re M s inter side
            (by simpa [fallback] using hSideFallback)
    · have hRightFallbackIteNe : rightFallbackIte ≠ Term.Stuck := by
        intro hBad
        apply hMemIteNe
        simpa [memIte, hMemFalse, eo_ite_false] using hBad
      rcases eo_ite_cases_of_ne_stuck condRightFalse
          (Term.Boolean false) fallback hRightFallbackIteNe with
        hRightFalseTrue | hRightFalseFalse
      · have hSideFalse : side = Term.Boolean false := by
          rw [hSideWhole]
          simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemFalse,
            rightFallbackIte, hRightFalseTrue, eo_ite_true]
        have hRightEqFalse : right = Term.Boolean false :=
          eq_of_eo_is_eq_true_consume_local right (Term.Boolean false)
            (by simpa [condRightFalse] using hRightFalseTrue)
        have hRightTy :
            __smtx_typeof (__eo_to_smt right) = SmtType.Bool := by
          rw [hRightEqFalse]
          change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
          rw [__smtx_typeof.eq_1]
        have hRightTrans :
            RuleProofs.eo_has_smt_translation
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) s) c2))
                right) :=
          str_re_consume_eq_translation_of_types s c2 right hSTy
            hInterArgs.2 hRightTy
        have hRightRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
              (__smtx_model_eval M (__eo_to_smt right)) :=
          ihRight right hRightTrans rfl (by
            rw [hRightEqFalse]
            simp)
        have hRightEval :
            __smtx_model_eval M (__eo_to_smt right) =
              SmtValue.Boolean false := by
          rw [hRightEqFalse]
          change __smtx_model_eval M (SmtTerm.Boolean false) =
            SmtValue.Boolean false
          rw [__smtx_model_eval.eq_1]
        exact str_re_consume_model_rel_of_re_inter_right_false M hM s c1
          c2 right side (by simpa [inter] using hEqTrans) hRightRel
          hRightEval hSideFalse
      · have hSideFallback : side = fallback := by
          rw [hSideWhole]
          simp [whole, hLeftFalseFalse, eo_ite_false, memIte, hMemFalse,
            rightFallbackIte, hRightFalseFalse, eo_ite_false]
        exact str_re_consume_model_rel_of_side_eq_str_in_re M s inter side
          (by simpa [fallback] using hSideFallback)

theorem str_re_consume_rec_str_concat_re_allchar_model_rel_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r2 fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.UOp UserOp.re_allchar))
                r2)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.UOp UserOp.re_allchar))
            r2)
          fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s2 r2 fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let allchar := Term.UOp UserOp.re_allchar
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    allchar) r2
  let reduced := __str_re_consume_rec s2 r2 fuel
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
    sConcat) rConcat
  let cond := __eo_is_eq (__eo_len s1) (Term.Numeral 1)
  let whole := __eo_ite cond reduced fallback
  have hSideWhole : side = whole := by
    rw [hSide, __str_re_consume_rec.eq_7 fuel s1 s2 r2 hFuel]
  have hWholeNe : whole ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideWhole, hBad]
  rcases eo_ite_cases_of_ne_stuck cond reduced fallback hWholeNe with
    hLenTrue | hLenFalse
  · have hSideRec : side = reduced := by
      rw [hSideWhole]
      simp [whole, cond, reduced, fallback, hLenTrue, eo_ite_true]
    have hReducedRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2)
                r2)))
          (__smtx_model_eval M
            (__eo_to_smt (__str_re_consume_rec s2 r2 fuel))) :=
      str_re_consume_tail_model_rel_from_ih M s1 s2 allchar r2 fuel
        side (by simpa [sConcat, rConcat, allchar] using hEqTrans)
        (by simpa [reduced] using hSideRec) hSideNe ih
    exact str_re_consume_rec_str_concat_re_allchar_len_one_model_rel M hM
      s1 s2 r2 fuel side hEqTrans hSide hFuel
      (by simpa [cond] using hLenTrue) hReducedRel
  · exact str_re_consume_rec_str_concat_re_allchar_len_mismatch_model_rel
      M s1 s2 r2 fuel side hSide hFuel
      (by simpa [cond] using hLenFalse)

theorem str_re_consume_rec_str_concat_str_to_re_model_rel_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 r2 fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s3))
                r2)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s3))
            r2)
          fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s2 r2 fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s3))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let head := Term.Apply (Term.UOp UserOp.str_to_re) s3
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    head) r2
  let reduced := __str_re_consume_rec s2 r2 fuel
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
    sConcat) rConcat
  let condEq := __eo_eq s1 s3
  let condLen := __eo_and
    (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
    (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
  let lenIte := __eo_ite condLen (Term.Boolean false) fallback
  let whole := __eo_ite condEq reduced lenIte
  have hSideWhole : side = whole := by
    rw [hSide, __str_re_consume_rec.eq_5 fuel s1 s2 s3 r2 hS3Ne
      hFuel]
  have hWholeNe : whole ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideWhole, hBad]
  rcases eo_ite_cases_of_ne_stuck condEq reduced lenIte hWholeNe with
    hEqTrue | hEqFalse
  · have hSideRec : side = reduced := by
      rw [hSideWhole]
      simp [whole, condEq, reduced, lenIte, hEqTrue, eo_ite_true]
    have hReducedRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2)
                r2)))
          (__smtx_model_eval M
            (__eo_to_smt (__str_re_consume_rec s2 r2 fuel))) :=
      str_re_consume_tail_model_rel_from_ih M s1 s2 head r2 fuel side
        (by simpa [sConcat, head, rConcat] using hEqTrans)
        (by simpa [reduced] using hSideRec) hSideNe ih
    exact str_re_consume_rec_str_concat_str_to_re_eq_true_model_rel M hM
      s1 s2 s3 r2 fuel side hEqTrans hSide hFuel hS3Ne
      (by simpa [condEq] using hEqTrue) hReducedRel
  · have hLenIteNe : lenIte ≠ Term.Stuck := by
      intro hBad
      apply hWholeNe
      simpa [whole, hEqFalse, eo_ite_false] using hBad
    rcases eo_ite_cases_of_ne_stuck condLen (Term.Boolean false)
        fallback hLenIteNe with hLenTrue | hLenFalse
    · exact str_re_consume_rec_str_concat_str_to_re_len_mismatch_model_rel
        M hM s1 s2 s3 r2 fuel side hEqTrans hSide hFuel hS3Ne
        (by simpa [condEq] using hEqFalse)
        (by simpa [condLen] using hLenTrue)
    · exact str_re_consume_rec_str_concat_str_to_re_no_match_model_rel
        M s1 s2 s3 r2 fuel side hSide hFuel hS3Ne
        (by simpa [condEq] using hEqFalse)
        (by simpa [condLen] using hLenFalse)

theorem str_re_consume_rec_str_concat_re_range_model_rel_from_ih
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r2 fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
                r2)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
            r2)
          fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s2 r2 fuel) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let range := Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
    range) r2
  let reduced := __str_re_consume_rec s2 r2 fuel
  let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
    sConcat) rConcat
  let condLen := __eo_and
    (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
    (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
      (__eo_is_eq (__eo_len s5) (Term.Numeral 1)))
  let condMatch :=
    __eo_requires (__eo_is_str s1) (Term.Boolean true)
      (__str_eval_str_in_re_rec
        (__str_flatten
          (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s1))
        range)
  let matchIte := __eo_ite condMatch reduced (Term.Boolean false)
  let whole := __eo_ite condLen matchIte fallback
  have hSideWhole : side = whole := by
    rw [hSide, __str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r2 hFuel]
  have hWholeNe : whole ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideWhole, hBad]
  rcases eo_ite_cases_of_ne_stuck condLen matchIte fallback hWholeNe with
    hLenTrue | hLenFalse
  · have hMatchIteNe : matchIte ≠ Term.Stuck := by
      intro hBad
      apply hWholeNe
      simpa [whole, hLenTrue, eo_ite_true] using hBad
    rcases eo_ite_cases_of_ne_stuck condMatch reduced
        (Term.Boolean false) hMatchIteNe with hMatchTrue | hMatchFalse
    · have hSideRec : side = reduced := by
        rw [hSideWhole]
        simp [whole, hLenTrue, eo_ite_true, matchIte, hMatchTrue,
          reduced]
      have hReducedRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2)
                  r2)))
            (__smtx_model_eval M
              (__eo_to_smt (__str_re_consume_rec s2 r2 fuel))) :=
        str_re_consume_tail_model_rel_from_ih M s1 s2 range r2 fuel
          side (by simpa [sConcat, range, rConcat] using hEqTrans)
          (by simpa [reduced] using hSideRec) hSideNe ih
      exact str_re_consume_rec_str_concat_re_range_match_model_rel M hM
        s1 s2 s3 s5 r2 fuel side hEqTrans hSide hFuel
        (by simpa [condLen] using hLenTrue)
        (by simpa [condMatch, range] using hMatchTrue) hReducedRel
    · exact str_re_consume_rec_str_concat_re_range_mismatch_model_rel
        M hM s1 s2 s3 s5 r2 fuel side hEqTrans hSide hFuel
        (by simpa [condLen] using hLenTrue)
        (by simpa [condMatch, range] using hMatchFalse)
  · exact str_re_consume_rec_str_concat_re_range_len_mismatch_model_rel
      M s1 s2 s3 s5 r2 fuel side hSide hFuel
      (by simpa [condLen] using hLenFalse)

end RuleProofs
