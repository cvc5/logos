module

public import Cpc.Proofs.RuleSupport.StrInReConsume.Semantics
import all Cpc.Proofs.RuleSupport.StrInReConsume.Semantics

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck
    (s r fuel : Term)
    (h :
      __str_re_consume_rec s r fuel ≠ Term.Stuck) :
    s ≠ Term.Stuck := by
  intro hS
  subst s
  exact str_re_consume_rec_stuck_left_absurd r fuel
    (__str_re_consume_rec Term.Stuck r fuel) rfl h

theorem StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck
    (s r fuel : Term)
    (h :
      __str_re_consume_rec s r fuel ≠ Term.Stuck) :
    r ≠ Term.Stuck := by
  intro hR
  subst r
  have hS : s ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck s Term.Stuck fuel h
  exact str_re_consume_rec_stuck_right_absurd s fuel
    (__str_re_consume_rec s Term.Stuck fuel) hS rfl h

theorem StrInReConsumeInternal.str_re_consume_rec_fuel_ne_stuck_of_ne_stuck
    (s r fuel : Term)
    (h :
      __str_re_consume_rec s r fuel ≠ Term.Stuck) :
    fuel ≠ Term.Stuck := by
  intro hFuel
  subst fuel
  have hS : s ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck s r Term.Stuck h
  have hR : r ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck s r Term.Stuck h
  exact str_re_consume_rec_stuck_fuel_absurd s r
    (__str_re_consume_rec s r Term.Stuck) hS hR rfl h

theorem StrInReConsumeInternal.str_re_consume_rec_rebuild_of_ne_false
    (s r fuel side : Term)
    (hSide : side = __str_re_consume_rec s r fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false)
    (hReNe : __str_membership_re side ≠ Term.Stuck) :
    side =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str side))
        (__str_membership_re side) := by
  exact str_membership_re_eq_rebuild side (__str_membership_re side) rfl
    hReNe

theorem StrInReConsumeInternal.str_membership_types_of_bool_rebuild_local
    (side : Term)
    (hSideTy : __smtx_typeof (__eo_to_smt side) = SmtType.Bool)
    (hReNe : __str_membership_re side ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
        SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt (__str_membership_re side)) =
        SmtType.RegLan := by
  have hRebuild :
      side =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str side))
          (__str_membership_re side) :=
    str_membership_re_eq_rebuild side (__str_membership_re side) rfl
      hReNe
  have hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str side))
          (__str_membership_re side)) := by
    unfold RuleProofs.eo_has_bool_type
    simpa [← hRebuild] using hSideTy
  simpa [RuleProofs.ReUnfoldNegSupport.mkStrInRe] using
    RuleProofs.ReUnfoldNegSupport.str_in_re_args_of_bool_type
      (__str_membership_str side) (__str_membership_re side) hBool

theorem StrInReConsumeInternal.str_re_consume_rec_projection_types_of_bool_local
    (side : Term)
    (hSideTy : __smtx_typeof (__eo_to_smt side) = SmtType.Bool)
    (hMemReNe : __str_membership_re side ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
        SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt (__str_membership_re side)) =
        SmtType.RegLan :=
  StrInReConsumeInternal.str_membership_types_of_bool_rebuild_local side hSideTy hMemReNe

theorem StrInReConsumeInternal.smt_typeof_eo_ite_of_branches_local
    (c t e : Term) {T : SmtType}
    (hThenTy : __smtx_typeof (__eo_to_smt t) = T)
    (hElseTy : __smtx_typeof (__eo_to_smt e) = T)
    (hNe : __eo_ite c t e ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_ite c t e)) = T := by
  rcases eo_ite_cases_of_ne_stuck c t e hNe with hCond | hCond
  · simpa [hCond, eo_ite_true] using hThenTy
  · simpa [hCond, eo_ite_false] using hElseTy

theorem StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local
    (c t e : Term) {T : SmtType}
    (hThenTy : t ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt t) = T)
    (hElseTy : e ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt e) = T)
    (hNe : __eo_ite c t e ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_ite c t e)) = T := by
  rcases eo_ite_cases_of_ne_stuck c t e hNe with hCond | hCond
  · have hThenNe : t ≠ Term.Stuck := by
      intro hBad
      apply hNe
      rw [hCond, eo_ite_true, hBad]
    simpa [hCond, eo_ite_true] using hThenTy hThenNe
  · have hElseNe : e ≠ Term.Stuck := by
      intro hBad
      apply hNe
      rw [hCond, eo_ite_false, hBad]
    simpa [hCond, eo_ite_false] using hElseTy hElseNe

theorem StrInReConsumeInternal.smt_typeof_eo_requires_of_result_local
    (a b result : Term) {T : SmtType}
    (hResultTy : __smtx_typeof (__eo_to_smt result) = T)
    (hReqNe : __eo_requires a b result ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_requires a b result)) = T := by
  rw [eo_requires_result_eq_of_ne_stuck a b result hReqNe]
  exact hResultTy

theorem StrInReConsumeInternal.smt_typeof_boolean_false_local :
    __smtx_typeof (__eo_to_smt (Term.Boolean false)) = SmtType.Bool := by
  change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
  rw [__smtx_typeof.eq_1]

theorem StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local
    (s r : Term)
    (hSTy :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
      SmtType.Bool := by
  change __smtx_typeof
      (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtType.Bool
  rw [typeof_str_in_re_eq]
  simp [hSTy, hRTy, native_ite, native_Teq]

theorem StrInReConsumeInternal.re_concat_nil_eq_eps_of_is_list_nil_true_local
    (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
        Term.Boolean true) :
    nil = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
  cases nil <;> simp [__eo_is_list_nil] at hNil ⊢
  case Apply f x =>
    cases f <;> simp at hNil ⊢
    case UOp op =>
      cases op <;> simp at hNil ⊢
      case str_to_re =>
        cases x <;> simp at hNil ⊢
        case String s =>
          cases s <;> simp at hNil ⊢

theorem StrInReConsumeInternal.smt_typeof_re_concat_nil_of_is_list_nil_true_local
    (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
        Term.Boolean true) :
    __smtx_typeof (__eo_to_smt nil) = SmtType.RegLan := by
  have hEq := StrInReConsumeInternal.re_concat_nil_eq_eps_of_is_list_nil_true_local nil hNil
  subst nil
  change __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [__smtx_typeof, native_string_valid, native_ite, native_Teq]

theorem StrInReConsumeInternal.smt_typeof_get_nil_rec_re_concat_of_reglan_local
    (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true) :
    __smtx_typeof
        (__eo_to_smt (__eo_get_nil_rec (Term.UOp UserOp.re_concat) a)) =
      SmtType.RegLan := by
  have hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat)
          (__eo_get_nil_rec (Term.UOp UserOp.re_concat) a) =
        Term.Boolean true :=
    eo_is_list_nil_get_nil_rec_of_is_list_true
      (Term.UOp UserOp.re_concat) a hList
  exact StrInReConsumeInternal.smt_typeof_re_concat_nil_of_is_list_nil_true_local
    (__eo_get_nil_rec (Term.UOp UserOp.re_concat) a) hNil

theorem StrInReConsumeInternal.smt_typeof_list_rev_rec_re_concat_of_reglan_local
    (a acc : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.RegLan)
    (hRev : __eo_list_rev_rec a acc ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_list_rev_rec a acc)) =
      SmtType.RegLan := by
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hList
  | case2 a hA =>
      simp [__eo_list_rev_rec] at hRev
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.re_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.re_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y
          hList
      have hArgs :=
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_args_of_reglan x y
          haTy
      have hNewAccTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x)
                  acc)) =
            SmtType.RegLan :=
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_of_reglan x acc
          hArgs.1 hAccTy
      have hTailRev :
          __eo_list_rev_rec y
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) acc) ≠
            Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      simpa [__eo_list_rev_rec] using
        ih hTailList hArgs.2 hNewAccTy hTailRev
  | case4 nil acc hNil hAcc hNot =>
      simpa [__eo_list_rev_rec] using hAccTy

theorem StrInReConsumeInternal.smt_typeof_list_rev_re_concat_of_reglan_local
    (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hRev : __eo_list_rev (Term.UOp UserOp.re_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.re_concat) a)) =
      SmtType.RegLan := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.re_concat) a
  have hNilTy :
      __smtx_typeof (__eo_to_smt nil) = SmtType.RegLan := by
    simpa [nil] using
      StrInReConsumeInternal.smt_typeof_get_nil_rec_re_concat_of_reglan_local a hList
  have hRecNe :
      __eo_list_rev_rec a nil ≠ Term.Stuck := by
    simpa [nil] using
      eo_list_rev_rec_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.re_concat) a hRev
  rw [eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.re_concat) a hRev]
  exact StrInReConsumeInternal.smt_typeof_list_rev_rec_re_concat_of_reglan_local a nil hList haTy
    hNilTy hRecNe

theorem StrInReConsumeInternal.str_re_consume_sflat_type_facts_local
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSFlatNe :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro s)) ≠
        Term.Stuck) :
    let flat := __str_flatten (__str_nary_intro s)
    let sFlat := __eo_list_rev (Term.UOp UserOp.str_concat) flat
    __smtx_typeof (__eo_to_smt sFlat) = SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sFlat = Term.Boolean true ∧
      flat ≠ Term.Stuck ∧
      __eo_is_list (Term.UOp UserOp.str_concat) flat = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt flat) = SmtType.Seq SmtType.Char := by
  let flat := __str_flatten (__str_nary_intro s)
  let sFlat := __eo_list_rev (Term.UOp UserOp.str_concat) flat
  have hFlatNe : flat ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      flat hSFlatNe
  rcases str_re_consume_str_flatten_eval_rel M hM s r side hEqTrans
      (by simpa [flat] using hFlatNe) with
    ⟨_ss, _flatSs, _hSEval, _hFlatEval, hFlatTy, hFlatList,
      _hFlatRel⟩
  have hSFlatTy :
      __smtx_typeof (__eo_to_smt sFlat) = SmtType.Seq SmtType.Char := by
    simpa [sFlat, flat] using
      smt_typeof_list_rev_str_concat_of_seq flat SmtType.Char hFlatList
        hFlatTy (by simpa [sFlat] using hSFlatNe)
  have hSFlatList :
      __eo_is_list (Term.UOp UserOp.str_concat) sFlat =
        Term.Boolean true := by
    simpa [sFlat] using
      eo_list_rev_result_is_list_true_of_ne_stuck
        (Term.UOp UserOp.str_concat) flat hSFlatNe
  exact ⟨hSFlatTy, hSFlatList, hFlatNe, hFlatList, hFlatTy⟩

theorem StrInReConsumeInternal.re_split_str_to_re_parts_ne_stuck_local
    (parts tail : Term)
    (h : __re_split_str_to_re parts tail ≠ Term.Stuck) :
    parts ≠ Term.Stuck := by
  intro hParts
  subst parts
  simp [__re_split_str_to_re] at h

theorem StrInReConsumeInternal.re_split_str_to_re_tail_ne_stuck_local
    (parts tail : Term)
    (h : __re_split_str_to_re parts tail ≠ Term.Stuck) :
    tail ≠ Term.Stuck := by
  intro hTail
  subst tail
  cases parts <;> simp [__re_split_str_to_re] at h

theorem StrInReConsumeInternal.re_split_str_to_re_is_re_concat_list_true_local
    (parts tail : Term)
    (hParts :
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true)
    (hTail :
      __eo_is_list (Term.UOp UserOp.re_concat) tail =
        Term.Boolean true)
    (hSplit : __re_split_str_to_re parts tail ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.re_concat)
        (__re_split_str_to_re parts tail) =
      Term.Boolean true := by
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      simp [__eo_is_list] at hParts
  | case2 parts hPartsNe =>
      simp [__re_split_str_to_re] at hSplit
  | case3 c rest tail hTailNe ih =>
      have hRestParts :
          __eo_is_list (Term.UOp UserOp.str_concat) rest =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          c rest hParts
      have hRestSplitNe :
          __re_split_str_to_re rest tail ≠ Term.Stuck := by
        intro hBad
        apply hSplit
        calc
          __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
              tail =
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                (__re_split_str_to_re rest tail) := by
            simp [__re_split_str_to_re]
          _ = Term.Stuck := by
            rw [hBad]
            rfl
      have hRestList :
          __eo_is_list (Term.UOp UserOp.re_concat)
              (__re_split_str_to_re rest tail) =
            Term.Boolean true :=
        ih hRestParts hTail hRestSplitNe
      have hMkNe :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) ≠ Term.Stuck := by
        simpa [__re_split_str_to_re] using hSplit
      have hMkEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) c))
          (__re_split_str_to_re rest tail) hMkNe
      rw [show __re_split_str_to_re
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
            tail =
          __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) c))
            (__re_split_str_to_re rest tail) by
        simp [__re_split_str_to_re]]
      rw [hMkEq]
      exact
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.UOp UserOp.str_to_re) c)
          (__re_split_str_to_re rest tail) (by decide) hRestList
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      simpa [__re_split_str_to_re] using hTail

theorem StrInReConsumeInternal.re_split_str_to_re_ne_stuck_of_lists_local
    (parts tail : Term)
    (hParts :
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true)
    (hTail :
      __eo_is_list (Term.UOp UserOp.re_concat) tail =
        Term.Boolean true) :
    __re_split_str_to_re parts tail ≠ Term.Stuck := by
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      simp [__eo_is_list] at hParts
  | case2 parts hPartsNe =>
      simp [__eo_is_list] at hTail
  | case3 c rest tail hTailNe ih =>
      have hRestParts :
          __eo_is_list (Term.UOp UserOp.str_concat) rest =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          c rest hParts
      have hRestSplitNe :
          __re_split_str_to_re rest tail ≠ Term.Stuck :=
        ih hRestParts hTail
      have hConsNe :
          Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) ≠ Term.Stuck := by
        intro hBad
        simp at hBad
      intro hBad
      have hMkEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) := by
        have hMkNe :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                (__re_split_str_to_re rest tail) ≠ Term.Stuck := by
          intro hMkStuck
          cases hSplit : __re_split_str_to_re rest tail <;>
            simp [__eo_mk_apply, hSplit] at hMkStuck
          exact hRestSplitNe hSplit
        exact eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) c))
          (__re_split_str_to_re rest tail) hMkNe
      have hExpanded :
          __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
              tail =
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) := by
        simp [__re_split_str_to_re]
      rw [hExpanded, hMkEq] at hBad
      exact hConsNe hBad
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      have hTailNonStuck : tail ≠ Term.Stuck := by
        intro hBad
        subst tail
        simp [__eo_is_list] at hTail
      simpa [__re_split_str_to_re] using hTailNonStuck

def StrInReConsumeInternal.str_flattened_chunks_local : Term -> Prop
  | Term.Stuck => False
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c) rest =>
      __str_flatten
          (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) c) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
          (Term.String []) ∧
      StrInReConsumeInternal.str_flattened_chunks_local rest
  | _ => True

theorem StrInReConsumeInternal.str_flatten_singleton_intro_string_single_local
    (c : native_Char) :
    __str_flatten
        (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
          (Term.String [c])) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
        (Term.String []) := by
  have hsimpa := str_flatten_nary_intro_cons c []
  try simp [__str_nary_intro] at hsimpa ⊢
  exact hsimpa

theorem StrInReConsumeInternal.str_flattened_chunks_string_atom_chain_local :
    ∀ w : native_String,
      StrInReConsumeInternal.str_flattened_chunks_local
        (StrInReConsumeInternal.consume_atom_chain_term (w.map (fun ch => Term.String [ch]))
          (Term.String []))
  | [] => by
      simp [StrInReConsumeInternal.consume_atom_chain_term, StrInReConsumeInternal.str_flattened_chunks_local]
  | c :: cs => by
      rw [List.map_cons, StrInReConsumeInternal.consume_atom_chain_cons]
      exact ⟨StrInReConsumeInternal.str_flatten_singleton_intro_string_single_local c,
        StrInReConsumeInternal.str_flattened_chunks_string_atom_chain_local cs⟩

theorem StrInReConsumeInternal.str_flattened_chunks_string_flatten_local
    (w : native_String) :
    StrInReConsumeInternal.str_flattened_chunks_local
      (__str_flatten
        (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
          (Term.String w))) := by
  cases w with
  | nil =>
      rw [show __str_flatten
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
              (Term.String [])) =
          __str_flatten (__str_nary_intro (Term.String [])) by
            rfl]
      rw [str_flatten_nary_intro_empty]
      simp [StrInReConsumeInternal.str_flattened_chunks_local]
  | cons c cs =>
      rw [show __str_flatten
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
              (Term.String (c :: cs))) =
          StrInReConsumeInternal.consume_atom_chain_term
            ((c :: cs).map (fun ch => Term.String [ch])) (Term.String []) by
        rw [show __str_flatten
              (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
                (Term.String (c :: cs))) =
            __str_flatten (__str_nary_intro (Term.String (c :: cs))) by
              rfl]
        rw [str_flatten_nary_intro_cons,
          ← StrInReConsumeInternal.consume_atom_chain_string_atoms_eq_substrWord (c :: cs)]]
      exact StrInReConsumeInternal.str_flattened_chunks_string_atom_chain_local (c :: cs)

theorem StrInReConsumeInternal.re_split_str_to_re_ne_stuck_of_chunks_local
    (parts tail : Term)
    (hParts : StrInReConsumeInternal.str_flattened_chunks_local parts)
    (hTail : tail ≠ Term.Stuck) :
    __re_split_str_to_re parts tail ≠ Term.Stuck := by
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      cases hParts
  | case2 parts hPartsNe =>
      exact False.elim (hTail rfl)
  | case3 c rest tail hTailNe ih =>
      rcases hParts with ⟨_hHeadFlat, hRestChunks⟩
      let restSplit := __re_split_str_to_re rest tail
      have hRestSplitNe : restSplit ≠ Term.Stuck :=
        ih hRestChunks hTailNe
      have hMkNe :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit ≠ Term.Stuck := by
        cases hRest : restSplit <;> simp [__eo_mk_apply]
        exact False.elim (hRestSplitNe hRest)
      intro hBad
      exact hMkNe (by
        simpa [__re_split_str_to_re, restSplit] using hBad)
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      simpa [__re_split_str_to_re] using hTail

theorem StrInReConsumeInternal.re_split_str_to_re_string_empty_tail_local
    (tail : Term)
    (hTail : tail ≠ Term.Stuck) :
    __re_split_str_to_re (Term.String []) tail = tail := by
  cases tail <;> simp [__re_split_str_to_re] at hTail ⊢

theorem StrInReConsumeInternal.re_split_str_to_re_flatten_true_of_chunks_local
    (parts tail : Term)
    (hParts : StrInReConsumeInternal.str_flattened_chunks_local parts)
    (hTailNorm : __re_flatten (Term.Boolean true) tail = tail)
    (hSplit : __re_split_str_to_re parts tail ≠ Term.Stuck) :
    __re_flatten (Term.Boolean true) (__re_split_str_to_re parts tail) =
      __re_split_str_to_re parts tail := by
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      cases hParts
  | case2 parts hPartsNe =>
      simp [__re_split_str_to_re] at hSplit
  | case3 c rest tail hTailNe ih =>
      rcases hParts with ⟨hHeadFlat, hRestChunks⟩
      let restSplit := __re_split_str_to_re rest tail
      have hRestSplitNe : restSplit ≠ Term.Stuck := by
        intro hBad
        apply hSplit
        calc
          __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
              tail =
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                restSplit := by
            simp [__re_split_str_to_re, restSplit]
          _ = Term.Stuck := by
            rw [hBad]
            rfl
      have hRestNorm :
          __re_flatten (Term.Boolean true) restSplit = restSplit :=
        ih hRestChunks hTailNorm hRestSplitNe
      have hMkNe :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit ≠ Term.Stuck := by
        simpa [__re_split_str_to_re, restSplit] using hSplit
      have hMkEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) c))
          restSplit hMkNe
      have hSplitHead :
          __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c)
                (Term.String [])) restSplit =
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit := by
        rw [show __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c)
                (Term.String [])) restSplit =
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re (Term.String []) restSplit) by
          simp [__re_split_str_to_re]]
        rw [StrInReConsumeInternal.re_split_str_to_re_string_empty_tail_local restSplit
          hRestSplitNe]
      calc
        __re_flatten (Term.Boolean true)
            (__re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
              tail) =
            __re_flatten (Term.Boolean true)
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                restSplit) := by
              simp [__re_split_str_to_re, restSplit]
        _ =
            __re_flatten (Term.Boolean true)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                restSplit) := by
              rw [hMkEq]
        _ =
            __re_split_str_to_re
              (__str_flatten
                (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) c))
              (__re_flatten (Term.Boolean true) restSplit) := by
              simp [__re_flatten]
        _ =
            __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c)
                (Term.String [])) restSplit := by
              rw [hHeadFlat, hRestNorm]
        _ =
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit := hSplitHead
        _ =
            __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
              tail := by
              simp [__re_split_str_to_re, restSplit]
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      simpa [__re_split_str_to_re] using hTailNorm

theorem StrInReConsumeInternal.re_split_str_to_re_flatten_true_string_flatten_local
    (w : native_String) (tail : Term)
    (hTailNorm : __re_flatten (Term.Boolean true) tail = tail)
    (hSplit :
      __re_split_str_to_re
          (__str_flatten
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
              (Term.String w))) tail ≠
        Term.Stuck) :
    __re_flatten (Term.Boolean true)
        (__re_split_str_to_re
          (__str_flatten
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
              (Term.String w))) tail) =
      __re_split_str_to_re
        (__str_flatten
          (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
            (Term.String w))) tail := by
  exact StrInReConsumeInternal.re_split_str_to_re_flatten_true_of_chunks_local
    (__str_flatten
      (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
        (Term.String w))) tail
    (StrInReConsumeInternal.str_flattened_chunks_string_flatten_local w) hTailNorm hSplit

def StrInReConsumeInternal.re_action_frontier_true_local : Term -> Prop
  | Term.Stuck => False
  | Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) => True
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) tail =>
      __re_flatten (Term.Boolean false) head = head ∧
        __re_rev_comp head ≠ Term.Stuck ∧
        StrInReConsumeInternal.re_action_frontier_true_local tail
  | _ => False

theorem StrInReConsumeInternal.re_action_frontier_true_tail_local
    (head tail : Term)
    (hFrontier :
      StrInReConsumeInternal.re_action_frontier_true_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) tail)) :
    StrInReConsumeInternal.re_action_frontier_true_local tail :=
  hFrontier.2.2

theorem StrInReConsumeInternal.re_action_frontier_true_ne_stuck_local
    (t : Term)
    (hFrontier : StrInReConsumeInternal.re_action_frontier_true_local t) :
    t ≠ Term.Stuck := by
  cases t <;> simp [StrInReConsumeInternal.re_action_frontier_true_local] at hFrontier ⊢

theorem StrInReConsumeInternal.re_action_frontier_true_mk_concat_local
    (head tail : Term)
    (hHead : __re_flatten (Term.Boolean false) head = head)
    (hHeadComp : __re_rev_comp head ≠ Term.Stuck)
    (hTail : StrInReConsumeInternal.re_action_frontier_true_local tail)
    (hMk :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_concat) head)
          tail ≠ Term.Stuck) :
    StrInReConsumeInternal.re_action_frontier_true_local
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_concat) head)
        tail) := by
  let inner := __eo_mk_apply (Term.UOp UserOp.re_concat) head
  have hInnerNe : inner ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck inner tail
      (by simpa [inner] using hMk)
  have hInnerEq :
      inner = Term.Apply (Term.UOp UserOp.re_concat) head :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.re_concat) head hInnerNe
  have hMkEq :
      __eo_mk_apply inner tail =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) tail := by
    rw [eo_mk_apply_eq_apply_of_ne_stuck inner tail
      (by simpa [inner] using hMk), hInnerEq]
  change StrInReConsumeInternal.re_action_frontier_true_local (__eo_mk_apply inner tail)
  rw [hMkEq]
  exact ⟨hHead, hHeadComp, hTail⟩

theorem StrInReConsumeInternal.re_split_str_to_re_action_frontier_true_local
    (parts tail : Term)
    (hTail : StrInReConsumeInternal.re_action_frontier_true_local tail)
    (hSplit : __re_split_str_to_re parts tail ≠ Term.Stuck) :
    StrInReConsumeInternal.re_action_frontier_true_local (__re_split_str_to_re parts tail) := by
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      simp [__re_split_str_to_re] at hSplit
  | case2 parts hPartsNe =>
      simp [__re_split_str_to_re] at hSplit
  | case3 c rest tail hTailNe ih =>
      let restSplit := __re_split_str_to_re rest tail
      have hRestSplitNe : restSplit ≠ Term.Stuck := by
        intro hBad
        apply hSplit
        calc
          __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
              tail =
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                restSplit := by
            simp [__re_split_str_to_re, restSplit]
          _ = Term.Stuck := by
            rw [hBad]
            rfl
      have hRestFrontier :
          StrInReConsumeInternal.re_action_frontier_true_local restSplit :=
        ih hTail hRestSplitNe
      have hMkNe :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit ≠ Term.Stuck := by
        simpa [__re_split_str_to_re, restSplit] using hSplit
      have hMkEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit := by
        have hInnerNe :
            __eo_mk_apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c) ≠
              Term.Stuck :=
          eo_mk_apply_fun_ne_stuck_of_ne_stuck
            (__eo_mk_apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) c))
            restSplit (by
              simpa [__eo_mk_apply] using hMkNe)
        have hInnerEq :
            __eo_mk_apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c) =
              Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c) :=
          eo_mk_apply_eq_apply_of_ne_stuck
            (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) c) hInnerNe
        rw [hInnerEq]
      have hHeadNorm :
          __re_flatten (Term.Boolean false)
              (Term.Apply (Term.UOp UserOp.str_to_re) c) =
            Term.Apply (Term.UOp UserOp.str_to_re) c := by
        simp [__re_flatten]
      have hHeadComp :
          __re_rev_comp (Term.Apply (Term.UOp UserOp.str_to_re) c) ≠
            Term.Stuck := by
        simp [__re_rev_comp]
      have hFrontier :
          StrInReConsumeInternal.re_action_frontier_true_local
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit) :=
        StrInReConsumeInternal.re_action_frontier_true_mk_concat_local
          (Term.Apply (Term.UOp UserOp.str_to_re) c)
          restSplit hHeadNorm hHeadComp hRestFrontier
          (by simpa [← hMkEq] using hMkNe)
      rw [show __re_split_str_to_re
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
            tail =
          __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) c))
            restSplit by
        simp [__re_split_str_to_re, restSplit]]
      rw [hMkEq]
      exact hFrontier
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      simpa [__re_split_str_to_re] using hTail

theorem StrInReConsumeInternal.re_flatten_true_str_to_re_string_frontier_local
    (w : native_String) :
    StrInReConsumeInternal.re_action_frontier_true_local
      (__re_flatten (Term.Boolean true)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String w))) := by
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  cases w with
  | nil =>
      simp [__re_flatten, StrInReConsumeInternal.re_action_frontier_true_local]
  | cons c cs =>
      let parts :=
        __str_flatten
          (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
            (Term.String (c :: cs)))
      have hTail : StrInReConsumeInternal.re_action_frontier_true_local eps := by
        simp [eps, StrInReConsumeInternal.re_action_frontier_true_local]
      have hSplitNe :
          __re_split_str_to_re parts eps ≠ Term.Stuck :=
        StrInReConsumeInternal.re_split_str_to_re_ne_stuck_of_chunks_local parts eps
          (by
            simpa [parts] using
              StrInReConsumeInternal.str_flattened_chunks_string_flatten_local (c :: cs))
          (by simp [eps])
      have hFrontier :
          StrInReConsumeInternal.re_action_frontier_true_local
            (__re_split_str_to_re parts eps) :=
        StrInReConsumeInternal.re_split_str_to_re_action_frontier_true_local parts eps hTail
          hSplitNe
      simpa [eps, parts, __re_flatten] using hFrontier

theorem StrInReConsumeInternal.re_flatten_true_str_to_re_string_norm_local
    (w : native_String) :
    __re_flatten (Term.Boolean true)
        (__re_flatten (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String w))) =
      __re_flatten (Term.Boolean true)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String w)) := by
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  cases w with
  | nil =>
      simp [__re_flatten]
  | cons c cs =>
      let parts :=
        __str_flatten
          (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
            (Term.String (c :: cs)))
      have hSplitNe :
          __re_split_str_to_re parts eps ≠ Term.Stuck :=
        StrInReConsumeInternal.re_split_str_to_re_ne_stuck_of_chunks_local parts eps
          (by
            simpa [parts] using
              StrInReConsumeInternal.str_flattened_chunks_string_flatten_local (c :: cs))
          (by simp [eps])
      have hTailNorm :
          __re_flatten (Term.Boolean true) eps = eps := by
        simp [eps, __re_flatten]
      have hNorm :
          __re_flatten (Term.Boolean true)
              (__re_split_str_to_re parts eps) =
            __re_split_str_to_re parts eps :=
        StrInReConsumeInternal.re_split_str_to_re_flatten_true_string_flatten_local (c :: cs)
          eps hTailNorm (by simpa [parts, eps] using hSplitNe)
      simpa [eps, parts, __re_flatten] using hNorm

theorem StrInReConsumeInternal.re_flatten_true_str_to_re_string_ne_stuck_local
    (w : native_String) :
    __re_flatten (Term.Boolean true)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String w)) ≠
      Term.Stuck :=
  StrInReConsumeInternal.re_action_frontier_true_ne_stuck_local _
    (StrInReConsumeInternal.re_flatten_true_str_to_re_string_frontier_local w)

theorem StrInReConsumeInternal.smt_typeof_re_split_str_to_re_of_seq_reglan_local
    (parts tail : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true)
    (hPartsTy :
      __smtx_typeof (__eo_to_smt parts) =
        SmtType.Seq SmtType.Char)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (__re_split_str_to_re parts tail)) =
      SmtType.RegLan := by
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      simp [__eo_is_list] at hList
  | case2 parts hPartsNe =>
      change __smtx_typeof SmtTerm.None = SmtType.RegLan at hTailTy
      rw [TranslationProofs.smtx_typeof_none] at hTailTy
      cases hTailTy
  | case3 c rest tail hTailNe ih =>
      have hArgs :=
        str_concat_args_of_seq_type c rest SmtType.Char hPartsTy
      have hRestList :
          __eo_is_list (Term.UOp UserOp.str_concat) rest =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          c rest hList
      have hRestSplitTy :
          __smtx_typeof
              (__eo_to_smt (__re_split_str_to_re rest tail)) =
            SmtType.RegLan :=
        ih hRestList hArgs.2 hTailTy
      have hRestSplitNe :
          __re_split_str_to_re rest tail ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hRestSplitTy
        change __smtx_typeof SmtTerm.None = SmtType.RegLan at hRestSplitTy
        rw [TranslationProofs.smtx_typeof_none] at hRestSplitTy
        cases hRestSplitTy
      have hMkApplyEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re rest tail) :=
        have hMkApplyNe :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                (__re_split_str_to_re rest tail) ≠ Term.Stuck := by
          intro hBad
          cases hSplit : __re_split_str_to_re rest tail <;>
            simp [__eo_mk_apply, hSplit] at hBad
          exact hRestSplitNe hSplit
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) c))
          (__re_split_str_to_re rest tail) hMkApplyNe
      have hHeadTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) c)) =
            SmtType.RegLan := by
        change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt c)) =
          SmtType.RegLan
        rw [typeof_str_to_re_eq]
        simp [hArgs.1, native_ite, native_Teq]
      have hFullTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat)
                    (Term.Apply (Term.UOp UserOp.str_to_re) c))
                  (__re_split_str_to_re rest tail))) =
            SmtType.RegLan := by
        change __smtx_typeof
            (SmtTerm.re_concat
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__eo_to_smt (__re_split_str_to_re rest tail))) =
          SmtType.RegLan
        rw [typeof_re_concat_eq]
        simp [hHeadTy, hRestSplitTy, native_ite, native_Teq]
      simpa [__re_split_str_to_re, hMkApplyEq] using hFullTy
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      simpa [__re_split_str_to_re] using hTailTy

theorem StrInReConsumeInternal.re_split_str_to_re_eval_rel_consume_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ parts tail partsSs tailRv,
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true ->
      __smtx_typeof (__eo_to_smt parts) =
        SmtType.Seq SmtType.Char ->
      __smtx_model_eval M (__eo_to_smt parts) = SmtValue.Seq partsSs ->
      __smtx_typeof (__eo_to_smt tail) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt tail) = SmtValue.RegLan tailRv ->
      __re_split_str_to_re parts tail ≠ Term.Stuck ->
      ∃ outRv,
        __smtx_model_eval M (__eo_to_smt (__re_split_str_to_re parts tail)) =
          SmtValue.RegLan outRv ∧
        __smtx_typeof (__eo_to_smt (__re_split_str_to_re parts tail)) =
          SmtType.RegLan ∧
        RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
          (SmtValue.RegLan
            (native_re_concat
              (native_str_to_re (native_unpack_string partsSs)) tailRv)) := by
  intro parts tail
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      intro partsSs tailRv hList _hPartsTy _hPartsEval _hTailTy
        _hTailEval _hSplitNe
      simp [__eo_is_list] at hList
  | case2 parts hPartsNe =>
      intro partsSs tailRv _hList _hPartsTy _hPartsEval hTailTy
        _hTailEval _hSplitNe
      change __smtx_typeof SmtTerm.None = SmtType.RegLan at hTailTy
      rw [TranslationProofs.smtx_typeof_none] at hTailTy
      cases hTailTy
  | case3 c rest tail hTailNe ih =>
      intro partsSs tailRv hList hPartsTy hPartsEval hTailTy hTailEval
        hSplitNe
      have hArgs :=
        str_concat_args_of_seq_type c rest SmtType.Char hPartsTy
      have hRestList :
          __eo_is_list (Term.UOp UserOp.str_concat) rest =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          c rest hList
      rcases StrInReConsumeInternal.eval_str_concat_seq_cases_consume_local M c rest partsSs
          hPartsEval with
        ⟨cSs, restSs, hCEval, hRestEval, hPartsEq⟩
      have hCSsTy :
          __smtx_typeof_seq_value cSs =
            SmtType.Seq SmtType.Char := by
        have hCEvalTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c)) =
              SmtType.Seq SmtType.Char := by
          simpa [hArgs.1] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt c) (by
                unfold term_has_non_none_type
                rw [hArgs.1]
                simp)
        have hsimpa := hCEvalTy
        try simp [hCEval] at hsimpa ⊢
        exact hsimpa
      have hRestSplitNe :
          __re_split_str_to_re rest tail ≠ Term.Stuck := by
        intro hBad
        apply hSplitNe
        calc
          __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
              tail =
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                (__re_split_str_to_re rest tail) := by
            simp [__re_split_str_to_re]
          _ = Term.Stuck := by
            rw [hBad]
            rfl
      rcases ih restSs tailRv hRestList hArgs.2 hRestEval hTailTy
          hTailEval hRestSplitNe with
        ⟨restOutRv, hRestSplitEval, hRestSplitTy, hRestRel⟩
      let headRe := Term.Apply (Term.UOp UserOp.str_to_re) c
      let restSplit := __re_split_str_to_re rest tail
      have hHeadEval :
          __smtx_model_eval M (__eo_to_smt headRe) =
            SmtValue.RegLan (native_str_to_re (native_unpack_string cSs)) := by
        simpa [headRe] using
          eval_str_to_re_reglan_consume_local M c cSs hCEval hCSsTy
      have hHeadTy :
          __smtx_typeof (__eo_to_smt headRe) = SmtType.RegLan :=
        smt_typeof_str_to_re_of_seq_consume_local c hArgs.1
      have hMkApplyNe :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_concat) headRe)
              restSplit ≠ Term.Stuck := by
        simpa [__re_split_str_to_re, headRe, restSplit] using hSplitNe
      have hMkApplyEq :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_concat) headRe)
              restSplit =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) headRe)
              restSplit :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.re_concat) headRe) restSplit
          hMkApplyNe
      have hFullEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
                  headRe) restSplit)) =
            SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string cSs)) restOutRv) :=
        eval_re_concat_reglan_consume_local M headRe restSplit
          (native_str_to_re (native_unpack_string cSs)) restOutRv
          hHeadEval (by simpa [restSplit] using hRestSplitEval)
      have hFullTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat)
                  headRe) restSplit)) =
            SmtType.RegLan :=
        smt_typeof_re_concat_of_reglan_consume_local headRe restSplit
          hHeadTy (by simpa [restSplit] using hRestSplitTy)
      let packed :=
        native_pack_seq (__smtx_elem_typeof_seq_value cSs)
          (native_seq_concat (native_unpack_seq cSs)
            (native_unpack_seq restSs))
      have hPartsPacked : partsSs = packed := by
        simpa [packed] using hPartsEq
      have hPackedUnpack :
          native_unpack_string packed =
            native_unpack_string cSs ++ native_unpack_string restSs := by
        simpa [packed] using
          native_unpack_string_pack_seq_concat_local
            (__smtx_elem_typeof_seq_value cSs) cSs restSs
      have hPartsUnpack :
          native_unpack_string partsSs =
            native_unpack_string cSs ++ native_unpack_string restSs := by
        rw [hPartsPacked, hPackedUnpack]
      have hHeadRestRel :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string cSs))
                restOutRv))
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string cSs))
                (native_re_concat
                  (native_str_to_re (native_unpack_string restSs))
                  tailRv))) :=
        smt_value_rel_re_concat_consume_local
          (RuleProofs.smt_value_rel_refl
            (SmtValue.RegLan
              (native_str_to_re (native_unpack_string cSs))))
          hRestRel
      have hAssoc :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string cSs))
                (native_re_concat
                  (native_str_to_re (native_unpack_string restSs))
                  tailRv)))
            (SmtValue.RegLan
              (native_re_concat
                (native_re_concat
                  (native_str_to_re (native_unpack_string cSs))
                  (native_str_to_re (native_unpack_string restSs)))
                tailRv)) :=
        RuleProofs.smt_value_rel_symm _ _
          (smt_value_rel_re_concat_assoc_consume_local
            (native_str_to_re (native_unpack_string cSs))
            (native_str_to_re (native_unpack_string restSs)) tailRv)
      have hAppendHead :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string cSs))
                (native_str_to_re (native_unpack_string restSs))))
            (SmtValue.RegLan
              (native_str_to_re
                (native_unpack_string cSs ++
                  native_unpack_string restSs))) :=
        smt_value_rel_str_to_re_append_consume_local
          (native_unpack_string cSs) (native_unpack_string restSs)
      have hAppendTail :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_re_concat
                  (native_str_to_re (native_unpack_string cSs))
                  (native_str_to_re (native_unpack_string restSs)))
                tailRv))
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re
                  (native_unpack_string cSs ++
                    native_unpack_string restSs))
                tailRv)) :=
        smt_value_rel_re_concat_consume_local hAppendHead
          (RuleProofs.smt_value_rel_refl (SmtValue.RegLan tailRv))
      have hTarget :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re
                  (native_unpack_string cSs ++
                    native_unpack_string restSs))
                tailRv))
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string partsSs))
                tailRv)) := by
        rw [hPartsUnpack]
        simpa [impl_native_string_to_values, List.map_append] using
          RuleProofs.smt_value_rel_refl
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re
                  (native_unpack_string cSs ++
                    native_unpack_string restSs))
                tailRv))
      refine ⟨native_re_concat
          (native_str_to_re (native_unpack_string cSs)) restOutRv,
        ?_, ?_, ?_⟩
      · simpa [__re_split_str_to_re, headRe, restSplit, hMkApplyEq]
          using hFullEval
      · simpa [__re_split_str_to_re, headRe, restSplit, hMkApplyEq]
          using hFullTy
      · exact RuleProofs.smt_value_rel_trans _ _ _
          (RuleProofs.smt_value_rel_trans _ _ _
            (RuleProofs.smt_value_rel_trans _ _ _ hHeadRestRel hAssoc)
            hAppendTail)
          hTarget
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      intro partsSs tailRv hList hPartsTy hPartsEval hTailTy hTailEval
        _hSplitNe
      have hPartsNilRel :
          RuleProofs.smt_value_rel (SmtValue.Seq partsSs)
            (SmtValue.Seq (SmtSeq.empty SmtType.Char)) := by
        have hNil :
            __eo_is_list_nil (Term.UOp UserOp.str_concat) parts =
              Term.Boolean true :=
          eo_is_list_nil_str_concat_of_list_true_not_concat_local parts
            hList (by
              intro h
              rcases h with ⟨head, rest, hEq⟩
              exact hNotConcat head rest hEq)
        have hRel := smt_value_rel_str_concat_nil_empty M parts
          SmtType.Char hNil hPartsTy
        simpa [hPartsEval] using hRel
      have hStrRel :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan
              (native_str_to_re (native_unpack_string partsSs)))
            (SmtValue.RegLan (native_str_to_re [])) :=
        smt_value_rel_str_to_re_of_seq_rel_consume_local hPartsNilRel
      have hEmptyLeft :
          RuleProofs.smt_value_rel (SmtValue.RegLan tailRv)
            (SmtValue.RegLan
              (native_re_concat (native_str_to_re []) tailRv)) := by
        rw [native_re_concat_left_empty_local]
        exact RuleProofs.smt_value_rel_refl (SmtValue.RegLan tailRv)
      have hPrefix :
          RuleProofs.smt_value_rel
            (SmtValue.RegLan (native_re_concat (native_str_to_re []) tailRv))
            (SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string partsSs))
                tailRv)) :=
        smt_value_rel_re_concat_consume_local
          (RuleProofs.smt_value_rel_symm _ _ hStrRel)
          (RuleProofs.smt_value_rel_refl (SmtValue.RegLan tailRv))
      refine ⟨tailRv, ?_, ?_, ?_⟩
      · simpa [__re_split_str_to_re] using hTailEval
      · simpa [__re_split_str_to_re] using hTailTy
      · exact RuleProofs.smt_value_rel_trans _ _ _ hEmptyLeft hPrefix

theorem StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
    (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  have hNN : term_has_non_none_type
      (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    change
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) ≠
        SmtType.None
    rw [hTy]
    simp
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
    (typeof_re_concat_eq (__eo_to_smt a) (__eo_to_smt b)) hNN

theorem StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local
    (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  have hNN : term_has_non_none_type
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    change
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) ≠
        SmtType.None
    rw [hTy]
    simp
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
    (typeof_re_inter_eq (__eo_to_smt a) (__eo_to_smt b)) hNN

theorem StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local
    (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  have hNN : term_has_non_none_type
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    change
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) ≠
        SmtType.None
    rw [hTy]
    simp
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
    (typeof_re_union_eq (__eo_to_smt a) (__eo_to_smt b)) hNN

theorem StrInReConsumeInternal.re_mult_arg_type_of_reglan_consume_local
    (r : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
  exact RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan
    r hTy

theorem StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [__smtx_typeof, native_string_valid, native_ite, native_Teq]

theorem StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local :
    __eo_is_list (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
      Term.Boolean true := by
  rfl

theorem StrInReConsumeInternal.re_rev_map_rev_acc_ne_stuck_of_ne_stuck_local
    (a acc : Term)
    (h : __re_rev_map_rev a acc ≠ Term.Stuck) :
    acc ≠ Term.Stuck := by
  intro hAcc
  subst acc
  simp [__re_rev_map_rev] at h

theorem StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local
    (a acc : Term)
    (h : __re_rev_map_rev a acc ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro hA
  subst a
  cases acc <;> simp [__re_rev_map_rev] at h

abbrev StrInReConsumeInternal.re_empty_string_re_consume_local : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])

theorem StrInReConsumeInternal.re_rev_comp_arg_ne_stuck_of_ne_stuck_local
    (c : Term)
    (h : __re_rev_comp c ≠ Term.Stuck) :
    c ≠ Term.Stuck := by
  intro hc
  subst c
  simp [__re_rev_comp] at h

theorem StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
    (f x : Term)
    (hf : f ≠ Term.Stuck)
    (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x ≠ Term.Stuck := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem StrInReConsumeInternal.re_action_frontier_true_rev_map_ne_stuck_local :
    ∀ t acc,
      StrInReConsumeInternal.re_action_frontier_true_local t ->
      acc ≠ Term.Stuck ->
        __re_rev_map_rev t acc ≠ Term.Stuck
  | Term.Stuck, _acc, hFrontier, _hAcc => by
      cases hFrontier
  | Term.Apply (Term.UOp op) x, acc, hFrontier, hAcc => by
      by_cases hop : op = UserOp.str_to_re
      · subst op
        cases x <;>
          simp [StrInReConsumeInternal.re_action_frontier_true_local]
            at hFrontier ⊢
        all_goals
          try
            rename_i w
            cases w <;>
              simp [StrInReConsumeInternal.re_action_frontier_true_local, __re_rev_map_rev]
                at hFrontier ⊢
        all_goals try assumption
      · exfalso
        cases op <;> simp [StrInReConsumeInternal.re_action_frontier_true_local] at hFrontier hop
  | Term.Apply (Term.Apply (Term.UOp op) head) tail, acc,
      hFrontier, hAcc => by
      by_cases hop : op = UserOp.re_concat
      · subst op
        rcases hFrontier with ⟨_hHeadNorm, hHeadComp, hTail⟩
        let inner :=
          __eo_mk_apply (Term.UOp UserOp.re_concat) (__re_rev_comp head)
        let newAcc := __eo_mk_apply inner acc
        have hInnerNe : inner ≠ Term.Stuck :=
          StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
            (Term.UOp UserOp.re_concat) (__re_rev_comp head)
            (by simp) hHeadComp
        have hNewAccNe : newAcc ≠ Term.Stuck :=
          StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local inner acc hInnerNe hAcc
        have hTailRev :
            __re_rev_map_rev tail newAcc ≠ Term.Stuck :=
          StrInReConsumeInternal.re_action_frontier_true_rev_map_ne_stuck_local tail newAcc
            hTail hNewAccNe
        simpa [__re_rev_map_rev, inner, newAcc] using hTailRev
      · exfalso
        cases op <;> simp [StrInReConsumeInternal.re_action_frontier_true_local] at hFrontier hop
  | t, acc, hFrontier, hAcc => by
      cases t <;> try cases hFrontier
      case Apply f x =>
        cases f <;> try cases hFrontier
        case UOp op =>
          by_cases hop : op = UserOp.str_to_re
          · subst op
            cases x <;>
              simp [StrInReConsumeInternal.re_action_frontier_true_local]
                at hFrontier ⊢
            all_goals
              try
                rename_i w
                cases w <;>
                  simp [StrInReConsumeInternal.re_action_frontier_true_local, __re_rev_map_rev]
                    at hFrontier ⊢
            all_goals try assumption
          · exfalso
            cases op <;>
              simp [StrInReConsumeInternal.re_action_frontier_true_local] at hFrontier hop
        case Apply f' y =>
          cases f' <;> try cases hFrontier
          case UOp op =>
            by_cases hop : op = UserOp.re_concat
            · subst op
              rcases hFrontier with ⟨_hHeadNorm, hHeadComp, hTail⟩
              let inner :=
                __eo_mk_apply (Term.UOp UserOp.re_concat)
                  (__re_rev_comp y)
              let newAcc := __eo_mk_apply inner acc
              have hInnerNe : inner ≠ Term.Stuck :=
                StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
                  (Term.UOp UserOp.re_concat) (__re_rev_comp y)
                  (by simp) hHeadComp
              have hNewAccNe : newAcc ≠ Term.Stuck :=
                StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local inner acc hInnerNe hAcc
              have hTailRev :
                  __re_rev_map_rev x newAcc ≠ Term.Stuck :=
                StrInReConsumeInternal.re_action_frontier_true_rev_map_ne_stuck_local x newAcc
                  hTail hNewAccNe
              simpa [__re_rev_map_rev, inner, newAcc] using hTailRev
            · exfalso
              cases op <;>
                simp [StrInReConsumeInternal.re_action_frontier_true_local] at hFrontier hop
termination_by t acc _ _ => sizeOf t

theorem StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
    (f x : Term)
    (hf : f ≠ Term.Stuck)
    (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x :=
  eo_mk_apply_eq_apply_of_ne_stuck f x
    (StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local f x hf hx)

def StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local
    (a acc : Term) : Prop :=
  __re_rev_map_rev a acc ≠ Term.Stuck ->
    __re_rev_map_rev (__re_rev_map_rev a acc)
        StrInReConsumeInternal.re_empty_string_re_consume_local =
      __re_rev_map_rev acc a

def StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local
    (c : Term) : Prop :=
  __re_rev_comp c ≠ Term.Stuck ->
    __re_rev_comp (__re_rev_comp c) = c

theorem StrInReConsumeInternal.re_rev_map_rev_comp_action_involutive_local :
    (∀ a acc, StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local a acc) ∧
      (∀ c, StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local c) := by
  let eps := StrInReConsumeInternal.re_empty_string_re_consume_local
  have case1 :
      ∀ t, StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local t Term.Stuck := by
    intro t h
    exfalso
    exact h (__re_rev_map_rev.eq_1 t)
  have case2 :
      ∀ acc, (acc = Term.Stuck -> False) ->
        StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local eps acc := by
    intro acc hAccNe _hRev
    simpa [StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local, eps,
      StrInReConsumeInternal.re_empty_string_re_consume_local, __re_rev_map_rev.eq_2 acc hAccNe]
  have case3 :
      ∀ a b acc,
        (acc = Term.Stuck -> False) ->
        StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local a ->
        StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local b
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_concat)
              (__re_rev_comp a)) acc) ->
        StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)
          acc := by
    intro a b acc hAccNe ihComp ihTail hRev
    let compA := __re_rev_comp a
    let newAcc :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_concat) compA) acc
    have hEq :
        __re_rev_map_rev
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)
            acc =
          __re_rev_map_rev b newAcc := by
      simpa [compA, newAcc] using
        __re_rev_map_rev.eq_3 acc a b hAccNe
    have hTailRev : __re_rev_map_rev b newAcc ≠ Term.Stuck := by
      intro hBad
      exact hRev (by simpa [hEq] using hBad)
    have hTail := ihTail hTailRev
    have hNewAccNe : newAcc ≠ Term.Stuck :=
      StrInReConsumeInternal.re_rev_map_rev_acc_ne_stuck_of_ne_stuck_local b newAcc hTailRev
    have hInnerNe :
        __eo_mk_apply (Term.UOp UserOp.re_concat) compA ≠ Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.re_concat) compA) acc
        (by simpa [newAcc] using hNewAccNe)
    have hCompNe : compA ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.re_concat) compA hInnerNe
    have hCompInv : __re_rev_comp compA = a :=
      ihComp (by simpa [compA] using hCompNe)
    have hBNe : b ≠ Term.Stuck :=
      StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local b newAcc hTailRev
    have hANe : a ≠ Term.Stuck :=
      StrInReConsumeInternal.re_rev_comp_arg_ne_stuck_of_ne_stuck_local a
        (by simpa [compA] using hCompNe)
    have hInnerEq :
        __eo_mk_apply (Term.UOp UserOp.re_concat) compA =
          Term.Apply (Term.UOp UserOp.re_concat) compA :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.UOp UserOp.re_concat) compA hInnerNe
    have hNewAccEq :
        newAcc = Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat) compA) acc := by
      have hOuterEq := eo_mk_apply_eq_apply_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.re_concat) compA) acc
        (by simpa [newAcc] using hNewAccNe)
      rw [show newAcc =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) compA) acc by
            rfl,
        hOuterEq, hInnerEq]
    have hMapNew :
        __re_rev_map_rev newAcc b =
          __re_rev_map_rev acc
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) := by
      have hEqNew :
          __re_rev_map_rev
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) compA)
                acc) b =
            __re_rev_map_rev acc
              (__eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp.re_concat)
                  (__re_rev_comp compA)) b) := by
        simpa using __re_rev_map_rev.eq_3 b compA acc hBNe
      have hMkInnerA :
          __eo_mk_apply (Term.UOp UserOp.re_concat) a =
            Term.Apply (Term.UOp UserOp.re_concat) a :=
        StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
          (Term.UOp UserOp.re_concat) a (by simp) hANe
      have hMkOuterA :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) a) b =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b := by
        rw [StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
          (__eo_mk_apply (Term.UOp UserOp.re_concat) a) b]
        · rw [hMkInnerA]
        · rw [hMkInnerA]
          simp
        · exact hBNe
      rw [hNewAccEq]
      rw [hEqNew]
      rw [hCompInv]
      rw [hMkOuterA]
    calc
      __re_rev_map_rev
          (__re_rev_map_rev
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)
            acc) StrInReConsumeInternal.re_empty_string_re_consume_local
          = __re_rev_map_rev (__re_rev_map_rev b newAcc)
              StrInReConsumeInternal.re_empty_string_re_consume_local := by
            rw [hEq]
      _ = __re_rev_map_rev newAcc b := hTail
      _ = __re_rev_map_rev acc
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) :=
            hMapNew
  have case4 :
      ∀ t x,
        (x = Term.Stuck -> False) ->
        (t = eps -> False) ->
        (∀ a b,
          t = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
            False) ->
        StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local t x := by
    intro t x hX hNotEps hNotConcat hRev
    exfalso
    exact hRev (by
      simpa [eps, StrInReConsumeInternal.re_empty_string_re_consume_local] using
        __re_rev_map_rev.eq_4 t x
          (by simpa [eps, StrInReConsumeInternal.re_empty_string_re_consume_local] using hNotEps)
          hNotConcat hX)
  have case5 :
      StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local Term.Stuck := by
    intro h
    exfalso
    exact h __re_rev_comp.eq_1
  have case6 :
      StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local
        (Term.UOp UserOp.re_all) := by
    intro _h
    simp [__re_rev_comp]
  have case7 :
      StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local
        (Term.UOp UserOp.re_none) := by
    intro _h
    simp [__re_rev_comp]
  have case8 :
      ∀ body, StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local body eps ->
        StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local
          (Term.Apply (Term.UOp UserOp.re_mult) body) := by
    intro body ih hRev
    let mapped := __re_rev_map_rev body eps
    have hEq :
        __re_rev_comp (Term.Apply (Term.UOp UserOp.re_mult) body) =
          __eo_mk_apply (Term.UOp UserOp.re_mult) mapped := by
      simpa [eps, mapped] using __re_rev_comp.eq_4 body
    have hMkNe :
        __eo_mk_apply (Term.UOp UserOp.re_mult) mapped ≠ Term.Stuck := by
      intro hBad
      exact hRev (by simpa [hEq] using hBad)
    have hMappedNe : mapped ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.re_mult) mapped hMkNe
    have hMapInv := ih (by simpa [mapped] using hMappedNe)
    have hBodyNe : body ≠ Term.Stuck :=
      StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local body eps
        (by simpa [mapped] using hMappedNe)
    have hMapEpsBody : __re_rev_map_rev eps body = body := by
      simpa [eps, StrInReConsumeInternal.re_empty_string_re_consume_local] using
        __re_rev_map_rev.eq_2 body hBodyNe
    have hMkEqMapped :
        __eo_mk_apply (Term.UOp UserOp.re_mult) mapped =
          Term.Apply (Term.UOp UserOp.re_mult) mapped :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.UOp UserOp.re_mult) mapped hMkNe
    have hMkEqBody :
        __eo_mk_apply (Term.UOp UserOp.re_mult) body =
          Term.Apply (Term.UOp UserOp.re_mult) body :=
      StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
        (Term.UOp UserOp.re_mult) body (by simp) hBodyNe
    rw [hEq, hMkEqMapped]
    simp [__re_rev_comp]
    rw [show __re_rev_map_rev mapped StrInReConsumeInternal.re_empty_string_re_consume_local =
          __re_rev_map_rev eps body by
        simpa [eps, StrInReConsumeInternal.re_empty_string_re_consume_local, mapped] using hMapInv]
    rw [hMapEpsBody]
    rw [hMkEqBody]
  have comp_inter_union
      (op : UserOp)
      (hop : op = UserOp.re_inter ∨ op = UserOp.re_union)
      (c1 c2 : Term)
      (ihLeft : StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local c1 eps)
      (ihRight : StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local c2)
      (hRev :
        __re_rev_comp (Term.Apply (Term.Apply (Term.UOp op) c1) c2) ≠
          Term.Stuck) :
      __re_rev_comp
          (__re_rev_comp (Term.Apply (Term.Apply (Term.UOp op) c1) c2)) =
        Term.Apply (Term.Apply (Term.UOp op) c1) c2 := by
    cases hop with
    | inl hopInter =>
        subst op
        let left := __re_rev_map_rev c1 eps
        let right := __re_rev_comp c2
        let inner := __eo_mk_apply (Term.UOp UserOp.re_inter) left
        let outer := __eo_mk_apply inner right
        have hEq :
            __re_rev_comp
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
                  c2) =
              outer := by
          simpa [eps, left, right, inner, outer] using
            __re_rev_comp.eq_5 c1 c2
        have hOuterNe : outer ≠ Term.Stuck := by
          intro hBad
          exact hRev (by simpa [hEq] using hBad)
        have hInnerNe : inner ≠ Term.Stuck :=
          eo_mk_apply_fun_ne_stuck_of_ne_stuck inner right hOuterNe
        have hRightNe : right ≠ Term.Stuck :=
          eo_mk_apply_arg_ne_stuck_of_ne_stuck inner right hOuterNe
        have hLeftNe : left ≠ Term.Stuck :=
          eo_mk_apply_arg_ne_stuck_of_ne_stuck
            (Term.UOp UserOp.re_inter) left hInnerNe
        have hLeftInv := ihLeft (by simpa [left] using hLeftNe)
        have hRightInv := ihRight (by simpa [right] using hRightNe)
        have hC1Ne : c1 ≠ Term.Stuck :=
          StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local c1 eps
            (by simpa [left] using hLeftNe)
        have hC2Ne : c2 ≠ Term.Stuck :=
          StrInReConsumeInternal.re_rev_comp_arg_ne_stuck_of_ne_stuck_local c2
            (by simpa [right] using hRightNe)
        have hMapEpsC1 : __re_rev_map_rev eps c1 = c1 := by
          simpa [eps, StrInReConsumeInternal.re_empty_string_re_consume_local] using
            __re_rev_map_rev.eq_2 c1 hC1Ne
        have hInnerEq :
            inner = Term.Apply (Term.UOp UserOp.re_inter) left :=
          eo_mk_apply_eq_apply_of_ne_stuck
            (Term.UOp UserOp.re_inter) left hInnerNe
        have hOuterEq :
            outer = Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) left) right := by
          have hOuterEq0 :=
            eo_mk_apply_eq_apply_of_ne_stuck inner right hOuterNe
          simpa [outer, hInnerEq] using hOuterEq0
        have hMkInnerC1 :
            __eo_mk_apply (Term.UOp UserOp.re_inter) c1 =
              Term.Apply (Term.UOp UserOp.re_inter) c1 :=
          StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
            (Term.UOp UserOp.re_inter) c1 (by simp) hC1Ne
        have hMkOuterC :
            __eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp.re_inter) c1) c2 =
              Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 := by
          rw [StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
            (__eo_mk_apply (Term.UOp UserOp.re_inter) c1) c2]
          · rw [hMkInnerC1]
          · rw [hMkInnerC1]
            simp
          · exact hC2Ne
        rw [hEq, hOuterEq]
        simp [__re_rev_comp]
        rw [show __re_rev_map_rev left StrInReConsumeInternal.re_empty_string_re_consume_local =
              __re_rev_map_rev eps c1 by
            simpa [eps, StrInReConsumeInternal.re_empty_string_re_consume_local, left] using
              hLeftInv]
        rw [hMapEpsC1]
        rw [hRightInv]
        rw [hMkOuterC]
    | inr hopUnion =>
        subst op
        let left := __re_rev_map_rev c1 eps
        let right := __re_rev_comp c2
        let inner := __eo_mk_apply (Term.UOp UserOp.re_union) left
        let outer := __eo_mk_apply inner right
        have hEq :
            __re_rev_comp
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1)
                  c2) =
              outer := by
          simpa [eps, left, right, inner, outer] using
            __re_rev_comp.eq_6 c1 c2
        have hOuterNe : outer ≠ Term.Stuck := by
          intro hBad
          exact hRev (by simpa [hEq] using hBad)
        have hInnerNe : inner ≠ Term.Stuck :=
          eo_mk_apply_fun_ne_stuck_of_ne_stuck inner right hOuterNe
        have hRightNe : right ≠ Term.Stuck :=
          eo_mk_apply_arg_ne_stuck_of_ne_stuck inner right hOuterNe
        have hLeftNe : left ≠ Term.Stuck :=
          eo_mk_apply_arg_ne_stuck_of_ne_stuck
            (Term.UOp UserOp.re_union) left hInnerNe
        have hLeftInv := ihLeft (by simpa [left] using hLeftNe)
        have hRightInv := ihRight (by simpa [right] using hRightNe)
        have hC1Ne : c1 ≠ Term.Stuck :=
          StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local c1 eps
            (by simpa [left] using hLeftNe)
        have hC2Ne : c2 ≠ Term.Stuck :=
          StrInReConsumeInternal.re_rev_comp_arg_ne_stuck_of_ne_stuck_local c2
            (by simpa [right] using hRightNe)
        have hMapEpsC1 : __re_rev_map_rev eps c1 = c1 := by
          simpa [eps, StrInReConsumeInternal.re_empty_string_re_consume_local] using
            __re_rev_map_rev.eq_2 c1 hC1Ne
        have hInnerEq :
            inner = Term.Apply (Term.UOp UserOp.re_union) left :=
          eo_mk_apply_eq_apply_of_ne_stuck
            (Term.UOp UserOp.re_union) left hInnerNe
        have hOuterEq :
            outer = Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) left) right := by
          have hOuterEq0 :=
            eo_mk_apply_eq_apply_of_ne_stuck inner right hOuterNe
          simpa [outer, hInnerEq] using hOuterEq0
        have hMkInnerC1 :
            __eo_mk_apply (Term.UOp UserOp.re_union) c1 =
              Term.Apply (Term.UOp UserOp.re_union) c1 :=
          StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
            (Term.UOp UserOp.re_union) c1 (by simp) hC1Ne
        have hMkOuterC :
            __eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp.re_union) c1) c2 =
              Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 := by
          rw [StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
            (__eo_mk_apply (Term.UOp UserOp.re_union) c1) c2]
          · rw [hMkInnerC1]
          · rw [hMkInnerC1]
            simp
          · exact hC2Ne
        rw [hEq, hOuterEq]
        simp [__re_rev_comp]
        rw [show __re_rev_map_rev left StrInReConsumeInternal.re_empty_string_re_consume_local =
              __re_rev_map_rev eps c1 by
            simpa [eps, StrInReConsumeInternal.re_empty_string_re_consume_local, left] using
              hLeftInv]
        rw [hMapEpsC1]
        rw [hRightInv]
        rw [hMkOuterC]
  have case9 :
      ∀ c1 c2,
        StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local c1 eps ->
        StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local c2 ->
        StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
    intro c1 c2 ihLeft ihRight hRev
    exact comp_inter_union UserOp.re_inter (Or.inl rfl) c1 c2
      ihLeft ihRight hRev
  have case10 :
      ∀ c1 c2,
        StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local c1 eps ->
        StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local c2 ->
        StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
    intro c1 c2 ihLeft ihRight hRev
    exact comp_inter_union UserOp.re_union (Or.inr rfl) c1 c2
      ihLeft ihRight hRev
  have case11 :
      ∀ c,
        (c = Term.Stuck -> False) ->
        (c = Term.UOp UserOp.re_all -> False) ->
        (c = Term.UOp UserOp.re_none -> False) ->
        (∀ body, c = Term.Apply (Term.UOp UserOp.re_mult) body ->
          False) ->
        (∀ c1 c2,
          c = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
            False) ->
        (∀ c1 c2,
          c = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
            False) ->
        StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local c := by
    intro c hSt hAll hNone hMult hInter hUnion hRev
    simpa [StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local,
      __re_rev_comp.eq_7 c hSt hAll hNone hMult hInter hUnion]
  constructor
  · intro a acc
    exact __re_rev_map_rev.induct
      StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local
      StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local
      case1 case2 case3 case4 case5 case6 case7 case8 case9 case10
      case11 a acc
  · intro c
    exact __re_rev_comp.induct
      StrInReConsumeInternal.re_rev_map_rev_action_involutive_motive_local
      StrInReConsumeInternal.re_rev_comp_action_involutive_motive_local
      case1 case2 case3 case4 case5 case6 case7 case8 case9 case10
      case11 c

theorem StrInReConsumeInternal.re_rev_map_rev_action_double_eps_local
    (a : Term)
    (hRev :
      __re_rev_map_rev a StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck) :
    __re_rev_map_rev
        (__re_rev_map_rev a StrInReConsumeInternal.re_empty_string_re_consume_local)
        StrInReConsumeInternal.re_empty_string_re_consume_local =
      a := by
  have hMain :=
    (StrInReConsumeInternal.re_rev_map_rev_comp_action_involutive_local.1
      a StrInReConsumeInternal.re_empty_string_re_consume_local) hRev
  have hANe : a ≠ Term.Stuck :=
    StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local
      a StrInReConsumeInternal.re_empty_string_re_consume_local hRev
  have hEpsA : __re_rev_map_rev StrInReConsumeInternal.re_empty_string_re_consume_local a = a := by
    simpa [StrInReConsumeInternal.re_empty_string_re_consume_local] using
      __re_rev_map_rev.eq_2 a hANe
  simpa [hEpsA] using hMain

theorem StrInReConsumeInternal.re_rev_map_rev_action_double_eps_reglan_rel_local
    (M : SmtModel) (t : Term) (rv nextRv : SmtRegLan)
    (hRev :
      __re_rev_map_rev t StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv)
    (hNextEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_rev_map_rev t StrInReConsumeInternal.re_empty_string_re_consume_local)
              StrInReConsumeInternal.re_empty_string_re_consume_local)) =
        SmtValue.RegLan nextRv) :
    RuleProofs.smt_value_rel (SmtValue.RegLan nextRv)
      (SmtValue.RegLan rv) := by
  have hDouble :
      __re_rev_map_rev
          (__re_rev_map_rev t StrInReConsumeInternal.re_empty_string_re_consume_local)
          StrInReConsumeInternal.re_empty_string_re_consume_local =
        t :=
    StrInReConsumeInternal.re_rev_map_rev_action_double_eps_local t hRev
  have hNextAsOriginal :
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan nextRv := by
    rw [← hDouble]
    exact hNextEval
  have hRv : rv = nextRv := by
    rw [hEval] at hNextAsOriginal
    cases hNextAsOriginal
    rfl
  subst rv
  exact RuleProofs.smt_value_rel_refl (SmtValue.RegLan nextRv)

theorem StrInReConsumeInternal.eval_re_action_double_rev_reglan_rel_consume_local
    (M : SmtModel) (rParts : Term) (rv : SmtRegLan)
    (hEval : __smtx_model_eval M (__eo_to_smt rParts) = SmtValue.RegLan rv)
    (hRev :
      __re_rev_map_rev rParts StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck) :
    ∃ revRevRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_rev_map_rev rParts StrInReConsumeInternal.re_empty_string_re_consume_local)
              StrInReConsumeInternal.re_empty_string_re_consume_local)) =
        SmtValue.RegLan revRevRv ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan revRevRv)
        (SmtValue.RegLan rv) := by
  refine ⟨rv, ?_, RuleProofs.smt_value_rel_refl (SmtValue.RegLan rv)⟩
  rw [StrInReConsumeInternal.re_rev_map_rev_action_double_eps_local rParts hRev]
  exact hEval

theorem StrInReConsumeInternal.re_action_frontier_true_double_rev_eq_local
    (t : Term)
    (hFrontier : StrInReConsumeInternal.re_action_frontier_true_local t) :
    __re_rev_map_rev
        (__re_rev_map_rev t StrInReConsumeInternal.re_empty_string_re_consume_local)
        StrInReConsumeInternal.re_empty_string_re_consume_local =
      t :=
  StrInReConsumeInternal.re_rev_map_rev_action_double_eps_local t
    (StrInReConsumeInternal.re_action_frontier_true_rev_map_ne_stuck_local t
      StrInReConsumeInternal.re_empty_string_re_consume_local hFrontier
      (by simp [StrInReConsumeInternal.re_empty_string_re_consume_local]))

theorem StrInReConsumeInternal.re_action_frontier_true_double_rev_reglan_rel_local
    (M : SmtModel) (t : Term) (rv nextRv : SmtRegLan)
    (hFrontier : StrInReConsumeInternal.re_action_frontier_true_local t)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv)
    (hNextEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_rev_map_rev t StrInReConsumeInternal.re_empty_string_re_consume_local)
              StrInReConsumeInternal.re_empty_string_re_consume_local)) =
        SmtValue.RegLan nextRv) :
    RuleProofs.smt_value_rel (SmtValue.RegLan nextRv)
      (SmtValue.RegLan rv) := by
  exact StrInReConsumeInternal.re_rev_map_rev_action_double_eps_reglan_rel_local M t rv nextRv
    (StrInReConsumeInternal.re_action_frontier_true_rev_map_ne_stuck_local t
      StrInReConsumeInternal.re_empty_string_re_consume_local hFrontier
      (by simp [StrInReConsumeInternal.re_empty_string_re_consume_local]))
    hEval hNextEval

theorem StrInReConsumeInternal.re_flatten_false_mult_of_norm_local
    (body : Term)
    (hBody : __re_flatten (Term.Boolean true) body = body)
    (hMk : __eo_mk_apply (Term.UOp UserOp.re_mult) body ≠ Term.Stuck) :
    __re_flatten (Term.Boolean false)
        (__eo_mk_apply (Term.UOp UserOp.re_mult) body) =
      __eo_mk_apply (Term.UOp UserOp.re_mult) body := by
  have hMkEq :
      __eo_mk_apply (Term.UOp UserOp.re_mult) body =
        Term.Apply (Term.UOp UserOp.re_mult) body :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.re_mult) body hMk
  calc
    __re_flatten (Term.Boolean false)
        (__eo_mk_apply (Term.UOp UserOp.re_mult) body) =
        __re_flatten (Term.Boolean false)
          (Term.Apply (Term.UOp UserOp.re_mult) body) := by
          rw [hMkEq]
    _ = __eo_mk_apply (Term.UOp UserOp.re_mult) body := by
          simp [__re_flatten, hBody]

theorem StrInReConsumeInternal.re_flatten_false_inter_of_norm_local
    (a b : Term)
    (hA : __re_flatten (Term.Boolean true) a = a)
    (hB : __re_flatten (Term.Boolean false) b = b)
    (hMk :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_inter) a) b ≠
        Term.Stuck) :
    __re_flatten (Term.Boolean false)
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_inter) a) b) =
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_inter) a) b := by
  let inner := __eo_mk_apply (Term.UOp UserOp.re_inter) a
  have hInnerNe : inner ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck inner b
      (by simpa [inner] using hMk)
  have hInnerEq :
      inner = Term.Apply (Term.UOp UserOp.re_inter) a :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.re_inter) a hInnerNe
  have hOuterEq :
      __eo_mk_apply inner b = Term.Apply inner b :=
    eo_mk_apply_eq_apply_of_ne_stuck inner b
      (by simpa [inner] using hMk)
  have hMkEq :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_inter) a) b =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b := by
    change __eo_mk_apply inner b =
      Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b
    rw [hOuterEq, hInnerEq]
  calc
    __re_flatten (Term.Boolean false)
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_inter) a) b) =
        __re_flatten (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b) := by
          rw [hMkEq]
    _ = __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_inter) a) b := by
          simp [__re_flatten, hA, hB]

theorem StrInReConsumeInternal.re_flatten_false_union_of_norm_local
    (a b : Term)
    (hA : __re_flatten (Term.Boolean true) a = a)
    (hB : __re_flatten (Term.Boolean false) b = b)
    (hMk :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_union) a) b ≠
        Term.Stuck) :
    __re_flatten (Term.Boolean false)
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_union) a) b) =
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_union) a) b := by
  let inner := __eo_mk_apply (Term.UOp UserOp.re_union) a
  have hInnerNe : inner ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck inner b
      (by simpa [inner] using hMk)
  have hInnerEq :
      inner = Term.Apply (Term.UOp UserOp.re_union) a :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.re_union) a hInnerNe
  have hOuterEq :
      __eo_mk_apply inner b = Term.Apply inner b :=
    eo_mk_apply_eq_apply_of_ne_stuck inner b
      (by simpa [inner] using hMk)
  have hMkEq :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_union) a) b =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b := by
    change __eo_mk_apply inner b =
      Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b
    rw [hOuterEq, hInnerEq]
  calc
    __re_flatten (Term.Boolean false)
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_union) a) b) =
        __re_flatten (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b) := by
          rw [hMkEq]
    _ = __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_union) a) b := by
          simp [__re_flatten, hA, hB]

theorem StrInReConsumeInternal.re_rev_map_rev_mk_concat_eq_local
    (a b acc : Term)
    (hMk :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_concat) a) b ≠
        Term.Stuck)
    (hAcc : acc ≠ Term.Stuck) :
    __re_rev_map_rev
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_concat) a) b)
        acc =
      __re_rev_map_rev b
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat)
            (__re_rev_comp a)) acc) := by
  let inner := __eo_mk_apply (Term.UOp UserOp.re_concat) a
  have hInnerNe : inner ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck inner b
      (by simpa [inner] using hMk)
  have hInnerEq :
      inner = Term.Apply (Term.UOp UserOp.re_concat) a :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.re_concat) a hInnerNe
  have hMkEq :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_concat) a) b =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b := by
    change __eo_mk_apply inner b =
      Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b
    rw [eo_mk_apply_eq_apply_of_ne_stuck inner b
      (by simpa [inner] using hMk), hInnerEq]
  rw [hMkEq]
  exact __re_rev_map_rev.eq_3 acc a b hAcc

theorem StrInReConsumeInternal.re_split_str_to_re_rev_map_ne_stuck_local
    (parts tail : Term)
    (hTail :
      ∀ acc, acc ≠ Term.Stuck ->
        __re_rev_map_rev tail acc ≠ Term.Stuck)
    (hSplit : __re_split_str_to_re parts tail ≠ Term.Stuck) :
    ∀ acc, acc ≠ Term.Stuck ->
      __re_rev_map_rev (__re_split_str_to_re parts tail) acc ≠
        Term.Stuck := by
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 tail =>
      simp [__re_split_str_to_re] at hSplit
  | case2 parts hPartsNe =>
      simp [__re_split_str_to_re] at hSplit
  | case3 c rest tail hTailNe ih =>
      intro acc hAcc
      let restSplit := __re_split_str_to_re rest tail
      have hRestSplitNe : restSplit ≠ Term.Stuck := by
        intro hBad
        apply hSplit
        calc
          __re_split_str_to_re
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
              tail =
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                restSplit := by
            simp [__re_split_str_to_re, restSplit]
          _ = Term.Stuck := by
            rw [hBad]
            rfl
      have hMkNe :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit ≠ Term.Stuck := by
        simpa [__re_split_str_to_re, restSplit] using hSplit
      have hMkEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              restSplit := by
        have hInnerNe :
            __eo_mk_apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c) ≠
              Term.Stuck :=
          eo_mk_apply_fun_ne_stuck_of_ne_stuck
            (__eo_mk_apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) c))
            restSplit (by
              simpa [__eo_mk_apply] using hMkNe)
        have hInnerEq :
            __eo_mk_apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c) =
              Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c) :=
          eo_mk_apply_eq_apply_of_ne_stuck
            (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) c) hInnerNe
        rw [hInnerEq]
      let head := Term.Apply (Term.UOp UserOp.str_to_re) c
      let newAcc :=
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat)
            (__re_rev_comp head)) acc
      have hHeadComp : __re_rev_comp head ≠ Term.Stuck := by
        simp [head, __re_rev_comp]
      have hInnerNewNe :
          __eo_mk_apply (Term.UOp UserOp.re_concat)
              (__re_rev_comp head) ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (Term.UOp UserOp.re_concat) (__re_rev_comp head)
          (by simp) hHeadComp
      have hNewAccNe : newAcc ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (__eo_mk_apply (Term.UOp UserOp.re_concat)
            (__re_rev_comp head)) acc hInnerNewNe hAcc
      have hRestRev :
          __re_rev_map_rev restSplit newAcc ≠ Term.Stuck :=
        ih hTail hRestSplitNe newAcc hNewAccNe
      have hNestedMkNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) head)
              restSplit ≠ Term.Stuck := by
        simpa [← hMkEq, head] using hMkNe
      rw [show __re_split_str_to_re
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) c) rest)
            tail =
          __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) c))
            restSplit by
        simp [__re_split_str_to_re, restSplit]]
      rw [hMkEq]
      rw [StrInReConsumeInternal.re_rev_map_rev_mk_concat_eq_local head restSplit acc
        hNestedMkNe hAcc]
      simpa [head, newAcc] using hRestRev
  | case4 parts tail hPartsNe hTailNe hNotConcat =>
      intro acc hAcc
      simpa [__re_split_str_to_re] using hTail acc hAcc

theorem StrInReConsumeInternal.re_rev_map_rev_list_concat_rec_ne_stuck_local
    (x z acc : Term)
    (hXList :
      __eo_is_list (Term.UOp UserOp.re_concat) x = Term.Boolean true)
    (hXRev : __re_rev_map_rev x acc ≠ Term.Stuck)
    (hZRev :
      ∀ acc, acc ≠ Term.Stuck ->
        __re_rev_map_rev z acc ≠ Term.Stuck)
    (hConcat : __eo_list_concat_rec x z ≠ Term.Stuck)
    (hAcc : acc ≠ Term.Stuck) :
    __re_rev_map_rev (__eo_list_concat_rec x z) acc ≠ Term.Stuck := by
  induction x, z using __eo_list_concat_rec.induct generalizing acc with
  | case1 z =>
      cases (Term.UOp UserOp.re_concat) <;>
        simp [__eo_is_list] at hXList
  | case2 x hXNe =>
      simp [__eo_list_concat_rec] at hConcat
  | case3 f head tail z hZNe ih =>
      have hf : f = Term.UOp UserOp.re_concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.re_concat) f head tail hXList
      subst f
      have hTailList :
          __eo_is_list (Term.UOp UserOp.re_concat) tail =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.re_concat) head tail hXList
      have hTailConcatNe :
          __eo_list_concat_rec tail z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.re_concat) tail z hTailList hZNe
      let newAcc :=
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat)
            (__re_rev_comp head)) acc
      have hOrigEq :
          __re_rev_map_rev
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head)
                tail) acc =
            __re_rev_map_rev tail newAcc := by
        simpa [newAcc] using __re_rev_map_rev.eq_3 acc head tail hAcc
      have hTailRev :
          __re_rev_map_rev tail newAcc ≠ Term.Stuck := by
        simpa [hOrigEq] using hXRev
      have hNewAccNe : newAcc ≠ Term.Stuck :=
        StrInReConsumeInternal.re_rev_map_rev_acc_ne_stuck_of_ne_stuck_local tail newAcc
          hTailRev
      have hTailConcatRev :
          __re_rev_map_rev (__eo_list_concat_rec tail z) newAcc ≠
            Term.Stuck :=
        ih newAcc hTailList hTailRev hZRev hTailConcatNe hNewAccNe
      have hConcatEq :
          __eo_list_concat_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head)
                tail) z =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head)
              (__eo_list_concat_rec tail z) :=
        eo_list_concat_rec_cons_eq_of_tail_ne_stuck
          (Term.UOp UserOp.re_concat) head tail z hTailConcatNe
      have hRevEq :
          __re_rev_map_rev
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head)
                (__eo_list_concat_rec tail z)) acc =
            __re_rev_map_rev (__eo_list_concat_rec tail z) newAcc := by
        simpa [newAcc] using
          __re_rev_map_rev.eq_3 acc head (__eo_list_concat_rec tail z)
            hAcc
      simpa [hConcatEq, hRevEq] using hTailConcatRev
  | case4 nil z hNilNe hZNe hNotCons =>
      simpa [__eo_list_concat_rec] using hZRev acc hAcc

def StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local
    (mode r : Term) : Prop :=
  __re_flatten mode r ≠ Term.Stuck ->
    match mode with
    | Term.Boolean true =>
        ∀ acc, acc ≠ Term.Stuck ->
          __re_rev_map_rev (__re_flatten mode r) acc ≠ Term.Stuck
    | Term.Boolean false =>
        __re_rev_comp (__re_flatten mode r) ≠ Term.Stuck
    | _ => True

theorem StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_local :
    ∀ mode r, StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local mode r := by
  intro mode r
  induction mode, r using __re_flatten.induct with
  | case1 x =>
      intro hFlatNe
      exfalso
      exact hFlatNe (by simp [__re_flatten])
  | case2 =>
      intro _hFlatNe acc hAcc
      simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local,
        __re_flatten, __re_rev_map_rev] using hAcc
  | case3 s b ih =>
      intro hFlatNe acc hAcc
      let parts :=
        __str_flatten
          (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s)
      let flatB := __re_flatten (Term.Boolean true) b
      have hSplitNe : __re_split_str_to_re parts flatB ≠ Term.Stuck := by
        simpa [__re_flatten, parts, flatB] using hFlatNe
      have hFlatBNe : flatB ≠ Term.Stuck :=
        StrInReConsumeInternal.re_split_str_to_re_tail_ne_stuck_local parts flatB hSplitNe
      have hTail :
          ∀ acc, acc ≠ Term.Stuck ->
            __re_rev_map_rev flatB acc ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatB]
          using ih hFlatBNe
      simpa [__re_flatten, parts, flatB] using
        StrInReConsumeInternal.re_split_str_to_re_rev_map_ne_stuck_local parts flatB
          hTail hSplitNe acc hAcc
  | case4 a a2 b ihX ihB =>
      intro hFlatNe acc hAcc
      let flatX :=
        __re_flatten (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) a2)
      let flatB := __re_flatten (Term.Boolean true) b
      have hConcatNe :
          __eo_list_concat (Term.UOp UserOp.re_concat) flatX flatB ≠
            Term.Stuck := by
        simpa [__re_flatten, flatX, flatB] using hFlatNe
      have hDef :
          __eo_list_concat (Term.UOp UserOp.re_concat) flatX flatB =
            __eo_requires
              (__eo_is_list (Term.UOp UserOp.re_concat) flatX)
              (Term.Boolean true)
              (__eo_requires
                (__eo_is_list (Term.UOp UserOp.re_concat) flatB)
                (Term.Boolean true)
                (__eo_list_concat_rec flatX flatB)) := rfl
      have hReq0 :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.re_concat) flatX)
              (Term.Boolean true)
              (__eo_requires
                (__eo_is_list (Term.UOp UserOp.re_concat) flatB)
                (Term.Boolean true)
                (__eo_list_concat_rec flatX flatB)) ≠
            Term.Stuck := by
        rw [← hDef]
        exact hConcatNe
      have hXList :
          __eo_is_list (Term.UOp UserOp.re_concat) flatX =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck _ _ _ hReq0
      have hOuterEq :=
        eo_requires_eq_result_of_ne_stuck _ _ _ hReq0
      have hReq1 :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.re_concat) flatB)
              (Term.Boolean true)
              (__eo_list_concat_rec flatX flatB) ≠ Term.Stuck := by
        rw [← hOuterEq]
        exact hReq0
      have hBList :
          __eo_is_list (Term.UOp UserOp.re_concat) flatB =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck _ _ _ hReq1
      have hInnerEq :=
        eo_requires_eq_result_of_ne_stuck _ _ _ hReq1
      have hRecNe : __eo_list_concat_rec flatX flatB ≠ Term.Stuck := by
        rw [← hInnerEq]
        exact hReq1
      have hWhole :
          __eo_list_concat (Term.UOp UserOp.re_concat) flatX flatB =
            __eo_list_concat_rec flatX flatB := by
        rw [hDef, hOuterEq, hInnerEq]
      have hFlatXNe : flatX ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hXList
        simp [__eo_is_list] at hXList
      have hFlatBNe : flatB ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hBList
        simp [__eo_is_list] at hBList
      have hXRev :
          __re_rev_map_rev flatX acc ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatX]
          using ihX hFlatXNe acc hAcc
      have hBRev :
          ∀ acc, acc ≠ Term.Stuck ->
            __re_rev_map_rev flatB acc ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatB]
          using ihB hFlatBNe
      rw [show __re_flatten (Term.Boolean true)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
                  a2)) b) =
          __eo_list_concat (Term.UOp UserOp.re_concat) flatX flatB by
        simp [__re_flatten, flatX, flatB]]
      rw [hWhole]
      exact StrInReConsumeInternal.re_rev_map_rev_list_concat_rec_ne_stuck_local flatX flatB
        acc hXList hXRev hBRev hRecNe hAcc
  | case5 a b hNotStr hNotNested ihA ihB =>
      intro hFlatNe acc hAcc
      let flatA := __re_flatten (Term.Boolean false) a
      let flatB := __re_flatten (Term.Boolean true) b
      have hOutNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) flatA)
              flatB ≠ Term.Stuck := by
        simpa [__re_flatten, flatA, flatB] using hFlatNe
      have hInnerNe :
          __eo_mk_apply (Term.UOp UserOp.re_concat) flatA ≠
            Term.Stuck :=
        eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
      have hFlatANe : flatA ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
      have hFlatBNe : flatB ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOutNe
      have hHeadComp : __re_rev_comp flatA ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatA]
          using ihA hFlatANe
      have hTail :
          ∀ acc, acc ≠ Term.Stuck ->
            __re_rev_map_rev flatB acc ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatB]
          using ihB hFlatBNe
      let newAcc :=
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat)
            (__re_rev_comp flatA)) acc
      have hInnerNewNe :
          __eo_mk_apply (Term.UOp UserOp.re_concat)
              (__re_rev_comp flatA) ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (Term.UOp UserOp.re_concat) (__re_rev_comp flatA)
          (by simp) hHeadComp
      have hNewAccNe : newAcc ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (__eo_mk_apply (Term.UOp UserOp.re_concat)
            (__re_rev_comp flatA)) acc hInnerNewNe hAcc
      rw [show __re_flatten (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) =
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_concat) flatA)
            flatB by
        simp [__re_flatten, flatA, flatB]]
      rw [StrInReConsumeInternal.re_rev_map_rev_mk_concat_eq_local flatA flatB acc hOutNe hAcc]
      exact hTail newAcc hNewAccNe
  | case6 s hNotEmpty =>
      intro hFlatNe acc hAcc
      let parts :=
        __str_flatten
          (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s)
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      have hSplitNe : __re_split_str_to_re parts eps ≠ Term.Stuck := by
        simpa [__re_flatten, parts, eps] using hFlatNe
      have hTail :
          ∀ acc, acc ≠ Term.Stuck ->
            __re_rev_map_rev eps acc ≠ Term.Stuck := by
        intro acc hAcc
        simpa [eps, __re_rev_map_rev] using hAcc
      simpa [__re_flatten, parts, eps] using
        StrInReConsumeInternal.re_split_str_to_re_rev_map_ne_stuck_local parts eps hTail
          hSplitNe acc hAcc
  | case7 c hCNe hEmpty hConcatStr hNested hConcat hStr ih =>
      intro hFlatNe acc hAcc
      let flatC := __re_flatten (Term.Boolean false) c
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      have hOutNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat) flatC)
              eps ≠ Term.Stuck := by
        simpa [__re_flatten, flatC, eps] using hFlatNe
      have hInnerNe :
          __eo_mk_apply (Term.UOp UserOp.re_concat) flatC ≠
            Term.Stuck :=
        eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
      have hFlatCNe : flatC ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
      have hHeadComp : __re_rev_comp flatC ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatC]
          using ih hFlatCNe
      let newAcc :=
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat)
            (__re_rev_comp flatC)) acc
      have hInnerNewNe :
          __eo_mk_apply (Term.UOp UserOp.re_concat)
              (__re_rev_comp flatC) ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (Term.UOp UserOp.re_concat) (__re_rev_comp flatC)
          (by simp) hHeadComp
      have hNewAccNe : newAcc ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (__eo_mk_apply (Term.UOp UserOp.re_concat)
            (__re_rev_comp flatC)) acc hInnerNewNe hAcc
      have hTail :
          __re_rev_map_rev eps newAcc ≠ Term.Stuck := by
        simpa [eps, __re_rev_map_rev] using hNewAccNe
      rw [show __re_flatten (Term.Boolean true) c =
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_concat) flatC)
            eps by
        simp [__re_flatten, flatC, eps]]
      rw [StrInReConsumeInternal.re_rev_map_rev_mk_concat_eq_local flatC eps acc hOutNe hAcc]
      exact hTail
  | case8 =>
      intro _hFlatNe
      change
        __re_rev_comp
            (__re_flatten (Term.Boolean false) (Term.UOp UserOp.re_all)) ≠
          Term.Stuck
      simp [__re_flatten, __re_rev_comp]
  | case9 =>
      intro _hFlatNe
      change
        __re_rev_comp
            (__re_flatten (Term.Boolean false) (Term.UOp UserOp.re_none)) ≠
          Term.Stuck
      simp [__re_flatten, __re_rev_comp]
  | case10 body ih =>
      intro hFlatNe
      let flatBody := __re_flatten (Term.Boolean true) body
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      have hOutNe :
          __eo_mk_apply (Term.UOp UserOp.re_mult) flatBody ≠
            Term.Stuck := by
        simpa [__re_flatten, flatBody] using hFlatNe
      have hFlatBodyNe : flatBody ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOutNe
      have hBodyRev :
          ∀ acc, acc ≠ Term.Stuck ->
            __re_rev_map_rev flatBody acc ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatBody]
          using ih hFlatBodyNe
      have hBodyRevEps :
          __re_rev_map_rev flatBody eps ≠ Term.Stuck :=
        hBodyRev eps (by simp [eps])
      have hRevOutNe :
          __eo_mk_apply (Term.UOp UserOp.re_mult)
              (__re_rev_map_rev flatBody eps) ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (Term.UOp UserOp.re_mult) (__re_rev_map_rev flatBody eps)
          (by simp) hBodyRevEps
      have hOutEq :
          __eo_mk_apply (Term.UOp UserOp.re_mult) flatBody =
            Term.Apply (Term.UOp UserOp.re_mult) flatBody :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.UOp UserOp.re_mult) flatBody hOutNe
      rw [show __re_flatten (Term.Boolean false)
            (Term.Apply (Term.UOp UserOp.re_mult) body) =
          __eo_mk_apply (Term.UOp UserOp.re_mult) flatBody by
        simp [__re_flatten, flatBody]]
      rw [hOutEq]
      simpa [__re_rev_comp, eps] using hRevOutNe
  | case11 c1 c2 ih1 ih2 =>
      intro hFlatNe
      let flatC1 := __re_flatten (Term.Boolean true) c1
      let flatC2 := __re_flatten (Term.Boolean false) c2
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      have hOutNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_inter) flatC1)
              flatC2 ≠ Term.Stuck := by
        simpa [__re_flatten, flatC1, flatC2] using hFlatNe
      have hInnerNe :
          __eo_mk_apply (Term.UOp UserOp.re_inter) flatC1 ≠
            Term.Stuck :=
        eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
      have hFlatC1Ne : flatC1 ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
      have hFlatC2Ne : flatC2 ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOutNe
      have hLeftRevAll :
          ∀ acc, acc ≠ Term.Stuck ->
            __re_rev_map_rev flatC1 acc ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatC1]
          using ih1 hFlatC1Ne
      have hLeftRev :
          __re_rev_map_rev flatC1 eps ≠ Term.Stuck :=
        hLeftRevAll eps (by simp [eps])
      have hRightComp : __re_rev_comp flatC2 ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatC2]
          using ih2 hFlatC2Ne
      let left := __re_rev_map_rev flatC1 eps
      let right := __re_rev_comp flatC2
      let inner := __eo_mk_apply (Term.UOp UserOp.re_inter) left
      let outer := __eo_mk_apply inner right
      have hRevInnerNe : inner ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (Term.UOp UserOp.re_inter) left (by simp)
          (by simpa [left] using hLeftRev)
      have hRevOuterNe : outer ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local inner right hRevInnerNe
          (by simpa [right] using hRightComp)
      have hOutEq :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_inter) flatC1)
              flatC2 =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) flatC1)
              flatC2 := by
        have hInnerEq :
            __eo_mk_apply (Term.UOp UserOp.re_inter) flatC1 =
              Term.Apply (Term.UOp UserOp.re_inter) flatC1 :=
          eo_mk_apply_eq_apply_of_ne_stuck
            (Term.UOp UserOp.re_inter) flatC1 hInnerNe
        have hOuterEq :=
          eo_mk_apply_eq_apply_of_ne_stuck
            (__eo_mk_apply (Term.UOp UserOp.re_inter) flatC1)
            flatC2 hOutNe
        rw [hOuterEq, hInnerEq]
      rw [show __re_flatten (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) =
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_inter) flatC1) flatC2 by
        simp [__re_flatten, flatC1, flatC2]]
      rw [hOutEq]
      simpa [__re_rev_comp, eps, left, right, inner, outer] using
        hRevOuterNe
  | case12 c1 c2 ih1 ih2 =>
      intro hFlatNe
      let flatC1 := __re_flatten (Term.Boolean true) c1
      let flatC2 := __re_flatten (Term.Boolean false) c2
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      have hOutNe :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_union) flatC1)
              flatC2 ≠ Term.Stuck := by
        simpa [__re_flatten, flatC1, flatC2] using hFlatNe
      have hInnerNe :
          __eo_mk_apply (Term.UOp UserOp.re_union) flatC1 ≠
            Term.Stuck :=
        eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
      have hFlatC1Ne : flatC1 ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
      have hFlatC2Ne : flatC2 ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOutNe
      have hLeftRevAll :
          ∀ acc, acc ≠ Term.Stuck ->
            __re_rev_map_rev flatC1 acc ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatC1]
          using ih1 hFlatC1Ne
      have hLeftRev :
          __re_rev_map_rev flatC1 eps ≠ Term.Stuck :=
        hLeftRevAll eps (by simp [eps])
      have hRightComp : __re_rev_comp flatC2 ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local, flatC2]
          using ih2 hFlatC2Ne
      let left := __re_rev_map_rev flatC1 eps
      let right := __re_rev_comp flatC2
      let inner := __eo_mk_apply (Term.UOp UserOp.re_union) left
      let outer := __eo_mk_apply inner right
      have hRevInnerNe : inner ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local
          (Term.UOp UserOp.re_union) left (by simp)
          (by simpa [left] using hLeftRev)
      have hRevOuterNe : outer ≠ Term.Stuck :=
        StrInReConsumeInternal.eo_mk_apply_ne_stuck_of_args_local inner right hRevInnerNe
          (by simpa [right] using hRightComp)
      have hOutEq :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_union) flatC1)
              flatC2 =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_union) flatC1)
              flatC2 := by
        have hInnerEq :
            __eo_mk_apply (Term.UOp UserOp.re_union) flatC1 =
              Term.Apply (Term.UOp UserOp.re_union) flatC1 :=
          eo_mk_apply_eq_apply_of_ne_stuck
            (Term.UOp UserOp.re_union) flatC1 hInnerNe
        have hOuterEq :=
          eo_mk_apply_eq_apply_of_ne_stuck
            (__eo_mk_apply (Term.UOp UserOp.re_union) flatC1)
            flatC2 hOutNe
        rw [hOuterEq, hInnerEq]
      rw [show __re_flatten (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) =
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_union) flatC1) flatC2 by
        simp [__re_flatten, flatC1, flatC2]]
      rw [hOutEq]
      simpa [__re_rev_comp, eps, left, right, inner, outer] using
        hRevOuterNe
  | case13 c hCNe hAll hNone hMult hInter hUnion =>
      intro hFlatNe
      simpa [StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_motive_local,
        __re_flatten, __re_rev_comp] using hFlatNe
  | case14 x x_1 hTreeNe hEmpty hConcatStr hNested hConcat
      hStr hTrue hAll hNone hMult hInter hUnion hFalse =>
      intro _hFlatNe
      cases x <;> try trivial
      case Boolean b =>
        cases b
        · exact False.elim (hFalse rfl)
        · exact False.elim (hTrue rfl)

theorem StrInReConsumeInternal.re_flatten_true_action_rev_ne_stuck_local
    (r acc : Term)
    (hFlat : __re_flatten (Term.Boolean true) r ≠ Term.Stuck)
    (hAcc : acc ≠ Term.Stuck) :
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r) acc ≠
      Term.Stuck :=
  (StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_local (Term.Boolean true) r)
    hFlat acc hAcc

theorem StrInReConsumeInternal.re_flatten_false_rev_comp_ne_stuck_local
    (r : Term)
    (hFlat : __re_flatten (Term.Boolean false) r ≠ Term.Stuck) :
    __re_rev_comp (__re_flatten (Term.Boolean false) r) ≠ Term.Stuck :=
  (StrInReConsumeInternal.re_flatten_action_reverse_ne_stuck_local (Term.Boolean false) r) hFlat

theorem StrInReConsumeInternal.re_flatten_true_action_double_eps_local
    (r : Term)
    (hFlat : __re_flatten (Term.Boolean true) r ≠ Term.Stuck) :
    __re_rev_map_rev
        (__re_rev_map_rev (__re_flatten (Term.Boolean true) r)
          StrInReConsumeInternal.re_empty_string_re_consume_local)
        StrInReConsumeInternal.re_empty_string_re_consume_local =
      __re_flatten (Term.Boolean true) r :=
  StrInReConsumeInternal.re_rev_map_rev_action_double_eps_local
    (__re_flatten (Term.Boolean true) r)
    (StrInReConsumeInternal.re_flatten_true_action_rev_ne_stuck_local r
      StrInReConsumeInternal.re_empty_string_re_consume_local hFlat
      (by simp [StrInReConsumeInternal.re_empty_string_re_consume_local]))

theorem StrInReConsumeInternal.eval_re_flatten_action_double_rev_reglan_rel_consume_local
    (M : SmtModel) (r : Term) (rv : SmtRegLan)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt (__re_flatten (Term.Boolean true) r)) =
        SmtValue.RegLan rv)
    (hFlat : __re_flatten (Term.Boolean true) r ≠ Term.Stuck) :
    ∃ revRevRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_rev_map_rev (__re_flatten (Term.Boolean true) r)
                StrInReConsumeInternal.re_empty_string_re_consume_local)
              StrInReConsumeInternal.re_empty_string_re_consume_local)) =
        SmtValue.RegLan revRevRv ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan revRevRv)
        (SmtValue.RegLan rv) :=
  StrInReConsumeInternal.eval_re_action_double_rev_reglan_rel_consume_local M
    (__re_flatten (Term.Boolean true) r) rv hEval
    (StrInReConsumeInternal.re_flatten_true_action_rev_ne_stuck_local r
      StrInReConsumeInternal.re_empty_string_re_consume_local hFlat
      (by simp [StrInReConsumeInternal.re_empty_string_re_consume_local]))

theorem StrInReConsumeInternal.re_rev_map_rev_mk_mult_eq_stuck_local
    (body acc : Term) :
    __re_rev_map_rev (__eo_mk_apply (Term.UOp UserOp.re_mult) body) acc =
      Term.Stuck := by
  by_cases hMk : __eo_mk_apply (Term.UOp UserOp.re_mult) body = Term.Stuck
  · rw [hMk]
    cases acc <;> simp [__re_rev_map_rev]
  · have hMkEq :
        __eo_mk_apply (Term.UOp UserOp.re_mult) body =
          Term.Apply (Term.UOp UserOp.re_mult) body :=
      eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.re_mult) body hMk
    rw [hMkEq]
    cases acc <;> simp [__re_rev_map_rev]

theorem StrInReConsumeInternal.re_rev_map_rev_mk_inter_eq_stuck_local
    (a b acc : Term) :
    __re_rev_map_rev
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_inter) a) b)
        acc =
      Term.Stuck := by
  let inner := __eo_mk_apply (Term.UOp UserOp.re_inter) a
  by_cases hMk : __eo_mk_apply inner b = Term.Stuck
  · change __re_rev_map_rev (__eo_mk_apply inner b) acc = Term.Stuck
    rw [hMk]
    cases acc <;> simp [__re_rev_map_rev]
  · have hInnerNe : inner ≠ Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck inner b hMk
    have hInnerEq :
        inner = Term.Apply (Term.UOp UserOp.re_inter) a :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.UOp UserOp.re_inter) a hInnerNe
    have hMkEq :
        __eo_mk_apply inner b =
          Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b := by
      rw [eo_mk_apply_eq_apply_of_ne_stuck inner b hMk, hInnerEq]
    change __re_rev_map_rev (__eo_mk_apply inner b) acc = Term.Stuck
    rw [hMkEq]
    cases acc <;> simp [__re_rev_map_rev]

theorem StrInReConsumeInternal.re_rev_map_rev_mk_union_eq_stuck_local
    (a b acc : Term) :
    __re_rev_map_rev
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.re_union) a) b)
        acc =
      Term.Stuck := by
  let inner := __eo_mk_apply (Term.UOp UserOp.re_union) a
  by_cases hMk : __eo_mk_apply inner b = Term.Stuck
  · change __re_rev_map_rev (__eo_mk_apply inner b) acc = Term.Stuck
    rw [hMk]
    cases acc <;> simp [__re_rev_map_rev]
  · have hInnerNe : inner ≠ Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck inner b hMk
    have hInnerEq :
        inner = Term.Apply (Term.UOp UserOp.re_union) a :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.UOp UserOp.re_union) a hInnerNe
    have hMkEq :
        __eo_mk_apply inner b =
          Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b := by
      rw [eo_mk_apply_eq_apply_of_ne_stuck inner b hMk, hInnerEq]
    change __re_rev_map_rev (__eo_mk_apply inner b) acc = Term.Stuck
    rw [hMkEq]
    cases acc <;> simp [__re_rev_map_rev]

def StrInReConsumeInternal.re_rev_map_rev_type_motive_local (a acc : Term) : Prop :=
  __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ->
    __eo_is_list (Term.UOp UserOp.re_concat) acc =
        Term.Boolean true ->
    __smtx_typeof (__eo_to_smt acc) = SmtType.RegLan ->
    __re_rev_map_rev a acc ≠ Term.Stuck ->
    __eo_is_list (Term.UOp UserOp.re_concat) a =
        Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt (__re_rev_map_rev a acc)) =
        SmtType.RegLan ∧
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__re_rev_map_rev a acc) =
        Term.Boolean true

def StrInReConsumeInternal.re_rev_comp_type_motive_local (c : Term) : Prop :=
  __smtx_typeof (__eo_to_smt c) = SmtType.RegLan ->
    __re_rev_comp c ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (__re_rev_comp c)) = SmtType.RegLan

theorem StrInReConsumeInternal.re_rev_map_rev_extend_acc_type_facts_local
    (head acc : Term)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.RegLan)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.re_concat) acc =
        Term.Boolean true)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.RegLan)
    (hMk :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat) head) acc ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_concat) head) acc)) =
        SmtType.RegLan ∧
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_concat) head) acc) =
        Term.Boolean true := by
  let inner := __eo_mk_apply (Term.UOp UserOp.re_concat) head
  have hInnerNe : inner ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck inner acc (by
      simpa [inner] using hMk)
  have hInnerEq :
      inner = Term.Apply (Term.UOp UserOp.re_concat) head :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.re_concat) head hInnerNe
  have hMkEq :
      __eo_mk_apply inner acc =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) acc := by
    rw [eo_mk_apply_eq_apply_of_ne_stuck inner acc (by
      simpa [inner] using hMk), hInnerEq]
  constructor
  · rw [show __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat) head) acc =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) acc by
          simpa [inner] using hMkEq]
    exact smt_typeof_re_concat_of_reglan_consume_local head acc
      hHeadTy hAccTy
  · rw [show __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat) head) acc =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) acc by
          simpa [inner] using hMkEq]
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_concat) head acc (by simp) hAccList

theorem StrInReConsumeInternal.re_rev_map_rev_comp_type_facts_local :
    (∀ a acc, StrInReConsumeInternal.re_rev_map_rev_type_motive_local a acc) ∧
      (∀ c, StrInReConsumeInternal.re_rev_comp_type_motive_local c) := by
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  have hEpsList :
      __eo_is_list (Term.UOp UserOp.re_concat) eps = Term.Boolean true := by
    simpa [eps] using StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
  have hEpsTy : __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan := by
    simpa [eps] using StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local
  have case1 :
      ∀ t, StrInReConsumeInternal.re_rev_map_rev_type_motive_local t Term.Stuck := by
    intro t _hTy _hAccList _hAccTy hRev
    exfalso
    exact hRev (__re_rev_map_rev.eq_1 t)
  have case2 :
      ∀ acc, (acc = Term.Stuck -> False) ->
        StrInReConsumeInternal.re_rev_map_rev_type_motive_local eps acc := by
    intro acc hAccNe hTy hAccList hAccTy _hRev
    constructor
    · simpa [eps] using StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
    · constructor
      · simpa [eps, __re_rev_map_rev.eq_2 acc hAccNe] using hAccTy
      · simpa [eps, __re_rev_map_rev.eq_2 acc hAccNe] using hAccList
  have case3 :
      ∀ a b acc,
        (acc = Term.Stuck -> False) ->
        StrInReConsumeInternal.re_rev_comp_type_motive_local a ->
        StrInReConsumeInternal.re_rev_map_rev_type_motive_local b
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_concat)
              (__re_rev_comp a)) acc) ->
        StrInReConsumeInternal.re_rev_map_rev_type_motive_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)
          acc := by
    intro a b acc hAccNe ihComp ihTail hConcatTy hAccList hAccTy hRev
    let compA := __re_rev_comp a
    let newAcc :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_concat) compA) acc
    have hRevEq :
        __re_rev_map_rev
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)
            acc =
          __re_rev_map_rev b newAcc := by
      simpa [compA, newAcc] using
        __re_rev_map_rev.eq_3 acc a b hAccNe
    have hTailRev : __re_rev_map_rev b newAcc ≠ Term.Stuck := by
      intro hBad
      exact hRev (by simpa [hRevEq] using hBad)
    have hArgs := StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local a b hConcatTy
    have hNewAccNe : newAcc ≠ Term.Stuck :=
      StrInReConsumeInternal.re_rev_map_rev_acc_ne_stuck_of_ne_stuck_local b newAcc hTailRev
    have hInnerNe :
        __eo_mk_apply (Term.UOp UserOp.re_concat) compA ≠ Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.re_concat) compA) acc
        (by simpa [newAcc] using hNewAccNe)
    have hCompNe : compA ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.re_concat) compA hInnerNe
    have hCompTy : __smtx_typeof (__eo_to_smt compA) = SmtType.RegLan :=
      ihComp hArgs.1 (by simpa [compA] using hCompNe)
    rcases StrInReConsumeInternal.re_rev_map_rev_extend_acc_type_facts_local compA acc
        hCompTy hAccList hAccTy (by simpa [compA, newAcc] using hNewAccNe) with
      ⟨hNewAccTy, hNewAccList⟩
    rcases ihTail hArgs.2 (by simpa [newAcc] using hNewAccList)
        (by simpa [newAcc] using hNewAccTy) hTailRev with
      ⟨hBList, hTailTy, hTailList⟩
    constructor
    · exact eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.re_concat) a b (by simp) hBList
    · constructor
      · simpa [hRevEq] using hTailTy
      · simpa [hRevEq] using hTailList
  have case4 :
      ∀ t x,
        (x = Term.Stuck -> False) ->
        (t = eps -> False) ->
        (∀ a b,
          t = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
            False) ->
        StrInReConsumeInternal.re_rev_map_rev_type_motive_local t x := by
    intro t x hXNe hNotEps hNotConcat _hTy _hList _hAccTy hRev
    exfalso
    exact hRev (by
      simpa [eps] using
        __re_rev_map_rev.eq_4 t x (by simpa [eps] using hNotEps)
          hNotConcat hXNe)
  have case5 : StrInReConsumeInternal.re_rev_comp_type_motive_local Term.Stuck := by
    intro _hTy hRev
    exfalso
    exact hRev __re_rev_comp.eq_1
  have case6 : StrInReConsumeInternal.re_rev_comp_type_motive_local (Term.UOp UserOp.re_all) := by
    intro hTy _hRev
    simpa [__re_rev_comp.eq_2] using hTy
  have case7 : StrInReConsumeInternal.re_rev_comp_type_motive_local (Term.UOp UserOp.re_none) := by
    intro hTy _hRev
    simpa [__re_rev_comp.eq_3] using hTy
  have case8 :
      ∀ body,
        StrInReConsumeInternal.re_rev_map_rev_type_motive_local body eps ->
        StrInReConsumeInternal.re_rev_comp_type_motive_local
          (Term.Apply (Term.UOp UserOp.re_mult) body) := by
    intro body ihBody hTy hRev
    let mapped := __re_rev_map_rev body eps
    have hBodyTy : __smtx_typeof (__eo_to_smt body) = SmtType.RegLan :=
      StrInReConsumeInternal.re_mult_arg_type_of_reglan_consume_local body hTy
    have hCompEq :
        __re_rev_comp (Term.Apply (Term.UOp UserOp.re_mult) body) =
          __eo_mk_apply (Term.UOp UserOp.re_mult) mapped := by
      simpa [eps, mapped] using __re_rev_comp.eq_4 body
    have hMkNe :
        __eo_mk_apply (Term.UOp UserOp.re_mult) mapped ≠ Term.Stuck := by
      intro hBad
      exact hRev (by simpa [hCompEq] using hBad)
    have hMappedNe : mapped ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.re_mult) mapped hMkNe
    rcases ihBody hBodyTy hEpsList hEpsTy (by
        simpa [mapped] using hMappedNe) with
      ⟨_hBodyList, hMappedTy, _hMappedList⟩
    have hMkEq :
        __eo_mk_apply (Term.UOp UserOp.re_mult) mapped =
          Term.Apply (Term.UOp UserOp.re_mult) mapped :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.UOp UserOp.re_mult) mapped hMkNe
    rw [hCompEq, hMkEq]
    exact smt_typeof_re_mult_of_reglan_consume_local mapped hMappedTy
  have case9 :
      ∀ c1 c2,
        StrInReConsumeInternal.re_rev_map_rev_type_motive_local c1 eps ->
        StrInReConsumeInternal.re_rev_comp_type_motive_local c2 ->
        StrInReConsumeInternal.re_rev_comp_type_motive_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
    intro c1 c2 ihLeft ihRight hTy hRev
    let left := __re_rev_map_rev c1 eps
    let right := __re_rev_comp c2
    let inner := __eo_mk_apply (Term.UOp UserOp.re_inter) left
    let outer := __eo_mk_apply inner right
    have hArgs := StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2 hTy
    have hCompEq :
        __re_rev_comp
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) =
          outer := by
      simpa [eps, left, right, inner, outer] using
        __re_rev_comp.eq_5 c1 c2
    have hOuterNe : outer ≠ Term.Stuck := by
      intro hBad
      exact hRev (by simpa [hCompEq] using hBad)
    have hInnerNe : inner ≠ Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck inner right hOuterNe
    have hRightNe : right ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck inner right hOuterNe
    have hLeftNe : left ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.re_inter) left hInnerNe
    rcases ihLeft hArgs.1 hEpsList hEpsTy (by
        simpa [left] using hLeftNe) with
      ⟨_hLeftList, hLeftTy, _hLeftOutList⟩
    have hRightTy : __smtx_typeof (__eo_to_smt right) = SmtType.RegLan :=
      ihRight hArgs.2 (by simpa [right] using hRightNe)
    have hInnerEq :
        inner = Term.Apply (Term.UOp UserOp.re_inter) left :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.UOp UserOp.re_inter) left hInnerNe
    have hOuterEq : outer = Term.Apply inner right :=
      eo_mk_apply_eq_apply_of_ne_stuck inner right hOuterNe
    rw [hCompEq, hOuterEq, hInnerEq]
    exact smt_typeof_re_inter_of_reglan_consume_local left right
      hLeftTy hRightTy
  have case10 :
      ∀ c1 c2,
        StrInReConsumeInternal.re_rev_map_rev_type_motive_local c1 eps ->
        StrInReConsumeInternal.re_rev_comp_type_motive_local c2 ->
        StrInReConsumeInternal.re_rev_comp_type_motive_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
    intro c1 c2 ihLeft ihRight hTy hRev
    let left := __re_rev_map_rev c1 eps
    let right := __re_rev_comp c2
    let inner := __eo_mk_apply (Term.UOp UserOp.re_union) left
    let outer := __eo_mk_apply inner right
    have hArgs := StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2 hTy
    have hCompEq :
        __re_rev_comp
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) =
          outer := by
      simpa [eps, left, right, inner, outer] using
        __re_rev_comp.eq_6 c1 c2
    have hOuterNe : outer ≠ Term.Stuck := by
      intro hBad
      exact hRev (by simpa [hCompEq] using hBad)
    have hInnerNe : inner ≠ Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck inner right hOuterNe
    have hRightNe : right ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck inner right hOuterNe
    have hLeftNe : left ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.re_union) left hInnerNe
    rcases ihLeft hArgs.1 hEpsList hEpsTy (by
        simpa [left] using hLeftNe) with
      ⟨_hLeftList, hLeftTy, _hLeftOutList⟩
    have hRightTy : __smtx_typeof (__eo_to_smt right) = SmtType.RegLan :=
      ihRight hArgs.2 (by simpa [right] using hRightNe)
    have hInnerEq :
        inner = Term.Apply (Term.UOp UserOp.re_union) left :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.UOp UserOp.re_union) left hInnerNe
    have hOuterEq : outer = Term.Apply inner right :=
      eo_mk_apply_eq_apply_of_ne_stuck inner right hOuterNe
    rw [hCompEq, hOuterEq, hInnerEq]
    exact smt_typeof_re_union_of_reglan_consume_local left right
      hLeftTy hRightTy
  have case11 :
      ∀ c,
        (c = Term.Stuck -> False) ->
        (c = Term.UOp UserOp.re_all -> False) ->
        (c = Term.UOp UserOp.re_none -> False) ->
        (∀ body, c = Term.Apply (Term.UOp UserOp.re_mult) body ->
          False) ->
        (∀ c1 c2,
          c = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
            False) ->
        (∀ c1 c2,
          c = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
            False) ->
        StrInReConsumeInternal.re_rev_comp_type_motive_local c := by
    intro c hNe hNotAll hNotNone hNotMult hNotInter hNotUnion hTy _hRev
    have hCompEq : __re_rev_comp c = c :=
      __re_rev_comp.eq_7 c hNe hNotAll hNotNone hNotMult hNotInter
        hNotUnion
    simpa [hCompEq] using hTy
  constructor
  · intro a acc
    exact __re_rev_map_rev.induct
      StrInReConsumeInternal.re_rev_map_rev_type_motive_local
      StrInReConsumeInternal.re_rev_comp_type_motive_local
      case1 case2 case3 case4 case5 case6 case7 case8 case9 case10
      case11 a acc
  · intro c
    exact __re_rev_comp.induct
      StrInReConsumeInternal.re_rev_map_rev_type_motive_local
      StrInReConsumeInternal.re_rev_comp_type_motive_local
      case1 case2 case3 case4 case5 case6 case7 case8 case9 case10
      case11 c

theorem StrInReConsumeInternal.re_rev_map_rev_type_facts_local
    (a acc : Term)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.re_concat) acc =
        Term.Boolean true)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.RegLan)
    (hRev : __re_rev_map_rev a acc ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.re_concat) a =
        Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt (__re_rev_map_rev a acc)) =
        SmtType.RegLan ∧
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__re_rev_map_rev a acc) =
        Term.Boolean true := by
  exact StrInReConsumeInternal.re_rev_map_rev_comp_type_facts_local.1 a acc hATy hAccList
    hAccTy hRev

theorem StrInReConsumeInternal.re_rev_comp_type_local
    (c : Term)
    (hTy : __smtx_typeof (__eo_to_smt c) = SmtType.RegLan)
    (hRev : __re_rev_comp c ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__re_rev_comp c)) = SmtType.RegLan := by
  exact StrInReConsumeInternal.re_rev_map_rev_comp_type_facts_local.2 c hTy hRev

theorem StrInReConsumeInternal.re_flatten_true_str_to_re_eval_rel_consume_local
    (M : SmtModel) (hM : model_wf M)
    (s : Term) (ss : SmtSeq)
    (hSTy :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hFlatNe :
      __re_flatten (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.str_to_re) s) ≠
        Term.Stuck) :
    ∃ flatRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_flatten (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.str_to_re) s))) =
        SmtValue.RegLan flatRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_flatten (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.str_to_re) s))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRv)
        (SmtValue.RegLan (native_str_to_re (native_unpack_string ss))) := by
  by_cases hEmpty : s = Term.String []
  · subst s
    have hSSEq : ss = native_pack_string [] := by
      have hEval :
          __smtx_model_eval M (__eo_to_smt (Term.String [])) =
            SmtValue.Seq (native_pack_string []) := by
        change __smtx_model_eval M (SmtTerm.String []) =
          SmtValue.Seq (native_pack_string [])
        rw [__smtx_model_eval.eq_4]
      rw [hEval] at hSEval
      cases hSEval
      rfl
    subst ss
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    have hEpsEval :
        __smtx_model_eval M (__eo_to_smt eps) =
          SmtValue.RegLan (native_str_to_re []) := by
      change __smtx_model_eval M
          (SmtTerm.str_to_re (SmtTerm.String [])) =
        SmtValue.RegLan (native_str_to_re [])
      simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
       ]
    refine ⟨native_str_to_re [], ?_, ?_, ?_⟩
    · simpa [__re_flatten, eps] using hEpsEval
    · simpa [__re_flatten, eps] using StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local
    · simpa [native_unpack_string_pack_string] using
        RuleProofs.smt_value_rel_refl
          (SmtValue.RegLan (native_str_to_re []))
  · let parts := __str_flatten (__str_nary_intro s)
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    have hSplitNe :
        __re_split_str_to_re parts eps ≠ Term.Stuck := by
      simpa [__re_flatten, parts, eps, hEmpty] using hFlatNe
    have hPartsNe : parts ≠ Term.Stuck :=
      StrInReConsumeInternal.re_split_str_to_re_parts_ne_stuck_local parts eps hSplitNe
    rcases str_flatten_nary_intro_eval_rel M hM s ss hSTy hSEval
        (by simpa [parts] using hPartsNe) with
      ⟨partsSs, hPartsEval, hPartsTy, hPartsList, hPartsRel⟩
    have hEpsEval :
        __smtx_model_eval M (__eo_to_smt eps) =
          SmtValue.RegLan (native_str_to_re []) := by
      change __smtx_model_eval M
          (SmtTerm.str_to_re (SmtTerm.String [])) =
        SmtValue.RegLan (native_str_to_re [])
      simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
       ]
    rcases StrInReConsumeInternal.re_split_str_to_re_eval_rel_consume_local M hM parts eps
        partsSs (native_str_to_re []) hPartsList hPartsTy
        (by simpa [parts] using hPartsEval)
        (by simpa [eps] using StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local)
        (by simpa [eps] using hEpsEval)
        (by simpa [parts, eps] using hSplitNe) with
      ⟨flatRv, hFlatEval, hFlatTy, hSplitRel⟩
    have hRightEmpty :
        RuleProofs.smt_value_rel
          (SmtValue.RegLan
            (native_re_concat
              (native_str_to_re (native_unpack_string partsSs))
              (native_str_to_re [])))
          (SmtValue.RegLan
            (native_str_to_re (native_unpack_string partsSs))) := by
      rw [native_re_concat_right_empty_local]
      exact RuleProofs.smt_value_rel_refl
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string partsSs)))
    have hPartsStrRel :
        RuleProofs.smt_value_rel
          (SmtValue.RegLan
            (native_str_to_re (native_unpack_string partsSs)))
          (SmtValue.RegLan
            (native_str_to_re (native_unpack_string ss))) :=
      smt_value_rel_str_to_re_of_seq_rel_consume_local hPartsRel
    refine ⟨flatRv, ?_, ?_, ?_⟩
    · simpa [__re_flatten, parts, eps, hEmpty] using hFlatEval
    · simpa [__re_flatten, parts, eps, hEmpty] using hFlatTy
    · exact RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_trans _ _ _ hSplitRel hRightEmpty)
        hPartsStrRel

theorem StrInReConsumeInternal.re_flatten_true_str_to_re_eval_value_rel_consume_local
    (M : SmtModel) (hM : model_wf M)
    (s : Term) (ss : SmtSeq) (flatRv : SmtRegLan)
    (hSTy :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hFlatNe :
      __re_flatten (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.str_to_re) s) ≠
        Term.Stuck)
    (hFlatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_flatten (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.str_to_re) s))) =
        SmtValue.RegLan flatRv) :
    RuleProofs.smt_value_rel (SmtValue.RegLan flatRv)
      (SmtValue.RegLan (native_str_to_re (native_unpack_string ss))) := by
  rcases StrInReConsumeInternal.re_flatten_true_str_to_re_eval_rel_consume_local M hM s ss
      hSTy hSEval hFlatNe with
    ⟨flatRv0, hFlatEval0, _hFlatTy, hRel⟩
  have hFlatRv : flatRv0 = flatRv := by
    rw [hFlatEval] at hFlatEval0
    cases hFlatEval0
    rfl
  subst flatRv0
  exact hRel

theorem StrInReConsumeInternal.smt_typeof_re_flatten_true_of_reglan_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ (mode r : Term),
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __re_flatten mode r ≠ Term.Stuck ->
      __smtx_typeof
          (__eo_to_smt (__re_flatten mode r)) =
        SmtType.RegLan := by
  intro mode r hTy hFlatNe
  rcases smt_model_eval_reglan_of_type M hM r hTy with
    ⟨rv, hEval⟩
  rcases re_flatten_false_eval_rel M hM mode r rv hTy hEval hFlatNe with
    ⟨_flatRv, _hFlatEval, hFlatTy, _hFlatRel⟩
  exact hFlatTy

theorem StrInReConsumeInternal.str_re_consume_rflat_type_facts_local
    (M : SmtModel) (hM : model_wf M)
    (r : Term)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hRFlatNe :
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ≠
        Term.Stuck) :
    let flat := __re_flatten (Term.Boolean true) r
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let rFlat := __re_rev_map_rev flat eps
    __smtx_typeof (__eo_to_smt rFlat) = SmtType.RegLan ∧
      __eo_is_list (Term.UOp UserOp.re_concat) rFlat = Term.Boolean true ∧
      flat ≠ Term.Stuck ∧
      __eo_is_list (Term.UOp UserOp.re_concat) flat = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt flat) = SmtType.RegLan := by
  let flat := __re_flatten (Term.Boolean true) r
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let rFlat := __re_rev_map_rev flat eps
  have hFlatNe : flat ≠ Term.Stuck :=
    StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local flat eps
      (by simpa [flat, eps, rFlat] using hRFlatNe)
  have hFlatTy :
      __smtx_typeof (__eo_to_smt flat) = SmtType.RegLan := by
    simpa [flat] using
      StrInReConsumeInternal.smt_typeof_re_flatten_true_of_reglan_local M hM
        (Term.Boolean true) r hRTy
        (by simpa [flat] using hFlatNe)
  rcases StrInReConsumeInternal.re_rev_map_rev_type_facts_local flat eps hFlatTy
      (by simpa [eps] using
        StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local)
      (by simpa [eps] using StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local)
      (by simpa [flat, eps, rFlat] using hRFlatNe) with
    ⟨hFlatList, hRFlatTy, hRFlatList⟩
  exact ⟨hRFlatTy, hRFlatList, hFlatNe, hFlatList, hFlatTy⟩

theorem StrInReConsumeInternal.str_re_consume_sflat_eval_facts_local
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSFlatNe :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro s)) ≠
        Term.Stuck) :
    let flat := __str_flatten (__str_nary_intro s)
    let sFlat := __eo_list_rev (Term.UOp UserOp.str_concat) flat
    ∃ ss flatSs sFlatSs,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt flat) = SmtValue.Seq flatSs ∧
      __smtx_model_eval M (__eo_to_smt sFlat) =
        SmtValue.Seq sFlatSs ∧
      __smtx_typeof (__eo_to_smt flat) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt sFlat) = SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat) flat =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sFlat =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
        (SmtValue.Seq ss) := by
  let flat := __str_flatten (__str_nary_intro s)
  let sFlat := __eo_list_rev (Term.UOp UserOp.str_concat) flat
  rcases StrInReConsumeInternal.str_re_consume_sflat_type_facts_local M hM s r side hEqTrans
      (by simpa [flat, sFlat] using hSFlatNe) with
    ⟨hSFlatTy, hSFlatList, hFlatNe, hFlatList, hFlatTy⟩
  rcases str_re_consume_str_flatten_eval_rel M hM s r side hEqTrans
      (by simpa [flat] using hFlatNe) with
    ⟨ss, flatSs, hSEval, hFlatEval, hFlatTy', hFlatList',
      hFlatRel⟩
  have hSFlatEvalTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt sFlat)) =
        SmtType.Seq SmtType.Char := by
    have hPres :
        __smtx_typeof_value
            (__smtx_model_eval M (__eo_to_smt sFlat)) =
          __smtx_typeof (__eo_to_smt sFlat) :=
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt sFlat) (by
          unfold term_has_non_none_type
          rw [hSFlatTy]
          simp)
    rw [hPres, hSFlatTy]
  rcases seq_value_canonical hSFlatEvalTy with
    ⟨sFlatSs, hSFlatEval⟩
  exact ⟨ss, flatSs, sFlatSs, hSEval,
    by simpa [flat] using hFlatEval,
    by simpa [sFlat] using hSFlatEval,
    by simpa [flat] using hFlatTy',
    by simpa [sFlat] using hSFlatTy,
    by simpa [flat] using hFlatList',
    by simpa [sFlat] using hSFlatList,
    hFlatRel⟩

theorem StrInReConsumeInternal.str_re_consume_rflat_eval_facts_local
    (M : SmtModel) (hM : model_wf M)
    (r : Term)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hRFlatNe :
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ≠
        Term.Stuck) :
    let flat := __re_flatten (Term.Boolean true) r
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let rFlat := __re_rev_map_rev flat eps
    ∃ rv flatRv rFlatRv,
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
      __smtx_model_eval M (__eo_to_smt flat) =
        SmtValue.RegLan flatRv ∧
      __smtx_model_eval M (__eo_to_smt rFlat) =
        SmtValue.RegLan rFlatRv ∧
      __smtx_typeof (__eo_to_smt flat) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt rFlat) = SmtType.RegLan ∧
      __eo_is_list (Term.UOp UserOp.re_concat) flat =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_concat) rFlat =
        Term.Boolean true := by
  let flat := __re_flatten (Term.Boolean true) r
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let rFlat := __re_rev_map_rev flat eps
  rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM r hRTy
      (by simpa [flat, eps, rFlat] using hRFlatNe) with
    ⟨hRFlatTy, hRFlatList, _hFlatNe, hFlatList, hFlatTy⟩
  rcases smt_model_eval_reglan_of_type M hM r hRTy with
    ⟨rv, hREval⟩
  rcases smt_model_eval_reglan_of_type M hM flat hFlatTy with
    ⟨flatRv, hFlatEval⟩
  rcases smt_model_eval_reglan_of_type M hM rFlat hRFlatTy with
    ⟨rFlatRv, hRFlatEval⟩
  exact ⟨rv, flatRv, rFlatRv, hREval,
    by simpa [flat] using hFlatEval,
    by simpa [rFlat] using hRFlatEval,
    by simpa [flat] using hFlatTy,
    by simpa [rFlat] using hRFlatTy,
    by simpa [flat] using hFlatList,
    by simpa [rFlat] using hRFlatList⟩

theorem StrInReConsumeInternal.str_re_consume_first_input_eval_context_local
    (M : SmtModel) (hM : model_wf M)
    (s r side rFlatSrc : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hRFlatSrcTy :
      __smtx_typeof (__eo_to_smt rFlatSrc) = SmtType.RegLan)
    (hSFlatNe :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro s)) ≠
        Term.Stuck)
    (hRFlatNe :
      __re_rev_map_rev
          (__re_flatten (Term.Boolean true) rFlatSrc)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ≠
        Term.Stuck) :
    let sFlatSource := __str_flatten (__str_nary_intro s)
    let sFlat := __eo_list_rev (Term.UOp UserOp.str_concat) sFlatSource
    let rFlatSource :=
      __re_flatten (Term.Boolean true) rFlatSrc
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let rFlat := __re_rev_map_rev rFlatSource eps
    ∃ ss flatSs sFlatSs rv flatRv rFlatRv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt sFlatSource) =
        SmtValue.Seq flatSs ∧
      __smtx_model_eval M (__eo_to_smt sFlat) =
        SmtValue.Seq sFlatSs ∧
      __smtx_model_eval M (__eo_to_smt rFlatSrc) =
        SmtValue.RegLan rv ∧
      __smtx_model_eval M (__eo_to_smt rFlatSource) =
        SmtValue.RegLan flatRv ∧
      __smtx_model_eval M (__eo_to_smt rFlat) =
        SmtValue.RegLan rFlatRv ∧
      __smtx_typeof (__eo_to_smt sFlatSource) =
        SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt sFlat) =
        SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt rFlatSource) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt rFlat) = SmtType.RegLan ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sFlatSource =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sFlat =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_concat) rFlatSource =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_concat) rFlat =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
        (SmtValue.Seq ss) := by
  let sFlatSource := __str_flatten (__str_nary_intro s)
  let sFlat := __eo_list_rev (Term.UOp UserOp.str_concat) sFlatSource
  let rFlatSource :=
    __re_flatten (Term.Boolean true) rFlatSrc
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let rFlat := __re_rev_map_rev rFlatSource eps
  rcases StrInReConsumeInternal.str_re_consume_sflat_eval_facts_local M hM s r side hEqTrans
      (by simpa [sFlatSource, sFlat] using hSFlatNe) with
    ⟨ss, flatSs, sFlatSs, hSEval, hSFlatSourceEval, hSFlatEval,
      hSFlatSourceTy, hSFlatTy, hSFlatSourceList, hSFlatList,
      hSFlatSourceRel⟩
  rcases StrInReConsumeInternal.str_re_consume_rflat_eval_facts_local M hM rFlatSrc
      hRFlatSrcTy (by simpa [rFlatSource, eps, rFlat] using hRFlatNe) with
    ⟨rv, flatRv, rFlatRv, hREval, hRFlatSourceEval, hRFlatEval,
      hRFlatSourceTy, hRFlatTy, hRFlatSourceList, hRFlatList⟩
  exact ⟨ss, flatSs, sFlatSs, rv, flatRv, rFlatRv,
    by simpa using hSEval,
    by simpa [sFlatSource] using hSFlatSourceEval,
    by simpa [sFlat] using hSFlatEval,
    by simpa using hREval,
    by simpa [rFlatSource] using hRFlatSourceEval,
    by simpa [eps, rFlat] using hRFlatEval,
    by simpa [sFlatSource] using hSFlatSourceTy,
    by simpa [sFlat] using hSFlatTy,
    by simpa [rFlatSource] using hRFlatSourceTy,
    by simpa [eps, rFlat] using hRFlatTy,
    by simpa [sFlatSource] using hSFlatSourceList,
    by simpa [sFlat] using hSFlatList,
    by simpa [rFlatSource] using hRFlatSourceList,
    by simpa [eps, rFlat] using hRFlatList,
    hSFlatSourceRel⟩

theorem StrInReConsumeInternal.smt_value_rel_str_concat_double_rev_consume_local
    (M : SmtModel) (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a))))
      (__smtx_model_eval M (__eo_to_smt a)) := by
  rw [eo_list_rev_list_rev_str_concat_eq_of_list_true a hList hRev]
  exact RuleProofs.smt_value_rel_refl
    (__smtx_model_eval M (__eo_to_smt a))

theorem StrInReConsumeInternal.eval_str_concat_double_rev_seq_rel_consume_local
    (M : SmtModel) (a : Term) (T : SmtType) (ss : SmtSeq)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq ss)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    ∃ revRevSs,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) a))) =
        SmtValue.Seq revRevSs ∧
      RuleProofs.smt_value_rel (SmtValue.Seq revRevSs)
        (SmtValue.Seq ss) := by
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) a))))
        (SmtValue.Seq ss) := by
    simpa [hEval] using
      StrInReConsumeInternal.smt_value_rel_str_concat_double_rev_consume_local M a T hList hTy hRev
  rcases smt_value_rel_seq_right hRel with
    ⟨revRevSs, hRevRevEval, _hSeqRel⟩
  exact ⟨revRevSs, hRevRevEval, by simpa [hRevRevEval] using hRel⟩

theorem StrInReConsumeInternal.native_str_in_re_eq_of_double_rev_action_evals_consume_local
    (M : SmtModel) (hM : model_wf M)
    (sParts rParts : Term) (ss : SmtSeq) (rv : SmtRegLan)
    (hSList :
      __eo_is_list (Term.UOp UserOp.str_concat) sParts =
        Term.Boolean true)
    (hSTy :
      __smtx_typeof (__eo_to_smt sParts) =
        SmtType.Seq SmtType.Char)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt sParts) = SmtValue.Seq ss)
    (hSRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) sParts ≠ Term.Stuck)
    (hREval :
      __smtx_model_eval M (__eo_to_smt rParts) = SmtValue.RegLan rv)
    (hRRev :
      __re_rev_map_rev rParts StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck) :
    ∃ ss' rv',
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) sParts))) =
        SmtValue.Seq ss' ∧
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_rev_map_rev rParts StrInReConsumeInternal.re_empty_string_re_consume_local)
              StrInReConsumeInternal.re_empty_string_re_consume_local)) =
        SmtValue.RegLan rv' ∧
      native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string ss') rv' := by
  rcases StrInReConsumeInternal.eval_str_concat_double_rev_seq_rel_consume_local M sParts
      SmtType.Char ss hSList hSTy hSEval hSRev with
    ⟨ss', hSSRevRevEval, hSRel⟩
  rcases StrInReConsumeInternal.eval_re_action_double_rev_reglan_rel_consume_local M rParts rv
      hREval hRRev with
    ⟨rv', hRRRevRevEval, hRRel⟩
  have hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt sParts) (by
          unfold term_has_non_none_type
          rw [hSTy]
          simp)
  exact ⟨ss', rv', hSSRevRevEval, hRRRevRevEval,
    native_str_in_re_eq_of_seq_reglan_rel_symm hSeqTy hSRel hRRel⟩

theorem StrInReConsumeInternal.native_str_in_re_eq_of_double_rev_action_eval_values_consume_local
    (M : SmtModel) (hM : model_wf M)
    (sParts rParts : Term) (ss nextSs : SmtSeq)
    (rv nextRv : SmtRegLan)
    (hSList :
      __eo_is_list (Term.UOp UserOp.str_concat) sParts =
        Term.Boolean true)
    (hSTy :
      __smtx_typeof (__eo_to_smt sParts) =
        SmtType.Seq SmtType.Char)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt sParts) = SmtValue.Seq ss)
    (hSRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) sParts ≠ Term.Stuck)
    (hREval :
      __smtx_model_eval M (__eo_to_smt rParts) = SmtValue.RegLan rv)
    (hRRev :
      __re_rev_map_rev rParts StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck)
    (hNextSEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) sParts))) =
        SmtValue.Seq nextSs)
    (hNextREval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_rev_map_rev rParts StrInReConsumeInternal.re_empty_string_re_consume_local)
              StrInReConsumeInternal.re_empty_string_re_consume_local)) =
        SmtValue.RegLan nextRv) :
    native_str_in_re (native_unpack_string ss) rv =
      native_str_in_re (native_unpack_string nextSs) nextRv := by
  rcases StrInReConsumeInternal.native_str_in_re_eq_of_double_rev_action_evals_consume_local
      M hM sParts rParts ss rv hSList hSTy hSEval hSRev hREval hRRev with
    ⟨nextSs0, nextRv0, hNextSEval0, hNextREval0, hNative⟩
  have hNextSs : nextSs0 = nextSs := by
    rw [hNextSEval] at hNextSEval0
    cases hNextSEval0
    rfl
  have hNextRv : nextRv0 = nextRv := by
    rw [hNextREval] at hNextREval0
    cases hNextREval0
    rfl
  subst nextSs0
  subst nextRv0
  exact hNative

theorem StrInReConsumeInternal.native_str_in_re_eq_of_rel_double_rev_action_eval_values_consume_local
    (M : SmtModel) (hM : model_wf M)
    (sParts rParts : Term) (ss partsSs nextSs : SmtSeq)
    (rv partsRv nextRv : SmtRegLan)
    (hSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq partsSs)
        (SmtValue.Seq ss))
    (hRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan partsRv)
        (SmtValue.RegLan rv))
    (hSList :
      __eo_is_list (Term.UOp UserOp.str_concat) sParts =
        Term.Boolean true)
    (hSTy :
      __smtx_typeof (__eo_to_smt sParts) =
        SmtType.Seq SmtType.Char)
    (hPartsSEval :
      __smtx_model_eval M (__eo_to_smt sParts) =
        SmtValue.Seq partsSs)
    (hSRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) sParts ≠ Term.Stuck)
    (hPartsREval :
      __smtx_model_eval M (__eo_to_smt rParts) =
        SmtValue.RegLan partsRv)
    (hRRev :
      __re_rev_map_rev rParts StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck)
    (hNextSEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) sParts))) =
        SmtValue.Seq nextSs)
    (hNextREval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_rev_map_rev rParts StrInReConsumeInternal.re_empty_string_re_consume_local)
              StrInReConsumeInternal.re_empty_string_re_consume_local)) =
        SmtValue.RegLan nextRv) :
    native_str_in_re (native_unpack_string ss) rv =
      native_str_in_re (native_unpack_string nextSs) nextRv := by
  have hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    have hPartsTy :
        __smtx_typeof_value (SmtValue.Seq partsSs) =
          SmtType.Seq SmtType.Char := by
      rw [← hPartsSEval]
      simpa [hSTy] using
        smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt sParts) (by
            unfold term_has_non_none_type
            rw [hSTy]
            simp)
    have hSeq : RuleProofs.smt_seq_rel partsSs ss := by
      simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using
        hSeqRel
    have hEq : partsSs = ss :=
      (RuleProofs.smt_seq_rel_iff_eq partsSs ss).1 hSeq
    subst partsSs
    exact hPartsTy
  calc
    native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string partsSs) partsRv :=
      native_str_in_re_eq_of_seq_reglan_rel_symm hSeqTy hSeqRel hRegRel
    _ = native_str_in_re (native_unpack_string nextSs) nextRv :=
      StrInReConsumeInternal.native_str_in_re_eq_of_double_rev_action_eval_values_consume_local
        M hM sParts rParts partsSs nextSs partsRv nextRv hSList hSTy
        hPartsSEval hSRev hPartsREval hRRev hNextSEval hNextREval

theorem StrInReConsumeInternal.eo_get_nil_rec_re_concat_eq_of_nil_true_consume_local
    (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
        Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil = nil := by
  have hEq := StrInReConsumeInternal.re_concat_nil_eq_eps_of_is_list_nil_true_local nil hNil
  subst nil
  rfl

theorem StrInReConsumeInternal.eo_list_rev_rec_re_concat_nil_eq_of_nil_true_consume_local
    (nil acc : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
        Term.Boolean true) :
    __eo_list_rev_rec nil acc = acc := by
  have hEq := StrInReConsumeInternal.re_concat_nil_eq_eps_of_is_list_nil_true_local nil hNil
  subst nil
  cases acc <;> rfl

theorem StrInReConsumeInternal.eo_get_nil_rec_re_concat_list_rev_rec_eq_consume_local
    (tail acc : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.re_concat) tail =
        Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.re_concat) acc =
        Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.re_concat)
        (__eo_list_rev_rec tail acc) =
      __eo_get_nil_rec (Term.UOp UserOp.re_concat) acc := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.re_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.re_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y
          hTailList
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.re_concat) x acc (by decide) hAccList
      have hsimpa := ih hTailTailList hConsAccList
      try simp [__eo_list_rev_rec] at hsimpa ⊢
      exact hsimpa
  | case4 nil acc hNil hAcc hNot =>
      simp [__eo_list_rev_rec]

theorem StrInReConsumeInternal.eo_list_rev_rec_re_concat_rev_rec_get_nil_eq_consume_local
    (tail acc : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.re_concat) tail =
        Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.re_concat) acc =
        Term.Boolean true) :
    __eo_list_rev_rec (__eo_list_rev_rec tail acc)
        (__eo_get_nil_rec (Term.UOp UserOp.re_concat) tail) =
      __eo_list_rev_rec acc tail := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.re_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.re_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y
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
          __eo_is_list (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.re_concat) x acc (by decide) hAccList
      have hGetEq :
          __eo_get_nil_rec (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y) =
            __eo_get_nil_rec (Term.UOp UserOp.re_concat) y :=
        eo_get_nil_rec_cons_self_eq_of_tail_list
          (Term.UOp UserOp.re_concat) x y (by decide) hTailTailList
      rw [hGetEq]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.re_concat) x y acc
        hAccNonStuck]
      rw [ih hTailTailList hConsAccList]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.re_concat) x acc y
        hTailNonStuck]
  | case4 nil acc hNil hAcc hNot =>
      have hGet : __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil ≠
          Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.re_concat) nil hTailList
      have hReq :
          __eo_requires
              (__eo_is_list_nil (Term.UOp UserOp.re_concat) nil)
              (Term.Boolean true) nil ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hNilTrue :
          __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck
          (__eo_is_list_nil (Term.UOp UserOp.re_concat) nil)
          (Term.Boolean true) nil hReq
      have hGetEq :
          __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil = nil :=
        StrInReConsumeInternal.eo_get_nil_rec_re_concat_eq_of_nil_true_consume_local nil
          hNilTrue
      rw [StrInReConsumeInternal.eo_list_rev_rec_re_concat_nil_eq_of_nil_true_consume_local nil
        acc hNilTrue]
      rw [hGetEq]

theorem StrInReConsumeInternal.eo_list_rev_list_rev_re_concat_eq_of_list_true_consume_local
    (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (hRev : __eo_list_rev (Term.UOp UserOp.re_concat) a ≠ Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.re_concat)
        (__eo_list_rev (Term.UOp UserOp.re_concat) a) = a := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.re_concat) a
  have hNilList :
      __eo_is_list (Term.UOp UserOp.re_concat) nil = Term.Boolean true := by
    simpa [nil] using
      eo_get_nil_rec_is_list_true_of_is_list_true
        (Term.UOp UserOp.re_concat) a hList
  have hNilNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
        Term.Boolean true := by
    simpa [nil] using
      eo_is_list_nil_get_nil_rec_of_is_list_true
        (Term.UOp UserOp.re_concat) a hList
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.re_concat) a =
        __eo_list_rev_rec a nil := by
    simpa [nil] using
      eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.re_concat) a hRev
  have hRevRecNonStuck :
      __eo_list_rev_rec a nil ≠ Term.Stuck := by
    simpa [hRevEq] using hRev
  have hRevRecList :
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__eo_list_rev_rec a nil) = Term.Boolean true :=
    eo_list_rev_rec_is_list_true_of_lists (Term.UOp UserOp.re_concat)
      a nil hList hNilList hRevRecNonStuck
  have hRevRev :
      __eo_list_rev (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) a) ≠ Term.Stuck := by
    rw [hRevEq]
    exact eo_list_rev_ne_stuck_of_is_list_true
      (Term.UOp UserOp.re_concat) (__eo_list_rev_rec a nil) hRevRecList
  have hGetRev :
      __eo_get_nil_rec (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) a) = nil := by
    rw [hRevEq]
    calc
      __eo_get_nil_rec (Term.UOp UserOp.re_concat)
          (__eo_list_rev_rec a nil) =
        __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil := by
          exact
            StrInReConsumeInternal.eo_get_nil_rec_re_concat_list_rev_rec_eq_consume_local a nil
              hList hNilList
      _ = nil :=
        StrInReConsumeInternal.eo_get_nil_rec_re_concat_eq_of_nil_true_consume_local nil hNilNil
  have hRevRevEq :
      __eo_list_rev (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) a) =
        __eo_list_rev_rec (__eo_list_rev (Term.UOp UserOp.re_concat) a)
          (__eo_get_nil_rec (Term.UOp UserOp.re_concat)
            (__eo_list_rev (Term.UOp UserOp.re_concat) a)) :=
    eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.re_concat)
      (__eo_list_rev (Term.UOp UserOp.re_concat) a) hRevRev
  rw [hRevRevEq, hGetRev, hRevEq]
  rw [StrInReConsumeInternal.eo_list_rev_rec_re_concat_rev_rec_get_nil_eq_consume_local a nil
    hList hNilList]
  rw [StrInReConsumeInternal.eo_list_rev_rec_re_concat_nil_eq_of_nil_true_consume_local nil a
    hNilNil]

theorem StrInReConsumeInternal.smt_value_rel_re_concat_double_rev_consume_local
    (M : SmtModel) (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (hRev : __eo_list_rev (Term.UOp UserOp.re_concat) a ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_rev (Term.UOp UserOp.re_concat)
            (__eo_list_rev (Term.UOp UserOp.re_concat) a))))
      (__smtx_model_eval M (__eo_to_smt a)) := by
  rw [StrInReConsumeInternal.eo_list_rev_list_rev_re_concat_eq_of_list_true_consume_local a
    hList hRev]
  exact RuleProofs.smt_value_rel_refl
    (__smtx_model_eval M (__eo_to_smt a))

theorem StrInReConsumeInternal.eval_re_concat_double_rev_reglan_rel_consume_local
    (M : SmtModel) (a : Term) (rv : SmtRegLan)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (hEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan rv)
    (hRev : __eo_list_rev (Term.UOp UserOp.re_concat) a ≠ Term.Stuck) :
    ∃ revRevRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) a))) =
        SmtValue.RegLan revRevRv ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan revRevRv)
        (SmtValue.RegLan rv) := by
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) a))))
        (SmtValue.RegLan rv) := by
    simpa [hEval] using
      StrInReConsumeInternal.smt_value_rel_re_concat_double_rev_consume_local M a hList hRev
  exact smt_value_rel_reglan_right_consume_local hRel

theorem StrInReConsumeInternal.native_str_in_re_eq_of_double_rev_evals_consume_local
    (M : SmtModel) (hM : model_wf M)
    (sParts rParts : Term) (ss : SmtSeq)
    (rv : SmtRegLan)
    (hSList :
      __eo_is_list (Term.UOp UserOp.str_concat) sParts =
        Term.Boolean true)
    (hSTy :
      __smtx_typeof (__eo_to_smt sParts) =
        SmtType.Seq SmtType.Char)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt sParts) = SmtValue.Seq ss)
    (hSRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) sParts ≠ Term.Stuck)
    (hRList :
      __eo_is_list (Term.UOp UserOp.re_concat) rParts =
        Term.Boolean true)
    (hREval :
      __smtx_model_eval M (__eo_to_smt rParts) = SmtValue.RegLan rv)
    (hRRev :
      __eo_list_rev (Term.UOp UserOp.re_concat) rParts ≠ Term.Stuck) :
    ∃ ss' rv',
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) sParts))) =
        SmtValue.Seq ss' ∧
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) rParts))) =
        SmtValue.RegLan rv' ∧
      native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string ss') rv' := by
  rcases StrInReConsumeInternal.eval_str_concat_double_rev_seq_rel_consume_local M sParts
      SmtType.Char ss hSList hSTy hSEval hSRev with
    ⟨ss', hSSRevRevEval, hSRel⟩
  rcases StrInReConsumeInternal.eval_re_concat_double_rev_reglan_rel_consume_local M rParts rv
      hRList hREval hRRev with
    ⟨rv', hRRRevRevEval, hRRel⟩
  have hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt sParts) (by
          unfold term_has_non_none_type
          rw [hSTy]
          simp)
  exact ⟨ss', rv', hSSRevRevEval, hRRRevRevEval,
    native_str_in_re_eq_of_seq_reglan_rel_symm hSeqTy hSRel hRRel⟩

theorem StrInReConsumeInternal.native_str_in_re_eq_of_double_rev_eval_values_consume_local
    (M : SmtModel) (hM : model_wf M)
    (sParts rParts : Term) (ss nextSs : SmtSeq)
    (rv nextRv : SmtRegLan)
    (hSList :
      __eo_is_list (Term.UOp UserOp.str_concat) sParts =
        Term.Boolean true)
    (hSTy :
      __smtx_typeof (__eo_to_smt sParts) =
        SmtType.Seq SmtType.Char)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt sParts) = SmtValue.Seq ss)
    (hSRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) sParts ≠ Term.Stuck)
    (hRList :
      __eo_is_list (Term.UOp UserOp.re_concat) rParts =
        Term.Boolean true)
    (hREval :
      __smtx_model_eval M (__eo_to_smt rParts) = SmtValue.RegLan rv)
    (hRRev :
      __eo_list_rev (Term.UOp UserOp.re_concat) rParts ≠ Term.Stuck)
    (hNextSEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) sParts))) =
        SmtValue.Seq nextSs)
    (hNextREval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) rParts))) =
        SmtValue.RegLan nextRv) :
    native_str_in_re (native_unpack_string ss) rv =
      native_str_in_re (native_unpack_string nextSs) nextRv := by
  rcases StrInReConsumeInternal.native_str_in_re_eq_of_double_rev_evals_consume_local
      M hM sParts rParts ss rv hSList hSTy hSEval hSRev
      hRList hREval hRRev with
    ⟨nextSs0, nextRv0, hNextSEval0, hNextREval0, hNative⟩
  have hNextSs : nextSs0 = nextSs := by
    rw [hNextSEval] at hNextSEval0
    cases hNextSEval0
    rfl
  have hNextRv : nextRv0 = nextRv := by
    rw [hNextREval] at hNextREval0
    cases hNextREval0
    rfl
  subst nextSs0
  subst nextRv0
  exact hNative

theorem StrInReConsumeInternal.eo_mk_apply_ne_boolean_false_local (f x : Term) :
    __eo_mk_apply f x ≠ Term.Boolean false := by
  cases f <;> cases x <;> simp [__eo_mk_apply]

theorem StrInReConsumeInternal.str_re_consume_candidate_false_cases_local
    (first second final : Term)
    (hNe :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) ≠
        Term.Stuck)
    (hFalse :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) =
        Term.Boolean false) :
    first = Term.Boolean false ∨
      second = Term.Boolean false ∨ final = Term.Boolean false := by
  let inner :=
    __eo_ite (__eo_eq second (Term.Boolean false)) (Term.Boolean false)
      final
  rcases eo_ite_result_cases (__eo_eq first (Term.Boolean false))
      (Term.Boolean false) inner (Term.Boolean false) (by
        simpa [inner] using hNe) (by simpa [inner] using hFalse) with
    hFirst | hInner
  · left
    exact (eq_of_eo_eq_true first (Term.Boolean false) hFirst.1).symm
  · have hInnerNe : inner ≠ Term.Stuck := by
      rw [hInner.2]
      simp
    rcases eo_ite_result_cases (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final (Term.Boolean false) hInnerNe
        hInner.2 with hSecond | hFinal
    · right
      left
      exact (eq_of_eo_eq_true second (Term.Boolean false) hSecond.1).symm
    · right
      right
      exact hFinal.2

theorem StrInReConsumeInternal.str_re_consume_candidate_false_rec_cases_local
    (first second final : Term)
    (hNe :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) ≠
        Term.Stuck)
    (hFalse :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) =
        Term.Boolean false)
    (hFinalNotFalse : final ≠ Term.Boolean false) :
    first = Term.Boolean false ∨ second = Term.Boolean false := by
  rcases StrInReConsumeInternal.str_re_consume_candidate_false_cases_local first second final hNe
      hFalse with hFirst | hSecondOrFinal
  · exact Or.inl hFirst
  · rcases hSecondOrFinal with hSecond | hFinal
    · exact Or.inr hSecond
    · exact False.elim (hFinalNotFalse hFinal)

theorem StrInReConsumeInternal.str_re_consume_candidate_final_eq_local
    (first second final : Term)
    (hNe :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) ≠
        Term.Stuck)
    (hNotFalse :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) ≠
        Term.Boolean false) :
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final) =
      final := by
  let inner :=
    __eo_ite (__eo_eq second (Term.Boolean false)) (Term.Boolean false)
      final
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      inner
  rcases eo_ite_result_cases (__eo_eq first (Term.Boolean false))
      (Term.Boolean false) inner candidate (by
        simpa [candidate, inner] using hNe) (by
        simpa [candidate, inner]) with hFirst | hRest
  · exfalso
    exact hNotFalse (by simpa [candidate, inner] using hFirst.2.symm)
  · have hInnerNe : inner ≠ Term.Stuck := by
      intro hBad
      apply hNe
      simpa [candidate, inner, hRest.1, eo_ite_false] using hBad
    rcases eo_ite_result_cases (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final inner hInnerNe (by
          simpa [inner]) with hSecond | hFinal
    · exfalso
      exact hNotFalse (by
        simpa [candidate, inner, hRest.1, eo_ite_false] using
          hSecond.2.symm)
    · simpa [candidate, inner, hRest.1, eo_ite_false] using hFinal.2.symm

theorem StrInReConsumeInternal.str_re_consume_candidate_final_facts_local
    (first second final : Term)
    (hNe :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) ≠
        Term.Stuck)
    (hNotFalse :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) ≠
        Term.Boolean false) :
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final) =
      final ∧
      first ≠ Term.Boolean false ∧
      second ≠ Term.Boolean false ∧
      final ≠ Term.Stuck := by
  let inner :=
    __eo_ite (__eo_eq second (Term.Boolean false)) (Term.Boolean false)
      final
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      inner
  rcases eo_ite_result_cases (__eo_eq first (Term.Boolean false))
      (Term.Boolean false) inner candidate (by
        simpa [candidate, inner] using hNe) (by
        simpa [candidate, inner]) with hFirst | hRest
  · exfalso
    exact hNotFalse (by simpa [candidate, inner] using hFirst.2.symm)
  · have hFirstNotFalse : first ≠ Term.Boolean false := by
      intro hFirstFalse
      rw [hFirstFalse] at hRest
      simp [__eo_eq, native_teq] at hRest
    have hInnerNe : inner ≠ Term.Stuck := by
      intro hBad
      apply hNe
      simpa [candidate, inner, hRest.1, eo_ite_false] using hBad
    rcases eo_ite_result_cases (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final inner hInnerNe (by
          simpa [inner]) with hSecond | hFinal
    · exfalso
      exact hNotFalse (by
        simpa [candidate, inner, hRest.1, eo_ite_false] using
          hSecond.2.symm)
    · have hSecondNotFalse : second ≠ Term.Boolean false := by
        intro hSecondFalse
        rw [hSecondFalse] at hFinal
        simp [__eo_eq, native_teq] at hFinal
      have hCandidateFinal : candidate = final := by
        simpa [candidate, inner, hRest.1, eo_ite_false] using
          hFinal.2.symm
      have hFinalNe : final ≠ Term.Stuck := by
        intro hBad
        have hCandidateStuck : candidate = Term.Stuck := by
          rw [hCandidateFinal, hBad]
        exact hNe (by simpa [candidate] using hCandidateStuck)
      exact ⟨by simpa [candidate, inner] using hCandidateFinal,
        hFirstNotFalse, hSecondNotFalse, hFinalNe⟩

theorem StrInReConsumeInternal.str_re_consume_candidate_final_conditions_local
    (first second final : Term)
    (hNe :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) ≠
        Term.Stuck)
    (hNotFalse :
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
          (__eo_ite (__eo_eq second (Term.Boolean false))
            (Term.Boolean false) final) ≠
        Term.Boolean false) :
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final) =
      final ∧
      __eo_eq first (Term.Boolean false) = Term.Boolean false ∧
      __eo_eq second (Term.Boolean false) = Term.Boolean false ∧
      first ≠ Term.Stuck ∧
      second ≠ Term.Stuck ∧
      final ≠ Term.Stuck := by
  let inner :=
    __eo_ite (__eo_eq second (Term.Boolean false)) (Term.Boolean false)
      final
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      inner
  rcases eo_ite_result_cases (__eo_eq first (Term.Boolean false))
      (Term.Boolean false) inner candidate (by
        simpa [candidate, inner] using hNe) (by
        simpa [candidate, inner]) with hFirst | hRest
  · exfalso
    exact hNotFalse (by simpa [candidate, inner] using hFirst.2.symm)
  · have hInnerNe : inner ≠ Term.Stuck := by
      intro hBad
      apply hNe
      simpa [candidate, inner, hRest.1, eo_ite_false] using hBad
    rcases eo_ite_result_cases (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final inner hInnerNe (by
          simpa [inner]) with hSecond | hFinal
    · exfalso
      exact hNotFalse (by
        simpa [candidate, inner, hRest.1, eo_ite_false] using
          hSecond.2.symm)
    · have hCandidateFinal : candidate = final := by
        simpa [candidate, inner, hRest.1, eo_ite_false] using
          hFinal.2.symm
      have hFirstNe : first ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hRest
        simp [__eo_eq] at hRest
      have hSecondNe : second ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hFinal
        simp [__eo_eq] at hFinal
      have hFinalNe : final ≠ Term.Stuck := by
        intro hBad
        have hCandidateStuck : candidate = Term.Stuck := by
          rw [hCandidateFinal, hBad]
        exact hNe (by simpa [candidate] using hCandidateStuck)
      exact ⟨by simpa [candidate, inner] using hCandidateFinal,
        hRest.1, hFinal.1, hFirstNe, hSecondNe, hFinalNe⟩

theorem StrInReConsumeInternal.str_re_consume_non_mult_eq_local
    (s r : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    __str_re_consume s r =
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final) := by
  simpa using __str_re_consume.eq_4 s r hS hR hNotMult

theorem StrInReConsumeInternal.str_re_consume_non_mult_false_rec_cases_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck)
    (hFalse : side = Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    first = Term.Boolean false ∨ second = Term.Boolean false := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean false)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__str_collect (__str_membership_str second))))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second)))
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      (__eo_ite (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final)
  have hSideCandidate : side = candidate := by
    rw [hSide]
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second, final,
      candidate] using
        StrInReConsumeInternal.str_re_consume_non_mult_eq_local s r hS hR hNotMult
  have hCandidateNe : candidate ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideCandidate, hBad]
  have hCandidateFalse : candidate = Term.Boolean false := by
    rw [← hSideCandidate]
    exact hFalse
  have hFinalNotFalse : final ≠ Term.Boolean false := by
    simpa [final] using
      StrInReConsumeInternal.eo_mk_apply_ne_boolean_false_local
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
  exact StrInReConsumeInternal.str_re_consume_candidate_false_rec_cases_local first second final
    (by simpa [candidate] using hCandidateNe)
    (by simpa [candidate] using hCandidateFalse)
    hFinalNotFalse

theorem StrInReConsumeInternal.str_re_consume_non_mult_final_eq_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    side = final := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean false)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__str_collect (__str_membership_str second))))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second)))
  let inner :=
    __eo_ite (__eo_eq second (Term.Boolean false)) (Term.Boolean false)
      final
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      inner
  have hSideCandidate : side = candidate := by
    rw [hSide]
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second, final,
      inner, candidate] using
        StrInReConsumeInternal.str_re_consume_non_mult_eq_local s r hS hR hNotMult
  have hCandidateNe : candidate ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideCandidate, hBad]
  have hCandidateNotFalse : candidate ≠ Term.Boolean false := by
    intro hBad
    apply hSideNotFalse
    rw [hSideCandidate, hBad]
  rcases eo_ite_result_cases (__eo_eq first (Term.Boolean false))
      (Term.Boolean false) inner candidate hCandidateNe (by
        simpa [candidate]) with hFirst | hNotFirst
  · exfalso
    exact hCandidateNotFalse hFirst.2.symm
  · have hInnerNe : inner ≠ Term.Stuck := by
      intro hBad
      apply hCandidateNe
      rw [← hNotFirst.2, hBad]
    rcases eo_ite_result_cases (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final inner hInnerNe (by
          simpa [inner]) with hSecond | hFinal
    · exfalso
      apply hCandidateNotFalse
      rw [← hNotFirst.2]
      exact hSecond.2.symm
    · rw [hSideCandidate, ← hNotFirst.2, ← hFinal.2]

theorem StrInReConsumeInternal.str_re_consume_non_mult_final_carry_false_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    carry = Term.Boolean false ∧
      second ≠ Term.Stuck ∧
      __eo_eq first (Term.Boolean false) = Term.Boolean false ∧
      __eo_eq second (Term.Boolean false) = Term.Boolean false := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean false)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__str_collect (__str_membership_str second))))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second)))
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      (__eo_ite (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final)
  have hSideCandidate : side = candidate := by
    rw [hSide]
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second, final,
      candidate] using
        StrInReConsumeInternal.str_re_consume_non_mult_eq_local s r hS hR hNotMult
  have hCandidateNe : candidate ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideCandidate, hBad]
  have hCandidateNotFalse : candidate ≠ Term.Boolean false := by
    intro hBad
    apply hSideNotFalse
    rw [hSideCandidate, hBad]
  rcases StrInReConsumeInternal.str_re_consume_candidate_final_conditions_local first second final
      (by simpa [candidate] using hCandidateNe)
      (by simpa [candidate] using hCandidateNotFalse) with
    ⟨_hCandidateFinal, hFirstEqFalse, hSecondEqFalse, _hFirstNe,
      hSecondNe, _hFinalNe⟩
  have hNextSNe : nextS ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck nextS nextR nextS
      hSecondNe
  have hIteNe :
      __eo_ite carry sFlat (__str_membership_str first) ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first)) hNextSNe
  have hCarryNe : carry ≠ Term.Stuck := by
    rcases eo_ite_cases_of_ne_stuck carry sFlat
        (__str_membership_str first) hIteNe with hCarry | hCarry
    · rw [hCarry]
      simp
    · rw [hCarry]
      simp
  have hCarryFalse :
      carry = Term.Boolean false := by
    simpa [carry] using
      StrInReConsumeInternal.eo_and_false_left_eq_false_of_ne_stuck_local
        (__eo_not (__eo_eq (__str_membership_re first) eps))
        (by simpa [carry] using hCarryNe)
  exact ⟨by simpa [carry] using hCarryFalse,
    by simpa [second] using hSecondNe,
    by simpa [first] using hFirstEqFalse,
    by simpa [second] using hSecondEqFalse⟩

theorem StrInReConsumeInternal.str_re_consume_mult_eq_local
    (s r : Term)
    (hS : s ≠ Term.Stuck) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    __str_re_consume s (Term.Apply (Term.UOp UserOp.re_mult) r) =
      __eo_ite (__eo_eq candidate (Term.Boolean false))
        (Term.Boolean false)
        (__eo_requires (__str_membership_re candidate) eps
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str candidate))
            (Term.Apply (Term.UOp UserOp.re_mult) r))) := by
  simpa using __str_re_consume.eq_3 s r hS

theorem StrInReConsumeInternal.eo_requires_ne_boolean_false_of_result_ne_false_local
    (a b result : Term)
    (hResult : result ≠ Term.Boolean false) :
    __eo_requires a b result ≠ Term.Boolean false := by
  intro hReqFalse
  have hReqNe : __eo_requires a b result ≠ Term.Stuck := by
    rw [hReqFalse]
    simp
  have hReqEq := eo_requires_eq_result_of_ne_stuck a b result hReqNe
  apply hResult
  rw [← hReqEq]
  exact hReqFalse

theorem StrInReConsumeInternal.str_re_consume_mult_false_rec_cases_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hFalse : side = Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    first = Term.Boolean false ∨ second = Term.Boolean false := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean true)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__str_collect (__str_membership_str second))))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second)))
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      (__eo_ite (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final)
  let rebuild :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__str_membership_str candidate))
      (Term.Apply (Term.UOp UserOp.re_mult) r)
  let outer :=
    __eo_ite (__eo_eq candidate (Term.Boolean false))
      (Term.Boolean false)
      (__eo_requires (__str_membership_re candidate) eps rebuild)
  have hSideOuter : side = outer := by
    rw [hSide]
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second, final,
      candidate, rebuild, outer] using
        StrInReConsumeInternal.str_re_consume_mult_eq_local s r hS
  have hOuterNe : outer ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideOuter, hBad]
  have hOuterFalse : outer = Term.Boolean false := by
    rw [← hSideOuter]
    exact hFalse
  have hCandidateFalse : candidate = Term.Boolean false := by
    rcases eo_ite_result_cases (__eo_eq candidate (Term.Boolean false))
        (Term.Boolean false)
        (__eo_requires (__str_membership_re candidate) eps rebuild)
        (Term.Boolean false) (by simpa [outer] using hOuterNe)
        (by simpa [outer] using hOuterFalse) with hThen | hElse
    · exact (eq_of_eo_eq_true candidate (Term.Boolean false) hThen.1).symm
    · exfalso
      have hRebuildNotFalse : rebuild ≠ Term.Boolean false := by
        simpa [rebuild] using
          StrInReConsumeInternal.eo_mk_apply_ne_boolean_false_local
            (__eo_mk_apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str candidate))
            (Term.Apply (Term.UOp UserOp.re_mult) r)
      exact
        StrInReConsumeInternal.eo_requires_ne_boolean_false_of_result_ne_false_local
          (__str_membership_re candidate) eps rebuild hRebuildNotFalse hElse.2
  have hFinalNotFalse : final ≠ Term.Boolean false := by
    simpa [final] using
      StrInReConsumeInternal.eo_mk_apply_ne_boolean_false_local
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
  have hCandidateNe : candidate ≠ Term.Stuck := by
    rw [hCandidateFalse]
    simp
  exact StrInReConsumeInternal.str_re_consume_candidate_false_rec_cases_local first second final
    (by simpa [candidate] using hCandidateNe)
    (by simpa [candidate] using hCandidateFalse)
    hFinalNotFalse

theorem StrInReConsumeInternal.str_re_consume_mult_final_eq_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    let rebuild :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str candidate))
        (Term.Apply (Term.UOp UserOp.re_mult) r)
    side = rebuild ∧ candidate = final ∧ __str_membership_re candidate = eps := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean true)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__str_collect (__str_membership_str second))))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second)))
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      (__eo_ite (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final)
  let rebuild :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__str_membership_str candidate))
      (Term.Apply (Term.UOp UserOp.re_mult) r)
  let req := __eo_requires (__str_membership_re candidate) eps rebuild
  let outer := __eo_ite (__eo_eq candidate (Term.Boolean false))
    (Term.Boolean false) req
  have hSideOuter : side = outer := by
    rw [hSide]
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second, final,
      candidate, rebuild, req, outer] using
        StrInReConsumeInternal.str_re_consume_mult_eq_local s r hS
  have hOuterNe : outer ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hSideOuter, hBad]
  have hOuterNotFalse : outer ≠ Term.Boolean false := by
    intro hBad
    apply hSideNotFalse
    rw [hSideOuter, hBad]
  rcases eo_ite_result_cases (__eo_eq candidate (Term.Boolean false))
      (Term.Boolean false) req outer hOuterNe (by
        simpa [outer]) with hCandidateFalseBranch | hReqBranch
  · exfalso
    exact hOuterNotFalse hCandidateFalseBranch.2.symm
  · have hReqNe : req ≠ Term.Stuck := by
      intro hBad
      apply hOuterNe
      rw [← hReqBranch.2, hBad]
    have hReqResult := eo_requires_eq_result_of_ne_stuck
      (__str_membership_re candidate) eps rebuild hReqNe
    have hReqEq := eo_requires_eq_of_ne_stuck
      (__str_membership_re candidate) eps rebuild hReqNe
    have hSideRebuild : side = rebuild := by
      calc
        side = outer := hSideOuter
        _ = req := hReqBranch.2.symm
        _ = rebuild := hReqResult
    have hCandidateNotFalse : candidate ≠ Term.Boolean false := by
      intro hCandFalse
      have hCondTrue :
          __eo_eq candidate (Term.Boolean false) = Term.Boolean true := by
        rw [hCandFalse]
        simp [__eo_eq, native_teq]
      have hOuterFalse : outer = Term.Boolean false := by
        simp [outer, hCondTrue, eo_ite_true]
      exact hOuterNotFalse hOuterFalse
    have hCandidateNe : candidate ≠ Term.Stuck := by
      intro hCandStuck
      rw [hCandStuck] at hReqEq
      simp [__str_membership_re] at hReqEq
    have hCandidateFinal :=
      StrInReConsumeInternal.str_re_consume_candidate_final_eq_local first second final
        (by simpa [candidate] using hCandidateNe)
        (by simpa [candidate] using hCandidateNotFalse)
    exact ⟨hSideRebuild, by simpa [candidate] using hCandidateFinal,
      by simpa [eps] using hReqEq⟩

theorem StrInReConsumeInternal.str_re_consume_mult_final_carry_eq_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    carry = __eo_not (__eo_eq (__str_membership_re first) eps) ∧
      second ≠ Term.Stuck ∧
      __eo_eq first (Term.Boolean false) = Term.Boolean false ∧
      __eo_eq second (Term.Boolean false) = Term.Boolean false := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean true)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__str_collect (__str_membership_str second))))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second)))
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      (__eo_ite (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final)
  let rebuild :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__str_membership_str candidate))
      (Term.Apply (Term.UOp UserOp.re_mult) r)
  have hFinalFacts :
      side = rebuild ∧ candidate = final ∧
        __str_membership_re candidate = eps := by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      final, candidate, rebuild] using
      StrInReConsumeInternal.str_re_consume_mult_final_eq_local s r side hS hSide hSideNe
        hSideNotFalse
  rcases hFinalFacts with
    ⟨_hSideRebuild, hCandidateFinal, hCandidateMem⟩
  have hCandidateNe : candidate ≠ Term.Stuck := by
    intro hBad
    rw [hBad] at hCandidateMem
    simp [__str_membership_re] at hCandidateMem
  have hFinalNotFalse : final ≠ Term.Boolean false := by
    simpa [final] using
      StrInReConsumeInternal.eo_mk_apply_ne_boolean_false_local
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
  have hCandidateNotFalse : candidate ≠ Term.Boolean false := by
    intro hBad
    apply hFinalNotFalse
    rw [← hCandidateFinal]
    exact hBad
  rcases StrInReConsumeInternal.str_re_consume_candidate_final_conditions_local first second final
      (by simpa [candidate] using hCandidateNe)
      (by simpa [candidate] using hCandidateNotFalse) with
    ⟨_hCandidateFinal, hFirstEqFalse, hSecondEqFalse, _hFirstNe,
      hSecondNe, _hFinalNe⟩
  have hNextSNe : nextS ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck nextS nextR nextS
      hSecondNe
  have hIteNe :
      __eo_ite carry sFlat (__str_membership_str first) ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first)) hNextSNe
  have hCarryNe : carry ≠ Term.Stuck := by
    rcases eo_ite_cases_of_ne_stuck carry sFlat
        (__str_membership_str first) hIteNe with hCarry | hCarry
    · rw [hCarry]
      simp
    · rw [hCarry]
      simp
  have hCarryEq :
      carry = __eo_not (__eo_eq (__str_membership_re first) eps) := by
    simpa [carry] using
      StrInReConsumeInternal.eo_and_true_left_eq_arg_of_ne_stuck_local
        (__eo_not (__eo_eq (__str_membership_re first) eps))
        (by simpa [carry] using hCarryNe)
  exact ⟨by simpa [carry] using hCarryEq,
    by simpa [second] using hSecondNe,
    by simpa [first] using hFirstEqFalse,
    by simpa [second] using hSecondEqFalse⟩

theorem StrInReConsumeInternal.eo_list_singleton_elim_arg_ne_stuck_of_ne_stuck_local
    (f a : Term)
    (hElim : __eo_list_singleton_elim f a ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro hA
  subst a
  cases f <;>
    simp [__eo_list_singleton_elim, __eo_is_list, __eo_requires,
      native_ite, native_teq] at hElim

theorem StrInReConsumeInternal.str_re_consume_non_mult_final_subterms_ne_stuck_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    side = final ∧
      __str_collect (__str_membership_str second) ≠ Term.Stuck ∧
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)) ≠
        Term.Stuck := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean false)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let strPart :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
      (__str_collect (__str_membership_str second))
  let rePart :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
      (__re_unflatten (Term.Boolean true)
        (__str_membership_re second))
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart)
      rePart
  have hFinalEq :
      side = final := by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      strPart, rePart, final] using
      StrInReConsumeInternal.str_re_consume_non_mult_final_eq_local s r side hS hR hNotMult
        hSide hSideNe hSideNotFalse
  have hFinalNe : final ≠ Term.Stuck := by
    intro hBad
    apply hSideNe
    rw [hFinalEq, hBad]
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) strPart ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hFinalNe
  have hStrPartNe : strPart ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
  have hCollectNe :
      __str_collect (__str_membership_str second) ≠ Term.Stuck :=
    StrInReConsumeInternal.eo_list_singleton_elim_arg_ne_stuck_of_ne_stuck_local
      (Term.UOp UserOp.str_concat)
      (__str_collect (__str_membership_str second)) hStrPartNe
  have hRePartNe : rePart ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFinalNe
  exact ⟨by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      strPart, rePart, final] using hFinalEq,
    by simpa [second] using hCollectNe,
    by simpa [rePart, second] using hRePartNe⟩

theorem StrInReConsumeInternal.str_re_consume_mult_final_subterms_ne_stuck_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    let rebuild :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str candidate))
        (Term.Apply (Term.UOp UserOp.re_mult) r)
    side = rebuild ∧ candidate = final ∧
      __str_membership_re candidate =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ∧
      __str_collect (__str_membership_str second) ≠ Term.Stuck ∧
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)) ≠
        Term.Stuck := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean true)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let strPart :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
      (__str_collect (__str_membership_str second))
  let rePart :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
      (__re_unflatten (Term.Boolean true)
        (__str_membership_re second))
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart)
      rePart
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false)) (Term.Boolean false)
      (__eo_ite (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final)
  let rebuild :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__str_membership_str candidate))
      (Term.Apply (Term.UOp UserOp.re_mult) r)
  have hFinalFacts :
      side = rebuild ∧ candidate = final ∧
        __str_membership_re candidate = eps := by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      strPart, rePart, final, candidate, rebuild] using
      StrInReConsumeInternal.str_re_consume_mult_final_eq_local s r side hS hSide hSideNe
        hSideNotFalse
  rcases hFinalFacts with
    ⟨hSideRebuild, hCandidateFinal, hCandidateMem⟩
  have hCandidateNe : candidate ≠ Term.Stuck := by
    intro hBad
    rw [hBad] at hCandidateMem
    simp [__str_membership_re] at hCandidateMem
  have hFinalNe : final ≠ Term.Stuck := by
    intro hBad
    apply hCandidateNe
    rw [hCandidateFinal, hBad]
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) strPart ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hFinalNe
  have hStrPartNe : strPart ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
  have hCollectNe :
      __str_collect (__str_membership_str second) ≠ Term.Stuck :=
    StrInReConsumeInternal.eo_list_singleton_elim_arg_ne_stuck_of_ne_stuck_local
      (Term.UOp UserOp.str_concat)
      (__str_collect (__str_membership_str second)) hStrPartNe
  have hRePartNe : rePart ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFinalNe
  exact ⟨by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      strPart, rePart, final, candidate, rebuild] using hSideRebuild,
    by simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      strPart, rePart, final, candidate, rebuild] using hCandidateFinal,
    by simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      strPart, rePart, final, candidate, rebuild] using hCandidateMem,
    by simpa [second] using hCollectNe,
    by simpa [rePart, second] using hRePartNe⟩

theorem StrInReConsumeInternal.re_flatten_tree_ne_stuck_of_ne_stuck_local
    (mode r : Term)
    (h : __re_flatten mode r ≠ Term.Stuck) :
    r ≠ Term.Stuck := by
  intro hR
  subst r
  cases mode <;> simp [__re_flatten] at h

theorem StrInReConsumeInternal.str_collect_arg_ne_stuck_of_ne_stuck_local
    (x : Term)
    (h : __str_collect x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hX
  subst x
  simp [__str_collect] at h

theorem StrInReConsumeInternal.str_collect_arg_is_list_true_of_ne_stuck_local :
    ∀ (parts : Term),
      __str_collect parts ≠ Term.Stuck ->
        __eo_is_list (Term.UOp UserOp.str_concat) parts =
          Term.Boolean true := by
  intro parts
  induction parts using __str_collect.induct with
  | case1 =>
      intro hCollect
      simp [__str_collect] at hCollect
  | case2 head tail ih =>
      intro hCollect
      have hTailCollect :
          __str_collect tail ≠ Term.Stuck :=
        str_collect_tail_ne_stuck_of_cons_ne_stuck_local head tail
          hCollect
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        ih hTailCollect
      exact strConcat_is_list_cons_true_of_tail_list head tail hTailList
  | case3 t _hStuck _hNotConcat =>
      intro hCollect
      have hReq :
          __eo_requires t (__seq_empty (__eo_typeof t)) t ≠
            Term.Stuck := by
        simpa [__str_collect] using hCollect
      have hEq :
          t = __seq_empty (__eo_typeof t) :=
        eo_requires_eq_of_ne_stuck t (__seq_empty (__eo_typeof t)) t hReq
      have hTNe : t ≠ Term.Stuck :=
        eo_requires_left_ne_stuck_of_ne_stuck t
          (__seq_empty (__eo_typeof t)) t hReq
      have hEmptyNe :
          __seq_empty (__eo_typeof t) ≠ Term.Stuck := by
        intro hEmpty
        apply hTNe
        rw [hEq, hEmpty]
      have hEmptyList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__seq_empty (__eo_typeof t)) =
            Term.Boolean true :=
        eo_is_list_str_concat_seq_empty_of_ne_stuck (__eo_typeof t)
          hEmptyNe
      exact (Eq.symm hEq) ▸ hEmptyList

theorem StrInReConsumeInternal.re_unflatten_tree_ne_stuck_of_ne_stuck_local
    (mode r : Term)
    (h : __re_unflatten mode r ≠ Term.Stuck) :
    r ≠ Term.Stuck := by
  intro hR
  subst r
  cases mode <;> simp [__re_unflatten] at h

theorem StrInReConsumeInternal.str_re_consume_final_raw_projection_types_of_second_bool_local
    (second : Term)
    (hSecondTy : __smtx_typeof (__eo_to_smt second) = SmtType.Bool)
    (hUnflatElimNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)) ≠
        Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_membership_str second)) =
        SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt (__str_membership_re second)) =
        SmtType.RegLan := by
  have hUnflatNe :
      __re_unflatten (Term.Boolean true)
          (__str_membership_re second) ≠
        Term.Stuck :=
    StrInReConsumeInternal.eo_list_singleton_elim_arg_ne_stuck_of_ne_stuck_local
      (Term.UOp UserOp.re_concat)
      (__re_unflatten (Term.Boolean true)
        (__str_membership_re second)) hUnflatElimNe
  have hMemReNe : __str_membership_re second ≠ Term.Stuck :=
    StrInReConsumeInternal.re_unflatten_tree_ne_stuck_of_ne_stuck_local
      (Term.Boolean true) (__str_membership_re second) hUnflatNe
  exact StrInReConsumeInternal.str_re_consume_rec_projection_types_of_bool_local second
    hSecondTy hMemReNe

theorem StrInReConsumeInternal.str_re_consume_model_rel_of_final_second_native_eq_local
    (M : SmtModel) (hM : model_wf M)
    (s r side second : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSide :
      side =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect (__str_membership_str second))))
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              (__str_membership_re second))))
    (hSideNe : side ≠ Term.Stuck)
    (hPartsList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_membership_str second) =
        Term.Boolean true)
    (hSecondTy :
      __smtx_typeof (__eo_to_smt second) = SmtType.Bool)
    (hCollectNe :
      __str_collect (__str_membership_str second) ≠ Term.Stuck)
    (hUnflatElimNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)) ≠
        Term.Stuck)
    (hNativeEq :
      ∀ ss rv partsSs reRv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_str second)) =
          SmtValue.Seq partsSs ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_re second)) =
          SmtValue.RegLan reRv ->
          native_str_in_re (native_unpack_string ss) rv =
            native_str_in_re (native_unpack_string partsSs) reRv) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases StrInReConsumeInternal.str_re_consume_final_raw_projection_types_of_second_bool_local
      second hSecondTy hUnflatElimNe with
    ⟨hPartsTy, hRePartTy⟩
  exact StrInReConsumeInternal.str_re_consume_model_rel_of_final_parts_native_eq_local M hM s r
    side (__str_membership_str second) (__str_membership_re second)
    hEqTrans hSide hSideNe hPartsList hPartsTy hCollectNe hRePartTy
    hUnflatElimNe hNativeEq

theorem StrInReConsumeInternal.str_re_consume_rec_native_eq_of_rebuilt_result_local
    (M : SmtModel) (hM : model_wf M)
    (nextS nextR fuel second : Term)
    (ih : StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M nextS nextR fuel)
    (hSecond : second = __str_re_consume_rec nextS nextR fuel)
    (hSecondRebuild :
      second =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str second))
          (__str_membership_re second))
    (hSecondNe : second ≠ Term.Stuck)
    (hNextSTy :
      __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char)
    (hNextRTy :
      __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan)
    (hSecondTy :
      __smtx_typeof (__eo_to_smt second) = SmtType.Bool) :
    ∀ nextSs nextRv partsSs reRv,
      __smtx_model_eval M (__eo_to_smt nextS) =
        SmtValue.Seq nextSs ->
      __smtx_model_eval M (__eo_to_smt nextR) =
        SmtValue.RegLan nextRv ->
      __smtx_model_eval M
          (__eo_to_smt (__str_membership_str second)) =
        SmtValue.Seq partsSs ->
      __smtx_model_eval M
          (__eo_to_smt (__str_membership_re second)) =
        SmtValue.RegLan reRv ->
      native_str_in_re (native_unpack_string nextSs) nextRv =
        native_str_in_re (native_unpack_string partsSs) reRv := by
  let rebuilt :=
    Term.Apply
      (Term.Apply (Term.UOp UserOp.str_in_re)
        (__str_membership_str second))
      (__str_membership_re second)
  have hResidual :
      __str_re_consume_rec nextS nextR fuel = rebuilt := by
    rw [← hSecond, hSecondRebuild]
  have hRebuiltNe : rebuilt ≠ Term.Stuck := by
    intro hBad
    apply hSecondNe
    rw [hSecondRebuild]
    exact hBad
  have hRebuiltTy :
      __smtx_typeof (__eo_to_smt rebuilt) = SmtType.Bool := by
    dsimp [rebuilt]
    rw [← hSecondRebuild]
    exact hSecondTy
  have hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) nextS) nextR))
          rebuilt) :=
    str_re_consume_eq_translation_of_types nextS nextR rebuilt
      hNextSTy hNextRTy hRebuiltTy
  simpa [rebuilt] using
    str_re_consume_rec_native_eq_of_ih_residual M hM nextS nextR fuel
      (__str_membership_str second) (__str_membership_re second) ih
      (by simpa [rebuilt] using hResidual)
      (by simpa [rebuilt] using hRebuiltNe)
      (by simpa [rebuilt] using hEqTrans)

theorem StrInReConsumeInternal.str_re_consume_model_rel_of_final_second_input_native_eq_local
    (M : SmtModel) (hM : model_wf M)
    (s r side nextS nextR second : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSide :
      side =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect (__str_membership_str second))))
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              (__str_membership_re second))))
    (hSideNe : side ≠ Term.Stuck)
    (hNextSTy :
      __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char)
    (hNextRTy :
      __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan)
    (hPartsList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_membership_str second) =
        Term.Boolean true)
    (hSecondTy :
      __smtx_typeof (__eo_to_smt second) = SmtType.Bool)
    (hCollectNe :
      __str_collect (__str_membership_str second) ≠ Term.Stuck)
    (hUnflatElimNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)) ≠
        Term.Stuck)
    (hInputNativeEq :
      ∀ ss rv nextSs nextRv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt nextS) =
          SmtValue.Seq nextSs ->
        __smtx_model_eval M (__eo_to_smt nextR) =
          SmtValue.RegLan nextRv ->
          native_str_in_re (native_unpack_string ss) rv =
            native_str_in_re (native_unpack_string nextSs) nextRv)
    (hSecondNativeEq :
      ∀ nextSs nextRv partsSs reRv,
        __smtx_model_eval M (__eo_to_smt nextS) =
          SmtValue.Seq nextSs ->
        __smtx_model_eval M (__eo_to_smt nextR) =
          SmtValue.RegLan nextRv ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_str second)) =
          SmtValue.Seq partsSs ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_re second)) =
          SmtValue.RegLan reRv ->
          native_str_in_re (native_unpack_string nextSs) nextRv =
            native_str_in_re (native_unpack_string partsSs) reRv) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply StrInReConsumeInternal.str_re_consume_model_rel_of_final_second_native_eq_local M hM
    s r side second hEqTrans hSide hSideNe hPartsList hSecondTy
    hCollectNe hUnflatElimNe
  intro ss rv partsSs reRv hSEval hREval hPartsEval hRePartEval
  rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
      (__eo_to_smt nextS) hNextSTy with
    ⟨nextSs, hNextSEval⟩
  rcases smt_model_eval_reglan_of_type M hM nextR hNextRTy with
    ⟨nextRv, hNextREval⟩
  calc
    native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string nextSs) nextRv :=
      hInputNativeEq ss rv nextSs nextRv hSEval hREval hNextSEval
        hNextREval
    _ = native_str_in_re (native_unpack_string partsSs) reRv :=
      hSecondNativeEq nextSs nextRv partsSs reRv hNextSEval hNextREval
        hPartsEval hRePartEval

theorem StrInReConsumeInternal.str_re_consume_model_rel_of_final_second_parts_local
    (M : SmtModel) (hM : model_wf M)
    (s r side second : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSide :
      side =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect (__str_membership_str second))))
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              (__str_membership_re second))))
    (hSideNe : side ≠ Term.Stuck)
    (hPartsList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_membership_str second) =
        Term.Boolean true)
    (hSecondTy : __smtx_typeof (__eo_to_smt second) = SmtType.Bool)
    (hPartsEvalRel :
      ∀ ss,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          ∃ partsSs,
            __smtx_model_eval M
                (__eo_to_smt (__str_membership_str second)) =
              SmtValue.Seq partsSs ∧
            RuleProofs.smt_value_rel (SmtValue.Seq partsSs)
              (SmtValue.Seq ss))
    (hCollectNe : __str_collect (__str_membership_str second) ≠ Term.Stuck)
    (hRePartEvalRel :
      ∀ rv,
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∃ reRv,
            __smtx_model_eval M
                (__eo_to_smt (__str_membership_re second)) =
              SmtValue.RegLan reRv ∧
            RuleProofs.smt_value_rel (SmtValue.RegLan reRv)
              (SmtValue.RegLan rv))
    (hUnflatElimNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)) ≠
        Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases StrInReConsumeInternal.str_re_consume_final_raw_projection_types_of_second_bool_local
      second hSecondTy hUnflatElimNe with
    ⟨hPartsTy, hRePartTy⟩
  exact str_re_consume_model_rel_of_final_parts_local M hM s r side
    (__str_membership_str second) (__str_membership_re second) hEqTrans
    hSide hSideNe hPartsList hPartsTy hPartsEvalRel hCollectNe
    hRePartTy hRePartEvalRel hUnflatElimNe

theorem StrInReConsumeInternal.str_re_consume_candidate_str_eval_rel_of_second_parts_local
    (M : SmtModel) (hM : model_wf M)
    (s candidate second : Term)
    (hCandidateFinal :
      candidate =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect (__str_membership_str second))))
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              (__str_membership_re second))))
    (hCandidateMem :
      __str_membership_re candidate =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    (hPartsList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_membership_str second) =
        Term.Boolean true)
    (hPartsTy :
      __smtx_typeof (__eo_to_smt (__str_membership_str second)) =
        SmtType.Seq SmtType.Char)
    (hPartsEvalRel :
      ∀ ss,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          ∃ partsSs,
            __smtx_model_eval M
                (__eo_to_smt (__str_membership_str second)) =
              SmtValue.Seq partsSs ∧
            RuleProofs.smt_value_rel (SmtValue.Seq partsSs)
              (SmtValue.Seq ss))
    (hCollectNe : __str_collect (__str_membership_str second) ≠ Term.Stuck) :
    ∀ ss,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        ∃ outSs,
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str candidate)) =
            SmtValue.Seq outSs ∧
          RuleProofs.smt_value_rel (SmtValue.Seq outSs)
            (SmtValue.Seq ss) := by
  intro ss hSEval
  let strPart :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
      (__str_collect (__str_membership_str second))
  let rePart :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
      (__re_unflatten (Term.Boolean true)
        (__str_membership_re second))
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart) rePart
  have hCandidateFinalLocal : candidate = final := by
    simpa [strPart, rePart, final] using hCandidateFinal
  have hCandidateNe : candidate ≠ Term.Stuck := by
    intro hBad
    rw [hBad] at hCandidateMem
    simp [__str_membership_re] at hCandidateMem
  have hFinalNe : final ≠ Term.Stuck := by
    intro hBad
    apply hCandidateNe
    rw [hCandidateFinalLocal, hBad]
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) strPart ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hFinalNe
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) strPart =
        Term.Apply (Term.UOp UserOp.str_in_re) strPart :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re)
      strPart hInnerNe
  have hOuterEq :
      final =
        Term.Apply
          (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart)
          rePart := by
    simpa [final] using
      eo_mk_apply_eq_apply_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart) rePart
        hFinalNe
  have hFinalApply :
      final =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re) strPart) rePart := by
    rw [hOuterEq, hInnerEq]
  have hCandidateStr :
      __str_membership_str candidate = strPart := by
    rw [hCandidateFinalLocal, hFinalApply]
    exact str_membership_str_str_in_re strPart rePart
  rcases hPartsEvalRel ss hSEval with
    ⟨partsSs, hPartsEval, hPartsRel⟩
  rcases str_collect_singleton_elim_eval_rel_local M hM
      (__str_membership_str second) partsSs SmtType.Char hPartsList
      hPartsTy hPartsEval hCollectNe with
    ⟨outSs, hOutEval, hOutRelParts⟩
  exact ⟨outSs, by simpa [hCandidateStr, strPart] using hOutEval,
    RuleProofs.smt_value_rel_trans _ _ _ hOutRelParts hPartsRel⟩

theorem StrInReConsumeInternal.str_re_consume_candidate_str_native_eq_of_second_parts_local
    (M : SmtModel) (hM : model_wf M)
    (s r candidate second : Term)
    (hCandidateFinal :
      candidate =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect (__str_membership_str second))))
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              (__str_membership_re second))))
    (hCandidateMem :
      __str_membership_re candidate =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    (hPartsList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_membership_str second) =
        Term.Boolean true)
    (hPartsTy :
      __smtx_typeof (__eo_to_smt (__str_membership_str second)) =
        SmtType.Seq SmtType.Char)
    (hSecondNativeEq :
      ∀ ss rv partsSs,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_str second)) =
          SmtValue.Seq partsSs ->
        __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              (__str_membership_re second)) =
          Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
          native_str_in_re (native_unpack_string ss) rv =
            native_str_in_re (native_unpack_string partsSs) rv)
    (hCollectNe : __str_collect (__str_membership_str second) ≠ Term.Stuck) :
    ∀ ss rv candSs,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __smtx_model_eval M
          (__eo_to_smt (__str_membership_str candidate)) =
        SmtValue.Seq candSs ->
        native_str_in_re (native_unpack_string ss) rv =
          native_str_in_re (native_unpack_string candSs) rv := by
  intro ss rv candSs hSEval hREval hCandidateEval
  let strPart :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
      (__str_collect (__str_membership_str second))
  let rePart :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
      (__re_unflatten (Term.Boolean true)
        (__str_membership_re second))
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart) rePart
  have hCandidateFinalLocal : candidate = final := by
    simpa [strPart, rePart, final] using hCandidateFinal
  have hCandidateNe : candidate ≠ Term.Stuck := by
    intro hBad
    rw [hBad] at hCandidateMem
    simp [__str_membership_re] at hCandidateMem
  have hFinalNe : final ≠ Term.Stuck := by
    intro hBad
    apply hCandidateNe
    rw [hCandidateFinalLocal, hBad]
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) strPart ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hFinalNe
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) strPart =
        Term.Apply (Term.UOp UserOp.str_in_re) strPart :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re)
      strPart hInnerNe
  have hOuterEq :
      final =
        Term.Apply
          (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart)
          rePart := by
    simpa [final] using
      eo_mk_apply_eq_apply_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart) rePart
        hFinalNe
  have hFinalApply :
      final =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re) strPart) rePart := by
    rw [hOuterEq, hInnerEq]
  have hCandidateStr :
      __str_membership_str candidate = strPart := by
    rw [hCandidateFinalLocal, hFinalApply]
    exact str_membership_str_str_in_re strPart rePart
  rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
      (__eo_to_smt (__str_membership_str second)) hPartsTy with
    ⟨partsSs, hPartsEval⟩
  rcases str_collect_singleton_elim_eval_rel_local M hM
      (__str_membership_str second) partsSs SmtType.Char hPartsList
      hPartsTy hPartsEval hCollectNe with
    ⟨outSs, hOutEval, hOutRelParts⟩
  have hCandOut : SmtValue.Seq candSs = SmtValue.Seq outSs := by
    rw [← hCandidateEval]
    simpa [hCandidateStr, strPart] using hOutEval
  have hPartsSeqTy :
      __smtx_typeof_value (SmtValue.Seq partsSs) =
        SmtType.Seq SmtType.Char := by
    rw [← hPartsEval]
    simpa [hPartsTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt (__str_membership_str second)) (by
          unfold term_has_non_none_type
          rw [hPartsTy]
          simp)
  have hOutPartsNative :
      native_str_in_re (native_unpack_string outSs) rv =
        native_str_in_re (native_unpack_string partsSs) rv :=
    native_str_in_re_eq_of_seq_reglan_rel hPartsSeqTy hOutRelParts
      (RuleProofs.smt_value_rel_refl (SmtValue.RegLan rv))
  have hCandPartsNative :
      native_str_in_re (native_unpack_string candSs) rv =
        native_str_in_re (native_unpack_string partsSs) rv := by
    cases hCandOut
    exact hOutPartsNative
  have hOrigPartsNative :
      native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string partsSs) rv :=
    hSecondNativeEq ss rv partsSs hSEval hREval hPartsEval (by
      have hCandidateRe :
          __str_membership_re candidate = rePart := by
        rw [hCandidateFinalLocal, hFinalApply]
        exact str_membership_re_str_in_re strPart rePart
      have h := hCandidateMem
      rw [hCandidateRe] at h
      simpa [rePart] using h)
  exact hOrigPartsNative.trans hCandPartsNative.symm

theorem StrInReConsumeInternal.str_re_consume_non_mult_first_input_type_facts_local
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    __smtx_typeof (__eo_to_smt sFlat) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt rFlat) = SmtType.RegLan ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sFlat =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_concat) rFlat =
        Term.Boolean true ∧
      first ≠ Term.Stuck ∧
      sFlat ≠ Term.Stuck ∧
      rFlat ≠ Term.Stuck := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, _hSTy, hRTy, _hEqBool⟩
  rcases StrInReConsumeInternal.str_re_consume_non_mult_final_carry_false_local s r side hS hR
      hNotMult hSide hSideNe hSideNotFalse with
    ⟨_hCarryFalse, _hSecondNe, hFirstEqFalse, _hSecondEqFalse⟩
  have hFirstNe : first ≠ Term.Stuck :=
    StrInReConsumeInternal.eo_eq_left_ne_stuck_of_false_local first (Term.Boolean false)
      (by simpa [sFlat, rFlat, first] using hFirstEqFalse)
  have hSFlatNe : sFlat ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck sFlat rFlat sFlat
      hFirstNe
  have hRFlatNe : rFlat ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck sFlat rFlat sFlat
      hFirstNe
  rcases StrInReConsumeInternal.str_re_consume_sflat_type_facts_local M hM s r side hEqTrans
      (by simpa [sFlat, __str_nary_intro] using hSFlatNe) with
    ⟨hSFlatTy, hSFlatList, _hFlatNe, _hFlatList, _hFlatTy⟩
  rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM r hRTy
      (by simpa [rFlat] using hRFlatNe) with
    ⟨hRFlatTy, hRFlatList, _hReFlatNe, _hReFlatList, _hReFlatTy⟩
  exact ⟨hSFlatTy, hRFlatTy, hSFlatList, hRFlatList, hFirstNe,
    hSFlatNe, hRFlatNe⟩

theorem StrInReConsumeInternal.str_re_consume_non_mult_second_input_ne_stuck_facts_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    __str_membership_str first ≠ Term.Stuck ∧
      __str_membership_re first ≠ Term.Stuck ∧
      nextS ≠ Term.Stuck ∧
      nextR ≠ Term.Stuck ∧
      second ≠ Term.Stuck := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean false)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  rcases StrInReConsumeInternal.str_re_consume_non_mult_final_carry_false_local s r side hS hR
      hNotMult hSide hSideNe hSideNotFalse with
    ⟨hCarryFalse, hSecondNe, _hFirstEqFalse, _hSecondEqFalse⟩
  have hCarryFalseLocal : carry = Term.Boolean false := by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
      hCarryFalse
  have hNextSNe : nextS ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck nextS nextR nextS
      (by simpa [second] using hSecondNe)
  have hNextRNe : nextR ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck nextS nextR nextS
      (by simpa [second] using hSecondNe)
  have hIteSNe :
      __eo_ite carry sFlat (__str_membership_str first) ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first)) hNextSNe
  have hMemStrNe : __str_membership_str first ≠ Term.Stuck := by
    simpa [hCarryFalseLocal, eo_ite_false] using hIteSNe
  have hFlatNextRNe :
      __re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first)) ≠
        Term.Stuck :=
    StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps hNextRNe
  have hIteRNe :
      __eo_ite carry rFlat (__str_membership_re first) ≠ Term.Stuck :=
    StrInReConsumeInternal.re_flatten_tree_ne_stuck_of_ne_stuck_local
      (Term.Boolean true)
      (__eo_ite carry rFlat (__str_membership_re first))
      hFlatNextRNe
  have hMemReNe : __str_membership_re first ≠ Term.Stuck := by
    simpa [hCarryFalseLocal, eo_ite_false] using hIteRNe
  exact ⟨hMemStrNe, hMemReNe, hNextSNe, hNextRNe,
    by simpa [second] using hSecondNe⟩

theorem StrInReConsumeInternal.str_re_consume_non_mult_second_type_from_rec_type_local
    (M : SmtModel) (hM : model_wf M)
    (hRecType :
      ∀ s0 r0 fuel0, StrInReConsumeInternal.str_re_consume_rec_type_motive s0 r0 fuel0)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    __smtx_typeof (__eo_to_smt second) = SmtType.Bool := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean false)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  rcases StrInReConsumeInternal.str_re_consume_non_mult_first_input_type_facts_local M hM s r
      side hEqTrans hS hR hNotMult hSide hSideNe hSideNotFalse with
    ⟨hSFlatTy, hRFlatTy, _hSFlatList, _hRFlatList, hFirstNe,
      _hSFlatNe, _hRFlatNe⟩
  rcases StrInReConsumeInternal.str_re_consume_non_mult_second_input_ne_stuck_facts_local s r
      side hS hR hNotMult hSide hSideNe hSideNotFalse with
    ⟨_hMemStrNe, hMemReNe, hNextSNe, hNextRNe, hSecondNe⟩
  have hFirstTy :
      __smtx_typeof (__eo_to_smt first) = SmtType.Bool :=
    hRecType sFlat rFlat sFlat hSFlatTy hRFlatTy hFirstNe
  rcases StrInReConsumeInternal.str_re_consume_rec_projection_types_of_bool_local first
      hFirstTy (by simpa [first] using hMemReNe) with
    ⟨hMemStrTy, hMemReTy⟩
  rcases StrInReConsumeInternal.str_re_consume_non_mult_final_carry_false_local s r side hS hR
      hNotMult hSide hSideNe hSideNotFalse with
    ⟨hCarryFalse, _hSecondNe, _hFirstEqFalse, _hSecondEqFalse⟩
  have hCarryFalseLocal : carry = Term.Boolean false := by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
      hCarryFalse
  have hIteSTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_ite carry sFlat (__str_membership_str first))) =
        SmtType.Seq SmtType.Char := by
    simpa [hCarryFalseLocal, eo_ite_false] using hMemStrTy
  have hIteSList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_ite carry sFlat (__str_membership_str first)) =
        Term.Boolean true := by
    exact eo_list_rev_is_list_true_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
      (by simpa [nextS] using hNextSNe)
  have hNextSTy :
      __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char := by
    simpa [nextS] using
      smt_typeof_list_rev_str_concat_of_seq
        (__eo_ite carry sFlat (__str_membership_str first))
        SmtType.Char hIteSList hIteSTy
        (by simpa [nextS] using hNextSNe)
  have hIteRTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_ite carry rFlat (__str_membership_re first))) =
        SmtType.RegLan := by
    simpa [hCarryFalseLocal, eo_ite_false] using hMemReTy
  have hNextRTy :
      __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan := by
    rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM
        (__eo_ite carry rFlat (__str_membership_re first)) hIteRTy
        (by simpa [nextR] using hNextRNe) with
      ⟨hTy, _hList, _hFlatNe, _hFlatList, _hFlatTy⟩
    simpa [nextR] using hTy
  exact hRecType nextS nextR nextS hNextSTy hNextRTy
    (by simpa [second] using hSecondNe)

theorem StrInReConsumeInternal.str_re_consume_non_mult_model_rel_of_final_second_eval_rels_local
    (M : SmtModel) (hM : model_wf M)
    (hRecType :
      ∀ s0 r0 fuel0, StrInReConsumeInternal.str_re_consume_rec_type_motive s0 r0 fuel0)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hNotMult :
      ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    (∀ ss,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        ∃ partsSs,
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str second)) =
            SmtValue.Seq partsSs ∧
          RuleProofs.smt_value_rel (SmtValue.Seq partsSs)
            (SmtValue.Seq ss)) ->
    (∀ rv,
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        ∃ reRv,
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_re second)) =
            SmtValue.RegLan reRv ∧
          RuleProofs.smt_value_rel (SmtValue.RegLan reRv)
            (SmtValue.RegLan rv)) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  dsimp
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean false)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  intro hPartsEvalRel hRePartEvalRel
  rcases StrInReConsumeInternal.str_re_consume_non_mult_final_subterms_ne_stuck_local s r side
      hS hR hNotMult hSide hSideNe hSideNotFalse with
    ⟨hSideFinal, hCollectNe, hUnflatElimNe⟩
  have hPartsList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_membership_str second) =
        Term.Boolean true :=
    StrInReConsumeInternal.str_collect_arg_is_list_true_of_ne_stuck_local
      (__str_membership_str second)
      (by simpa [second] using hCollectNe)
  have hSecondTy :
      __smtx_typeof (__eo_to_smt second) = SmtType.Bool :=
    StrInReConsumeInternal.str_re_consume_non_mult_second_type_from_rec_type_local M hM hRecType
      s r side hEqTrans hS hR hNotMult hSide hSideNe hSideNotFalse
  exact StrInReConsumeInternal.str_re_consume_model_rel_of_final_second_parts_local M hM s r
    side second hEqTrans
    (by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hSideFinal)
    hSideNe hPartsList hSecondTy hPartsEvalRel
    (by simpa [second] using hCollectNe) hRePartEvalRel
    (by simpa [second] using hUnflatElimNe)

theorem StrInReConsumeInternal.str_re_consume_mult_second_input_ne_stuck_facts_local
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    __str_membership_re first ≠ Term.Stuck ∧
      carry ≠ Term.Stuck ∧
      nextS ≠ Term.Stuck ∧
      nextR ≠ Term.Stuck ∧
      second ≠ Term.Stuck := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean true)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  rcases StrInReConsumeInternal.str_re_consume_mult_final_carry_eq_local s r side hS hSide
      hSideNe hSideNotFalse with
    ⟨hCarryEq, hSecondNe, _hFirstEqFalse, _hSecondEqFalse⟩
  have hCarryEqLocal :
      carry = __eo_not (__eo_eq (__str_membership_re first) eps) := by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
      hCarryEq
  have hNextSNe : nextS ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck nextS nextR nextS
      (by simpa [second] using hSecondNe)
  have hNextRNe : nextR ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck nextS nextR nextS
      (by simpa [second] using hSecondNe)
  have hIteSNe :
      __eo_ite carry sFlat (__str_membership_str first) ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first)) hNextSNe
  have hCarryNe : carry ≠ Term.Stuck := by
    rcases eo_ite_cases_of_ne_stuck carry sFlat
        (__str_membership_str first) hIteSNe with hCarryTrue |
        hCarryFalse
    · rw [hCarryTrue]
      simp
    · rw [hCarryFalse]
      simp
  have hNotNe :
      __eo_not (__eo_eq (__str_membership_re first) eps) ≠ Term.Stuck := by
    simpa [← hCarryEqLocal] using hCarryNe
  have hEqNe :
      __eo_eq (__str_membership_re first) eps ≠ Term.Stuck :=
    StrInReConsumeInternal.eo_not_arg_ne_stuck_of_ne_stuck_local
      (__eo_eq (__str_membership_re first) eps) hNotNe
  have hMemReNe : __str_membership_re first ≠ Term.Stuck :=
    StrInReConsumeInternal.eo_eq_left_ne_stuck_of_ne_stuck_local (__str_membership_re first) eps
      hEqNe
  exact ⟨hMemReNe, hCarryNe, hNextSNe, hNextRNe,
    by simpa [second] using hSecondNe⟩

theorem StrInReConsumeInternal.str_re_consume_mult_first_input_type_facts_local
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r)))
          side))
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s
      (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    __smtx_typeof (__eo_to_smt sFlat) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt rFlat) = SmtType.RegLan ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sFlat =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_concat) rFlat =
        Term.Boolean true ∧
      first ≠ Term.Stuck ∧
      sFlat ≠ Term.Stuck ∧
      rFlat ≠ Term.Stuck := by
  let multR := Term.Apply (Term.UOp UserOp.re_mult) r
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  rcases str_re_consume_translation_facts s multR side (by
      simpa [multR] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, _hSTy, hMultRTy, _hEqBool⟩
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan :=
    StrInReConsumeInternal.re_mult_arg_type_of_reglan_consume_local r
      (by simpa [multR] using hMultRTy)
  rcases StrInReConsumeInternal.str_re_consume_mult_final_carry_eq_local s r side hS hSide
      hSideNe hSideNotFalse with
    ⟨_hCarryEq, _hSecondNe, hFirstEqFalse, _hSecondEqFalse⟩
  have hFirstNe : first ≠ Term.Stuck :=
    StrInReConsumeInternal.eo_eq_left_ne_stuck_of_false_local first (Term.Boolean false)
      (by simpa [sFlat, rFlat, first] using hFirstEqFalse)
  have hSFlatNe : sFlat ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck sFlat rFlat sFlat
      hFirstNe
  have hRFlatNe : rFlat ≠ Term.Stuck :=
    StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck sFlat rFlat sFlat
      hFirstNe
  rcases StrInReConsumeInternal.str_re_consume_sflat_type_facts_local M hM s multR side
      (by simpa [multR] using hEqTrans)
      (by simpa [sFlat, __str_nary_intro] using hSFlatNe) with
    ⟨hSFlatTy, hSFlatList, _hFlatNe, _hFlatList, _hFlatTy⟩
  rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM r hRTy
      (by simpa [rFlat] using hRFlatNe) with
    ⟨hRFlatTy, hRFlatList, _hReFlatNe, _hReFlatList, _hReFlatTy⟩
  exact ⟨hSFlatTy, hRFlatTy, hSFlatList, hRFlatList, hFirstNe,
    hSFlatNe, hRFlatNe⟩

theorem StrInReConsumeInternal.str_re_consume_mult_second_type_from_rec_type_local
    (M : SmtModel) (hM : model_wf M)
    (hRecType :
      ∀ s0 r0 fuel0, StrInReConsumeInternal.str_re_consume_rec_type_motive s0 r0 fuel0)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r)))
          side))
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s
      (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    __smtx_typeof (__eo_to_smt second) = SmtType.Bool := by
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean true)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  rcases StrInReConsumeInternal.str_re_consume_mult_first_input_type_facts_local M hM s r side
      hEqTrans hS hSide hSideNe hSideNotFalse with
    ⟨hSFlatTy, hRFlatTy, _hSFlatList, _hRFlatList, hFirstNe,
      _hSFlatNe, _hRFlatNe⟩
  rcases StrInReConsumeInternal.str_re_consume_mult_second_input_ne_stuck_facts_local s r side
      hS hSide hSideNe hSideNotFalse with
    ⟨hMemReNe, _hCarryNe, hNextSNe, hNextRNe, hSecondNe⟩
  have hFirstTy :
      __smtx_typeof (__eo_to_smt first) = SmtType.Bool :=
    hRecType sFlat rFlat sFlat hSFlatTy hRFlatTy hFirstNe
  rcases StrInReConsumeInternal.str_re_consume_rec_projection_types_of_bool_local first
      hFirstTy (by simpa [first] using hMemReNe) with
    ⟨hMemStrTy, hMemReTy⟩
  have hIteSNe :
      __eo_ite carry sFlat (__str_membership_str first) ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first)) hNextSNe
  have hIteSTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_ite carry sFlat (__str_membership_str first))) =
        SmtType.Seq SmtType.Char :=
    StrInReConsumeInternal.smt_typeof_eo_ite_of_branches_local carry sFlat
      (__str_membership_str first) hSFlatTy hMemStrTy hIteSNe
  have hIteSList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_ite carry sFlat (__str_membership_str first)) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
      (by simpa [nextS] using hNextSNe)
  have hNextSTy :
      __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char := by
    simpa [nextS] using
      smt_typeof_list_rev_str_concat_of_seq
        (__eo_ite carry sFlat (__str_membership_str first))
        SmtType.Char hIteSList hIteSTy
        (by simpa [nextS] using hNextSNe)
  have hFlatNextRNe :
      __re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first)) ≠
        Term.Stuck :=
    StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps hNextRNe
  have hIteRNe :
      __eo_ite carry rFlat (__str_membership_re first) ≠ Term.Stuck :=
    StrInReConsumeInternal.re_flatten_tree_ne_stuck_of_ne_stuck_local
      (Term.Boolean true)
      (__eo_ite carry rFlat (__str_membership_re first)) hFlatNextRNe
  have hIteRTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_ite carry rFlat (__str_membership_re first))) =
        SmtType.RegLan :=
    StrInReConsumeInternal.smt_typeof_eo_ite_of_branches_local carry rFlat
      (__str_membership_re first) hRFlatTy hMemReTy hIteRNe
  have hNextRTy :
      __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan := by
    rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM
        (__eo_ite carry rFlat (__str_membership_re first)) hIteRTy
        (by simpa [nextR] using hNextRNe) with
      ⟨hTy, _hList, _hFlatNe, _hFlatList, _hFlatTy⟩
    simpa [nextR] using hTy
  exact hRecType nextS nextR nextS hNextSTy hNextRTy
    (by simpa [second] using hSecondNe)

theorem StrInReConsumeInternal.str_re_consume_mult_model_rel_of_final_candidate_str_eval_rel_local
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r)))
          side))
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s
      (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false))
        (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    (∀ ss,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        ∃ partsSs,
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str candidate)) =
            SmtValue.Seq partsSs ∧
          RuleProofs.smt_value_rel (SmtValue.Seq partsSs)
            (SmtValue.Seq ss)) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply (Term.UOp UserOp.re_mult) r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  dsimp
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean true)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__str_collect (__str_membership_str second))))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second)))
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false))
      (Term.Boolean false)
      (__eo_ite (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final)
  let rebuild :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__str_membership_str candidate))
      (Term.Apply (Term.UOp UserOp.re_mult) r)
  intro hCandidateStrEvalRel
  rcases StrInReConsumeInternal.str_re_consume_mult_final_eq_local s r side hS hSide hSideNe
      hSideNotFalse with
    ⟨hSideRebuild, _hCandidateFinal, _hCandidateMem⟩
  have hSideRebuildLocal : side = rebuild := by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      final, candidate, rebuild] using hSideRebuild
  have hRebuildNe : rebuild ≠ Term.Stuck := by
    intro hBad
    exact hSideNe (by rw [hSideRebuildLocal, hBad])
  have hSideApply :
      side =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate))
          (Term.Apply (Term.UOp UserOp.re_mult) r) := by
    have hInnerNe :
        __eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate) ≠
          Term.Stuck := by
      simpa [rebuild] using
        eo_mk_apply_fun_ne_stuck_of_ne_stuck
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate))
          (Term.Apply (Term.UOp UserOp.re_mult) r) hRebuildNe
    have hInnerEq :
        __eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate) =
          Term.Apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate) :=
      eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re)
        (__str_membership_str candidate) hInnerNe
    have hOuterEq :
        rebuild =
          Term.Apply
            (__eo_mk_apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str candidate))
            (Term.Apply (Term.UOp UserOp.re_mult) r) := by
      simpa [rebuild] using
        eo_mk_apply_eq_apply_of_ne_stuck
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate))
          (Term.Apply (Term.UOp UserOp.re_mult) r) hRebuildNe
    rw [hSideRebuildLocal, hOuterEq, hInnerEq]
  exact str_re_consume_model_rel_of_side_str_in_re_rel M hM s
    (Term.Apply (Term.UOp UserOp.re_mult) r) side
    (__str_membership_str candidate)
    (Term.Apply (Term.UOp UserOp.re_mult) r) hEqTrans hSideApply
    (by
      intro ss rv hSEval hREval
      rcases hCandidateStrEvalRel ss hSEval with
        ⟨partsSs, hPartsEval, hPartsRel⟩
      exact ⟨partsSs, rv, hPartsEval, hREval, hPartsRel,
        RuleProofs.smt_value_rel_refl (SmtValue.RegLan rv)⟩)

theorem StrInReConsumeInternal.str_re_consume_mult_model_rel_of_final_candidate_native_eq_local
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r)))
          side))
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume s
      (Term.Apply (Term.UOp UserOp.re_mult) r))
    (hSideNe : side ≠ Term.Stuck)
    (hSideNotFalse : side ≠ Term.Boolean false) :
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false))
        (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    (∀ ss rv partsSs,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r)) =
        SmtValue.RegLan rv ->
      __smtx_model_eval M
          (__eo_to_smt (__str_membership_str candidate)) =
        SmtValue.Seq partsSs ->
        native_str_in_re (native_unpack_string ss) rv =
          native_str_in_re (native_unpack_string partsSs) rv) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply (Term.UOp UserOp.re_mult) r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  dsimp
  let sFlat :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__str_flatten (__eo_list_singleton_intro
        (Term.UOp UserOp.str_concat) s))
  let rFlat :=
    __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
  let first := __str_re_consume_rec sFlat rFlat sFlat
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let carry :=
    __eo_and (Term.Boolean true)
      (__eo_not (__eo_eq (__str_membership_re first) eps))
  let nextS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_ite carry sFlat (__str_membership_str first))
  let nextR :=
    __re_rev_map_rev
      (__re_flatten (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first))) eps
  let second := __str_re_consume_rec nextS nextR nextS
  let final :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__str_collect (__str_membership_str second))))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second)))
  let candidate :=
    __eo_ite (__eo_eq first (Term.Boolean false))
      (Term.Boolean false)
      (__eo_ite (__eo_eq second (Term.Boolean false))
        (Term.Boolean false) final)
  let rebuild :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_in_re)
        (__str_membership_str candidate))
      (Term.Apply (Term.UOp UserOp.re_mult) r)
  intro hCandidateNativeEq
  rcases StrInReConsumeInternal.str_re_consume_mult_final_eq_local s r side hS hSide hSideNe
      hSideNotFalse with
    ⟨hSideRebuild, _hCandidateFinal, _hCandidateMem⟩
  have hSideRebuildLocal : side = rebuild := by
    simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
      final, candidate, rebuild] using hSideRebuild
  have hRebuildNe : rebuild ≠ Term.Stuck := by
    intro hBad
    exact hSideNe (by rw [hSideRebuildLocal, hBad])
  have hSideApply :
      side =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate))
          (Term.Apply (Term.UOp UserOp.re_mult) r) := by
    have hInnerNe :
        __eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate) ≠
          Term.Stuck := by
      simpa [rebuild] using
        eo_mk_apply_fun_ne_stuck_of_ne_stuck
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate))
          (Term.Apply (Term.UOp UserOp.re_mult) r) hRebuildNe
    have hInnerEq :
        __eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate) =
          Term.Apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate) :=
      eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re)
        (__str_membership_str candidate) hInnerNe
    have hOuterEq :
        rebuild =
          Term.Apply
            (__eo_mk_apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str candidate))
            (Term.Apply (Term.UOp UserOp.re_mult) r) := by
      simpa [rebuild] using
        eo_mk_apply_eq_apply_of_ne_stuck
          (__eo_mk_apply (Term.UOp UserOp.str_in_re)
            (__str_membership_str candidate))
          (Term.Apply (Term.UOp UserOp.re_mult) r) hRebuildNe
    rw [hSideRebuildLocal, hOuterEq, hInnerEq]
  have hSideTy :=
    str_re_consume_side_smt_type s (Term.Apply (Term.UOp UserOp.re_mult) r)
      side hEqTrans
  rcases StrInReConsumeInternal.str_re_consume_final_args_type_of_side_local side
      (__str_membership_str candidate)
      (Term.Apply (Term.UOp UserOp.re_mult) r) hSideTy hSideRebuildLocal
      hSideNe with
    ⟨hCandidateStrTy, _hMultTy⟩
  exact str_re_consume_model_rel_of_side_native_eval M hM s
    (Term.Apply (Term.UOp UserOp.re_mult) r) side hEqTrans (by
      intro ss rv hSEval hREval
      rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
          (__eo_to_smt (__str_membership_str candidate))
          hCandidateStrTy with
        ⟨partsSs, hPartsEval⟩
      have hPartsSsTy :
          __smtx_typeof_value (SmtValue.Seq partsSs) =
            SmtType.Seq SmtType.Char := by
        rw [← hPartsEval]
        simpa [hCandidateStrTy] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt (__str_membership_str candidate)) (by
              unfold term_has_non_none_type
              rw [hCandidateStrTy]
              simp)
      have hNative :=
        hCandidateNativeEq ss rv partsSs hSEval hREval hPartsEval
      rw [hSideApply]
      change __smtx_model_eval M
          (SmtTerm.str_in_re
            (__eo_to_smt (__str_membership_str candidate))
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r))) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv)
      simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hPartsEval,
        hREval,
        model_str_in_re_unpack_eq_string_of_value_type partsSs rv hPartsSsTy]
      rw [← hNative])

/- ====================================================================
   Unreversed-pair ("unrev") semantics for `__str_re_consume_rec`.

   `__str_re_consume` runs `__str_re_consume_rec` on the REVERSED
   flattened inputs `(sFlat, rFlat)`.  A direct semantic bridge
   between the reversed pair and the original pair of the form

     eval (__re_rev_map_rev (__re_flatten true r) eps)
       ~ StrInReConsumeInternal.native_re_reverse_raw_consume_local rv

   is FALSE in general: `__re_rev_comp` leaves opaque atoms (e.g. a
   RegLan variable `R`, or `str_to_re x` for a string variable `x`)
   unchanged, so for `r := R` the left side evaluates to `rv` itself
   while the right side reverses the model value (`rv = {"ab"}` gives
   `{"ba"}`).  The same failure occurs on the string side:
   `__eo_list_rev` reverses chunk ORDER only, so for a string chunk
   variable `y` the value of `sFlat` is not the reversal of the value
   of `s`.  Hence no per-side single-reversal evaluator lemma exists.

   The correct route avoids single-reversal semantics entirely.  The
   transforms below are exactly the algorithm's own second-pass
   construction (`__eo_list_rev` on the string side and
   `__re_rev_map_rev (__re_flatten true ·) eps` on the regex side).
   Applying them to `(sFlat, rFlat)` recovers terms whose values agree
   with the ORIGINAL `(s, r)` pair via the proven involution lemmas
   (`StrInReConsumeInternal.re_rev_map_rev_comp_action_involutive_local`,
   `eo_list_rev_list_rev_str_concat_eq_of_list_true`), and applying
   them to the residual memberships of a consume result yields exactly
   the `(nextS, nextR)` terms of the second pass.  The three motives
   below mirror the three proven motive families on the flat side
   (`no_prefix` becomes no-SUFFIX, `residual` becomes a LEFT-
   continuation residual, `model_rel` stays a rebuild relation), but
   state their conclusions about the values of the unrev transforms
   of the current pair, so soundness of a `false`/residual result is
   expressed against the original-orientation semantics.  They are to
   be proven by the same `__str_re_consume_rec.induct` scheme as their
   flat counterparts; the per-case cores are snoc/right-cancellation
   analogues of the existing prepend/left cores and are derivable from
   the native reversal toolkit above
   (`StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local` etc.).
   ==================================================================== -/

end RuleProofs
