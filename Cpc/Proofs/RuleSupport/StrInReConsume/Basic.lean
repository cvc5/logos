module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

/-- Keep the model-level extensional equality macro out of `RuleProofs`, where
`native_str_in_re` denotes the string-specialized proof view. -/
private noncomputable def nativeReExtEqConsume
    (r s : SmtRegLan) : native_Bool :=
  native_re_ext_eq r s

namespace RuleProofs

theorem str_re_consume_translation_facts
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) ∧
      RuleProofs.eo_has_smt_translation side ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side) := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation strIn
      side (by simpa [strIn] using hEqTrans) with
    ⟨hStrInTrans, hSideTrans⟩
  rcases str_in_re_args_smt_types_of_has_translation s r hStrInTrans with
    ⟨hSTy, hRTy⟩
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      have hsimpa := hEqTrans
      try simp [strIn] at hsimpa ⊢
      exact hsimpa
    exact Smtm.eq_term_typeof_of_non_none hNN
  exact ⟨hStrInTrans, hSideTrans, hSTy, hRTy, by
    simpa [strIn] using hEqBool⟩

theorem str_re_consume_terms_ne_stuck
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    s ≠ Term.Stuck ∧ r ≠ Term.Stuck ∧ side ≠ Term.Stuck := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, hSideTrans, hSTy, hRTy, _hEqBool⟩
  have hSTrans : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSTy]
    simp
  have hRTrans : RuleProofs.eo_has_smt_translation r := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hRTy]
    simp
  exact ⟨
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans,
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans,
    RuleProofs.term_ne_stuck_of_has_smt_translation side hSideTrans⟩

theorem str_membership_str_str_in_re (s r : Term) :
    __str_membership_str
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) =
      s := by
  rfl

theorem str_membership_re_str_in_re (s r : Term) :
    __str_membership_re
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) =
      r := by
  rfl

theorem str_membership_rebuild_str_in_re
    (s r : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck) :
    __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__str_membership_re
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
  simp [str_membership_str_str_in_re, str_membership_re_str_in_re]
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s ≠ Term.Stuck := by
    cases s <;> simp [__eo_mk_apply] at hS ⊢
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s =
        Term.Apply (Term.UOp UserOp.str_in_re) s :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re) s
      hInnerNe
  have hOuterNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r ≠
        Term.Stuck := by
    cases r <;> simp [__eo_mk_apply] at hR ⊢
  rw [hInnerEq]
  exact eo_mk_apply_eq_apply_of_ne_stuck
    (Term.Apply (Term.UOp UserOp.str_in_re) s) r hOuterNe

theorem str_membership_re_eq_rebuild
    (t r : Term)
    (hRe : __str_membership_re t = r)
    (hRNe : r ≠ Term.Stuck) :
    t =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str t))
        r := by
  cases t <;> simp [__str_membership_re] at hRe hRNe ⊢
  case Apply f x =>
    cases f <;> simp at hRe hRNe ⊢
    case Apply g s =>
      cases g <;> simp at hRe hRNe ⊢
      case UOp op =>
        cases op <;> simp at hRe hRNe ⊢
        case str_in_re =>
          subst r
          simp [__str_membership_str]
        all_goals
          exfalso
          exact hRNe hRe.symm
      all_goals
        exfalso
        exact hRNe hRe.symm
    all_goals
      exfalso
      exact hRNe hRe.symm
  all_goals
    exfalso
    exact hRNe hRe.symm

theorem str_membership_re_eq_eps_rebuild
    (t : Term)
    (hRe :
      __str_membership_re t =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) :
    t =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str t))
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
  exact str_membership_re_eq_rebuild t
    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) hRe (by
      simp)

theorem str_membership_rebuild_of_eo_eq_eps
    (t : Term)
    (hRe :
      __eo_eq (__str_membership_re t)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true) :
    t =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str t))
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
  have hReEq :
      __str_membership_re t =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) :=
    (eq_of_eo_eq_true (__str_membership_re t)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) hRe).symm
  exact str_membership_re_eq_eps_rebuild t hReEq

theorem eo_ite_result_cases
    (c t e z : Term)
    (hNe : __eo_ite c t e ≠ Term.Stuck)
    (hEq : __eo_ite c t e = z) :
    (c = Term.Boolean true ∧ t = z) ∨
      (c = Term.Boolean false ∧ e = z) := by
  rcases eo_ite_cases_of_ne_stuck c t e hNe with hCond | hCond
  · left
    exact ⟨hCond, by simpa [hCond, eo_ite_true] using hEq⟩
  · right
    exact ⟨hCond, by simpa [hCond, eo_ite_false] using hEq⟩

theorem eo_ite_false_result_cases
    (c e : Term)
    (hNe : __eo_ite c (Term.Boolean false) e ≠ Term.Stuck)
    (hEq : __eo_ite c (Term.Boolean false) e = Term.Boolean false) :
    c = Term.Boolean true ∨ e = Term.Boolean false := by
  rcases eo_ite_result_cases c (Term.Boolean false) e
      (Term.Boolean false) hNe hEq with hThen | hElse
  · exact Or.inl hThen.1
  · exact Or.inr hElse.2

theorem eo_and_eq_true_local
    (a b : Term)
    (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;>
    try simp [__eo_and] at h
  case Boolean.Boolean x y =>
    simpa [__eo_and, SmtEval.native_and] using h
  case Binary.Binary w1 n1 w2 n2 =>
    simp [__eo_requires, native_ite, native_teq, native_not] at h
    split at h <;> cases h

theorem StrInReConsumeInternal.eo_and_false_left_eq_false_of_ne_stuck_local
    (x : Term)
    (h : __eo_and (Term.Boolean false) x ≠ Term.Stuck) :
    __eo_and (Term.Boolean false) x = Term.Boolean false := by
  cases x <;> simp [__eo_and, SmtEval.native_and] at h ⊢

theorem StrInReConsumeInternal.eo_and_true_left_eq_arg_of_ne_stuck_local
    (x : Term)
    (h : __eo_and (Term.Boolean true) x ≠ Term.Stuck) :
    __eo_and (Term.Boolean true) x = x := by
  cases x <;> simp [__eo_and, SmtEval.native_and] at h ⊢

theorem StrInReConsumeInternal.eo_not_arg_ne_stuck_of_ne_stuck_local
    (x : Term)
    (h : __eo_not x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hBad
  subst x
  simp [__eo_not] at h

theorem StrInReConsumeInternal.eo_eq_left_ne_stuck_of_ne_stuck_local
    (x y : Term)
    (h : __eo_eq x y ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hBad
  subst x
  cases y <;> simp [__eo_eq] at h

theorem StrInReConsumeInternal.eo_eq_right_ne_stuck_of_ne_stuck_local
    (x y : Term)
    (h : __eo_eq x y ≠ Term.Stuck) :
    y ≠ Term.Stuck := by
  intro hBad
  subst y
  cases x <;> simp [__eo_eq] at h

theorem StrInReConsumeInternal.eo_eq_left_ne_stuck_of_false_local
    (x y : Term)
    (h : __eo_eq x y = Term.Boolean false) :
    x ≠ Term.Stuck := by
  intro hBad
  subst x
  simp [__eo_eq] at h

theorem StrInReConsumeInternal.eo_eq_right_ne_stuck_of_false_local
    (x y : Term)
    (h : __eo_eq x y = Term.Boolean false) :
    y ≠ Term.Stuck := by
  intro hBad
  subst y
  cases x <;> simp [__eo_eq] at h

theorem StrInReConsumeInternal.ne_of_eo_eq_false_local
    (x y : Term)
    (h : __eo_eq x y = Term.Boolean false) :
    x ≠ y := by
  intro hEq
  subst y
  cases x <;> simp [__eo_eq, native_teq] at h

theorem eq_of_eo_is_eq_true_consume_local
    (x y : Term)
    (h : __eo_is_eq x y = Term.Boolean true) :
    x = y := by
  symm
  apply eq_of_eo_eq_true x y
  cases x <;> cases y <;>
    simpa [__eo_is_eq, __eo_eq, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] using h

theorem str_membership_rebuild_of_eo_is_eq_eps
    (t : Term)
    (hRe :
      __eo_is_eq (__str_membership_re t)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true) :
    t =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str t))
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
  have hReEq :
      __str_membership_re t =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) :=
    eq_of_eo_is_eq_true_consume_local (__str_membership_re t)
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) hRe
  exact str_membership_re_eq_eps_rebuild t hReEq

theorem str_re_consume_input_eval
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    ∃ ss rv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hRTy, _hEqBool⟩
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  refine ⟨ss, rv, hSEval, hREval, ?_⟩
  change __smtx_model_eval M
      (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv)
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval, hREval,
    model_str_in_re_unpack_eq_string_of_value_type ss rv hSsTy]

theorem str_re_consume_str_flatten_eval_rel
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hFlatNe : __str_flatten (__str_nary_intro s) ≠ Term.Stuck) :
    ∃ ss flatSs,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M
          (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
        SmtValue.Seq flatSs ∧
      __smtx_typeof
          (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro s)) =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
        (SmtValue.Seq ss) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, _hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, _rv, hSEval, _hREval, _hStrInEval⟩
  rcases str_flatten_nary_intro_eval_rel M hM s ss hSTy hSEval
      hFlatNe with
    ⟨flatSs, hFlatEval, hFlatTy, hFlatList, hFlatRel⟩
  exact ⟨ss, flatSs, hSEval, hFlatEval, hFlatTy, hFlatList, hFlatRel⟩

theorem str_re_consume_re_flatten_false_eval_rel
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hFlatNe :
      __re_flatten (Term.Boolean true) r ≠
        Term.Stuck) :
    ∃ rv flatRv,
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
      __smtx_model_eval M
          (__eo_to_smt
            (__re_flatten (Term.Boolean true) r)) =
        SmtValue.RegLan flatRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_flatten (Term.Boolean true) r)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRv)
        (SmtValue.RegLan rv) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, _hSTy, hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨_ss, rv, _hSEval, hREval, _hStrInEval⟩
  rcases re_flatten_false_eval_rel M hM (Term.Boolean true) r rv
      hRTy hREval hFlatNe with
    ⟨flatRv, hFlatEval, hFlatTy, hFlatRel⟩
  exact ⟨rv, flatRv, hREval, hFlatEval, hFlatTy, hFlatRel⟩

theorem str_re_consume_re_flatten_true_rev_facts
    (r : Term)
    (hRevNe :
      __eo_list_rev (Term.UOp UserOp.re_concat)
          (__re_flatten (Term.Boolean true) r) ≠
        Term.Stuck) :
    __re_flatten (Term.Boolean true) r ≠ Term.Stuck ∧
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__re_flatten (Term.Boolean true) r) =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat)
            (__re_flatten (Term.Boolean true) r)) =
        Term.Boolean true := by
  exact ⟨
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.re_concat)
      (__re_flatten (Term.Boolean true) r) hRevNe,
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.re_concat)
      (__re_flatten (Term.Boolean true) r) hRevNe,
    eo_list_rev_result_is_list_true_of_ne_stuck (Term.UOp UserOp.re_concat)
      (__re_flatten (Term.Boolean true) r) hRevNe⟩

theorem term_ne_stuck_of_smt_seq_type_local
    {t : Term} {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    t ≠ Term.Stuck := by
  intro h
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
  simp at hTy

theorem strConcat_singleton_elim_rel_eval_local
    (M : SmtModel) (hM : model_wf M) (c : Term) (T : SmtType) :
    __eo_is_list (Term.UOp UserOp.str_concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.Seq T ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hcTy
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.str_concat :=
            strConcat_is_list_cons_head_eq_of_true g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.str_concat) tail =
                Term.Boolean true :=
            strConcat_is_list_tail_true_of_cons_self head tail hList
          have hTypes := strConcat_args_of_seq_type head tail T hcTy
          cases hNil : __eo_is_list_nil (Term.UOp UserOp.str_concat) tail
          all_goals
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
              native_teq]
          case Boolean b =>
            cases b
            · exact RuleProofs.smt_value_rel_refl
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) head) tail)))
            · exact RuleProofs.smt_value_rel_symm
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) head) tail)))
                (__smtx_model_eval M (__eo_to_smt head))
                (strConcat_smt_value_rel_list_nil_right_empty M hM
                  head tail T hTypes.1 hNil hTypes.2)
          all_goals
            have hTailNe : tail ≠ Term.Stuck :=
              term_ne_stuck_of_smt_seq_type_local hTypes.2
            cases tail <;>
              simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                __eo_eq, native_teq] at hNil hTailNe
            case UOp1 op A =>
              cases op <;> simp at hNil
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

theorem str_collect_tail_ne_stuck_of_cons_ne_stuck_local
    (head tail : Term)
    (hCollect :
      __str_collect
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail) ≠
        Term.Stuck) :
    __str_collect tail ≠ Term.Stuck := by
  intro hTail
  cases head <;>
    simp [__str_collect, hTail, __str_collect_merge, __eo_ite,
      __eo_mk_apply, native_ite, native_teq] at hCollect

theorem str_collect_merge_tail_ne_stuck_of_ne_stuck_local
    (head tail : Term)
    (hMerge : __str_collect_merge head tail ≠ Term.Stuck) :
    tail ≠ Term.Stuck := by
  intro hTail
  subst tail
  cases head <;> simp [__str_collect_merge] at hMerge

theorem str_collect_merge_cons_eq_of_head_ne_stuck_local
    (head s1 stail : Term)
    (hHead : head ≠ Term.Stuck) :
    __str_collect_merge head
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) stail) =
      __eo_ite (__eo_is_str s1)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (__eo_concat head s1))
          stail)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            stail)) := by
  cases head <;> simp [__str_collect_merge] at hHead ⊢

theorem str_collect_merge_empty_eq_of_head_ne_stuck_local
    (head : Term)
    (hHead : head ≠ Term.Stuck) :
    __str_collect_merge head (Term.String []) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
        (Term.String []) := by
  cases head <;> simp [__str_collect_merge] at hHead ⊢

theorem str_collect_merge_cons_is_list_true_local
    (head s1 stail : Term)
    (hStailList :
      __eo_is_list (Term.UOp UserOp.str_concat) stail = Term.Boolean true)
    (hMerge :
      __str_collect_merge head
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            stail) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__str_collect_merge head
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            stail)) =
      Term.Boolean true := by
  have hHeadNe : head ≠ Term.Stuck := by
    intro hHead
    subst head
    simp [__str_collect_merge] at hMerge
  have hMergeEq :=
    str_collect_merge_cons_eq_of_head_ne_stuck_local head s1 stail
      hHeadNe
  rw [hMergeEq] at hMerge ⊢
  rcases eo_ite_cases_of_ne_stuck (__eo_is_str s1)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (__eo_concat head s1))
        stail)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
          stail)) hMerge with hStr | hStr
  · have hOutNe :
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (__eo_concat head s1))
            stail ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck _ _ _ hMerge hStr
    have hInnerNe :
        __eo_mk_apply (Term.UOp UserOp.str_concat)
            (__eo_concat head s1) ≠
          Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
    have hInnerEq :
        __eo_mk_apply (Term.UOp UserOp.str_concat)
            (__eo_concat head s1) =
          Term.Apply (Term.UOp UserOp.str_concat)
            (__eo_concat head s1) :=
      eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNe
    rw [hStr, eo_ite_true, hInnerEq]
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      simpa [hInnerEq] using hOutNe)]
    exact strConcat_is_list_cons_true_of_tail_list
      (__eo_concat head s1) stail hStailList
  · rw [hStr, eo_ite_false]
    exact strConcat_is_list_cons_true_of_tail_list head
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) stail)
      (strConcat_is_list_cons_true_of_tail_list s1 stail hStailList)

theorem str_collect_merge_empty_is_list_true_local
    (head : Term)
    (hEmptyList :
      __eo_is_list (Term.UOp UserOp.str_concat) (Term.String []) =
        Term.Boolean true)
    (hMerge : __str_collect_merge head (Term.String []) ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__str_collect_merge head (Term.String [])) =
      Term.Boolean true := by
  have hHeadNe : head ≠ Term.Stuck := by
    intro hHead
    subst head
    simp [__str_collect_merge] at hMerge
  rw [str_collect_merge_empty_eq_of_head_ne_stuck_local head hHeadNe]
  exact strConcat_is_list_cons_true_of_tail_list head (Term.String [])
    hEmptyList

theorem str_collect_is_list_true_of_ne_stuck_local :
    ∀ (parts : Term),
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true ->
      __str_collect parts ≠ Term.Stuck ->
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_collect parts) =
        Term.Boolean true := by
  intro parts
  induction parts using __str_collect.induct with
  | case1 =>
      intro hList _hCollect
      simp [__eo_is_list] at hList
  | case2 head tail ih =>
      intro hList hCollect
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        strConcat_is_list_tail_true_of_cons_self head tail hList
      have hTailCollectNe :
          __str_collect tail ≠ Term.Stuck :=
        str_collect_tail_ne_stuck_of_cons_ne_stuck_local head tail
          hCollect
      have hTailCollectList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__str_collect tail) =
            Term.Boolean true :=
        ih hTailList hTailCollectNe
      let collectedTail := __str_collect tail
      have hIteNe :
          __eo_ite (__eo_is_eq (__eo_len head) (Term.Numeral 1))
              (__str_collect_merge head collectedTail)
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail) ≠
            Term.Stuck := by
        simpa [__str_collect, collectedTail] using hCollect
      rcases eo_ite_cases_of_ne_stuck
          (__eo_is_eq (__eo_len head) (Term.Numeral 1))
          (__str_collect_merge head collectedTail)
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_concat) head)
            collectedTail) hIteNe with hLen | hLen
      · have hMergeNe :
            __str_collect_merge head collectedTail ≠ Term.Stuck :=
          eo_ite_then_ne_stuck_of_ne_stuck _ _ _ hIteNe hLen
        cases hCollectedTail : collectedTail with
        | Apply f stail =>
            cases f with
            | Apply g s1 =>
                have hg : g = Term.UOp UserOp.str_concat :=
                  strConcat_is_list_cons_head_eq_of_true g s1 stail
                    (by simpa [collectedTail, hCollectedTail] using
                      hTailCollectList)
                subst g
                have hStailList :
                    __eo_is_list (Term.UOp UserOp.str_concat) stail =
                      Term.Boolean true :=
                  strConcat_is_list_tail_true_of_cons_self s1 stail
                    (by simpa [collectedTail, hCollectedTail] using
                      hTailCollectList)
                rw [__str_collect, hLen, eo_ite_true]
                simpa [collectedTail, hCollectedTail] using
                  str_collect_merge_cons_is_list_true_local head s1
                    stail hStailList (by
                      simpa [collectedTail, hCollectedTail] using hMergeNe)
            | _ =>
                cases head <;>
                  simp [collectedTail, hCollectedTail, __str_collect_merge]
                    at hMergeNe
        | String str =>
            cases str with
            | nil =>
                rw [__str_collect, hLen, eo_ite_true]
                simpa [collectedTail, hCollectedTail] using
                  str_collect_merge_empty_is_list_true_local head
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hTailCollectList)
                    (by
                      simpa [collectedTail, hCollectedTail] using hMergeNe)
            | cons c cs =>
                simp [collectedTail, hCollectedTail, __eo_is_list,
                  __eo_get_nil_rec, __eo_is_list_nil,
                  __eo_is_list_nil_str_concat, __eo_eq, __eo_requires,
                  __eo_is_ok, native_teq, native_ite, SmtEval.native_ite,
                  SmtEval.native_not]
                  at hTailCollectList
        | _ =>
            cases head <;>
              simp [collectedTail, hCollectedTail, __str_collect_merge]
                at hMergeNe
      · have hElseNe :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail ≠
              Term.Stuck :=
          eo_ite_else_ne_stuck_of_ne_stuck _ _ _ hIteNe hLen
        rw [__str_collect, hLen, eo_ite_false]
        rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hElseNe]
        exact strConcat_is_list_cons_true_of_tail_list head collectedTail
          hTailCollectList
  | case3 t _hStuck _hNotConcat =>
      intro hList hCollect
      have hReq :
          __eo_requires t (__seq_empty (__eo_typeof t)) t ≠
            Term.Stuck := by
        simpa [__str_collect] using hCollect
      have hCollectEq :
          __str_collect t = t := by
        simpa [__str_collect] using
          eo_requires_eq_result_of_ne_stuck t (__seq_empty (__eo_typeof t))
            t hReq
      simpa [hCollectEq] using hList

theorem string_seq_type_char_local (w : native_String) (T : SmtType)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.String w)) =
        SmtType.Seq T) :
    T = SmtType.Char := by
  change __smtx_typeof (SmtTerm.String w) = SmtType.Seq T at hTy
  rw [__smtx_typeof.eq_4] at hTy
  cases hValid : native_string_valid w
  · simp [hValid, native_ite] at hTy
  · simp [hValid, native_ite] at hTy
    exact hTy.symm

theorem str_collect_str_concat_string_eval_local
    (M : SmtModel) (x y : native_String) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) (Term.String x))
            (Term.String y))) =
      SmtValue.Seq (native_pack_string (x ++ y)) := by
  change __smtx_model_eval M
      (SmtTerm.str_concat (SmtTerm.String x) (SmtTerm.String y)) =
    SmtValue.Seq (native_pack_string (x ++ y))
  simp [__smtx_model_eval, __smtx_model_eval_str_concat,
    native_seq_concat, native_pack_string, Smtm.native_unpack_pack_seq,
    elem_typeof_pack_seq, List.map_append]

theorem str_collect_eo_concat_string_rel_local
    (M : SmtModel) (x y : native_String) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_concat (Term.String x) (Term.String y))))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) (Term.String x))
            (Term.String y)))) := by
  rw [str_collect_str_concat_string_eval_local M x y]
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (SmtTerm.String (native_str_concat x y)))
    (SmtValue.Seq (native_pack_string (x ++ y)))
  simp [__smtx_model_eval, native_str_concat]
  exact RuleProofs.smt_value_rel_refl _

theorem str_collect_eo_concat_string_type_local
    (x y : native_String) (T : SmtType)
    (hXTy :
      __smtx_typeof (__eo_to_smt (Term.String x)) =
        SmtType.Seq T)
    (hYTy :
      __smtx_typeof (__eo_to_smt (Term.String y)) =
        SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (__eo_concat (Term.String x) (Term.String y))) =
      SmtType.Seq T := by
  have hT : T = SmtType.Char := string_seq_type_char_local x T hXTy
  subst T
  have hXValid :
      native_string_valid x = true :=
    native_string_valid_of_smtx_typeof_eo_string x hXTy
  have hYValid :
      native_string_valid y = true :=
    native_string_valid_of_smtx_typeof_eo_string y hYTy
  change __smtx_typeof (SmtTerm.String (native_str_concat x y)) =
    SmtType.Seq SmtType.Char
  rw [__smtx_typeof.eq_4]
  simp [native_str_concat, native_string_valid_append hXValid hYValid,
    native_ite]

theorem str_collect_eo_concat_string_assoc_rel_local
    (M : SmtModel) (hM : model_wf M)
    (x y : native_String) (tail : Term) (T : SmtType)
    (hXTy :
      __smtx_typeof (__eo_to_smt (Term.String x)) =
        SmtType.Seq T)
    (hYTy :
      __smtx_typeof (__eo_to_smt (Term.String y)) =
        SmtType.Seq T)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat)
              (__eo_concat (Term.String x) (Term.String y)))
            tail)))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) (Term.String x))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String y))
              tail)))) := by
  have hConcatTy :
      __smtx_typeof
          (__eo_to_smt (__eo_concat (Term.String x) (Term.String y))) =
        SmtType.Seq T :=
    str_collect_eo_concat_string_type_local x y T hXTy hYTy
  have hPairTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String x))
              (Term.String y))) =
        SmtType.Seq T :=
    strConcat_typeof_concat_of_seq (Term.String x) (Term.String y) T
      hXTy hYTy
  have hLeft :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (__eo_concat (Term.String x) (Term.String y)))
              tail)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat)
                    (Term.String x))
                  (Term.String y)))
              tail))) :=
    strConcat_smt_value_rel_left_congr M hM
      (__eo_concat (Term.String x) (Term.String y))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.str_concat) (Term.String x))
        (Term.String y))
      tail T hConcatTy hPairTy hTailTy
      (str_collect_eo_concat_string_rel_local M x y)
  have hAssoc :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat)
                    (Term.String x))
                  (Term.String y)))
              tail)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String x))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String y))
                tail)))) :=
    smt_value_rel_str_concat_assoc M hM
      (Term.String x) (Term.String y) tail T hXTy hYTy hTailTy
  exact RuleProofs.smt_value_rel_trans _ _ _ hLeft hAssoc

theorem str_collect_merge_cons_type_local
    (head s1 stail : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq T)
    (hStailTy : __smtx_typeof (__eo_to_smt stail) = SmtType.Seq T)
    (hMerge :
      __str_collect_merge head
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            stail) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__str_collect_merge head
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
              stail))) =
      SmtType.Seq T := by
  have hHeadNe : head ≠ Term.Stuck := by
    intro hHead
    subst head
    simp [__str_collect_merge] at hMerge
  have hMergeEq :=
    str_collect_merge_cons_eq_of_head_ne_stuck_local head s1 stail
      hHeadNe
  rw [hMergeEq] at hMerge ⊢
  rcases eo_ite_cases_of_ne_stuck (__eo_is_str s1)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (__eo_concat head s1))
        stail)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
          stail)) hMerge with hStr | hStr
  · have hOutNe :
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (__eo_concat head s1))
            stail ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck _ _ _ hMerge hStr
    have hInnerNe :
        __eo_mk_apply (Term.UOp UserOp.str_concat)
            (__eo_concat head s1) ≠
          Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
    have hConcatNe :
        __eo_concat head s1 ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
    rcases eo_is_str_eq_true_cases s1 hStr with ⟨ys, rfl⟩
    cases head <;> simp [__eo_concat] at hConcatNe
    case String xs =>
      have hConcatTy :
          __smtx_typeof
              (__eo_to_smt
                (__eo_concat (Term.String xs) (Term.String ys))) =
            SmtType.Seq T :=
        str_collect_eo_concat_string_type_local xs ys T hHeadTy hS1Ty
      have hInnerEq :
          __eo_mk_apply (Term.UOp UserOp.str_concat)
              (__eo_concat (Term.String xs) (Term.String ys)) =
            Term.Apply (Term.UOp UserOp.str_concat)
              (__eo_concat (Term.String xs) (Term.String ys)) :=
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNe
      have hOutNe' :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (__eo_concat (Term.String xs) (Term.String ys)))
              stail ≠
            Term.Stuck := by
        simpa [hInnerEq] using hOutNe
      have hOutEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (__eo_concat (Term.String xs) (Term.String ys)))
              stail =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (__eo_concat (Term.String xs) (Term.String ys)))
              stail :=
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hOutNe'
      rw [hStr, eo_ite_true, hInnerEq, hOutEq]
      exact strConcat_typeof_concat_of_seq
        (__eo_concat (Term.String xs) (Term.String ys)) stail T
        hConcatTy hStailTy
  · rw [hStr, eo_ite_false]
    exact strConcat_typeof_concat_of_seq head
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) stail)
      T hHeadTy
      (strConcat_typeof_concat_of_seq s1 stail T hS1Ty hStailTy)

theorem str_collect_merge_cons_eval_rel_local
    (M : SmtModel) (hM : model_wf M)
    (head s1 stail : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq T)
    (hStailTy : __smtx_typeof (__eo_to_smt stail) = SmtType.Seq T)
    (hMerge :
      __str_collect_merge head
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            stail) ≠
        Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__str_collect_merge head
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
              stail))))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
              stail)))) := by
  have hHeadNe : head ≠ Term.Stuck := by
    intro hHead
    subst head
    simp [__str_collect_merge] at hMerge
  have hMergeEq :=
    str_collect_merge_cons_eq_of_head_ne_stuck_local head s1 stail
      hHeadNe
  rw [hMergeEq] at hMerge ⊢
  rcases eo_ite_cases_of_ne_stuck (__eo_is_str s1)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (__eo_concat head s1))
        stail)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
          stail)) hMerge with hStr | hStr
  · have hOutNe :
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (__eo_concat head s1))
            stail ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck _ _ _ hMerge hStr
    have hInnerNe :
        __eo_mk_apply (Term.UOp UserOp.str_concat)
            (__eo_concat head s1) ≠
          Term.Stuck :=
      eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOutNe
    have hConcatNe :
        __eo_concat head s1 ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
    rcases eo_is_str_eq_true_cases s1 hStr with ⟨ys, rfl⟩
    cases head <;> simp [__eo_concat] at hConcatNe
    case String xs =>
      have hInnerEq :
          __eo_mk_apply (Term.UOp UserOp.str_concat)
              (__eo_concat (Term.String xs) (Term.String ys)) =
            Term.Apply (Term.UOp UserOp.str_concat)
              (__eo_concat (Term.String xs) (Term.String ys)) :=
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNe
      have hOutNe' :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (__eo_concat (Term.String xs) (Term.String ys)))
              stail ≠
            Term.Stuck := by
        simpa [hInnerEq] using hOutNe
      have hOutEq :
          __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (__eo_concat (Term.String xs) (Term.String ys)))
              stail =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (__eo_concat (Term.String xs) (Term.String ys)))
              stail :=
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hOutNe'
      rw [hStr, eo_ite_true, hInnerEq, hOutEq]
      exact str_collect_eo_concat_string_assoc_rel_local M hM xs ys
        stail T hHeadTy hS1Ty hStailTy
  · rw [hStr, eo_ite_false]
    exact RuleProofs.smt_value_rel_refl _

theorem str_collect_merge_empty_type_local
    (head : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hEmptyTy :
      __smtx_typeof (__eo_to_smt (Term.String [])) = SmtType.Seq T)
    (hMerge : __str_collect_merge head (Term.String []) ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__str_collect_merge head (Term.String []))) =
      SmtType.Seq T := by
  have hHeadNe : head ≠ Term.Stuck := by
    intro hHead
    subst head
    simp [__str_collect_merge] at hMerge
  rw [str_collect_merge_empty_eq_of_head_ne_stuck_local head hHeadNe]
  exact strConcat_typeof_concat_of_seq head (Term.String []) T
    hHeadTy hEmptyTy

theorem str_collect_merge_empty_eval_rel_local
    (M : SmtModel) (head : Term)
    (hMerge : __str_collect_merge head (Term.String []) ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__str_collect_merge head (Term.String []))))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
            (Term.String [])))) := by
  have hHeadNe : head ≠ Term.Stuck := by
    intro hHead
    subst head
    simp [__str_collect_merge] at hMerge
  rw [str_collect_merge_empty_eq_of_head_ne_stuck_local head hHeadNe]
  exact RuleProofs.smt_value_rel_refl _

theorem str_collect_eval_rel_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ (parts : Term) (ss : SmtSeq) (T : SmtType),
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true ->
      __smtx_typeof (__eo_to_smt parts) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt parts) = SmtValue.Seq ss ->
      __str_collect parts ≠ Term.Stuck ->
      ∃ collectedSs,
        __smtx_model_eval M (__eo_to_smt (__str_collect parts)) =
          SmtValue.Seq collectedSs ∧
        __smtx_typeof (__eo_to_smt (__str_collect parts)) =
          SmtType.Seq T ∧
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__str_collect parts) =
          Term.Boolean true ∧
        RuleProofs.smt_value_rel (SmtValue.Seq collectedSs)
          (SmtValue.Seq ss) := by
  intro parts
  induction parts using __str_collect.induct with
  | case1 =>
      intro ss T hList _hTy _hEval _hCollect
      simp [__eo_is_list] at hList
  | case2 head tail ih =>
      intro ss T hList hTy hEval hCollect
      have hArgs := strConcat_args_of_seq_type head tail T hTy
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        strConcat_is_list_tail_true_of_cons_self head tail hList
      have hTailEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt tail)) =
            SmtType.Seq T := by
        simpa [hArgs.2] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt tail) (by
              unfold term_has_non_none_type
              rw [hArgs.2]
              simp)
      rcases seq_value_canonical hTailEvalTy with ⟨tailSs, hTailEval⟩
      have hTailCollectNe :
          __str_collect tail ≠ Term.Stuck :=
        str_collect_tail_ne_stuck_of_cons_ne_stuck_local head tail
          hCollect
      rcases ih tailSs T hTailList hArgs.2 hTailEval hTailCollectNe with
        ⟨collectedTailSs, hTailCollectEval, hTailCollectTy,
          hTailCollectList, hTailCollectRel⟩
      let collectedTail := __str_collect tail
      have hTailRelEval :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt collectedTail))
            (__smtx_model_eval M (__eo_to_smt tail)) := by
        simpa [collectedTail, hTailCollectEval, hTailEval] using
          hTailCollectRel
      have hCollectList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__str_collect
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head)
                  tail)) =
            Term.Boolean true :=
        str_collect_is_list_true_of_ne_stuck_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail)
          hList hCollect
      have hIteNe :
          __eo_ite (__eo_is_eq (__eo_len head) (Term.Numeral 1))
              (__str_collect_merge head collectedTail)
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail) ≠
            Term.Stuck := by
        simpa [__str_collect, collectedTail] using hCollect
      rcases eo_ite_cases_of_ne_stuck
          (__eo_is_eq (__eo_len head) (Term.Numeral 1))
          (__str_collect_merge head collectedTail)
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_concat) head)
            collectedTail) hIteNe with hLen | hLen
      · have hMergeNe :
            __str_collect_merge head collectedTail ≠ Term.Stuck :=
          eo_ite_then_ne_stuck_of_ne_stuck _ _ _ hIteNe hLen
        cases hCollectedTail : collectedTail with
        | Apply f stail =>
            cases f with
            | Apply g s1 =>
                have hg : g = Term.UOp UserOp.str_concat :=
                  strConcat_is_list_cons_head_eq_of_true g s1 stail
                    (by simpa [collectedTail, hCollectedTail] using
                      hTailCollectList)
                subst g
                have hTailCollectArgs :=
                  strConcat_args_of_seq_type s1 stail T
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hTailCollectTy)
                have hMergeTy :
                    __smtx_typeof
                        (__eo_to_smt
                          (__str_collect_merge head
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_concat) s1)
                              stail))) =
                      SmtType.Seq T :=
                  str_collect_merge_cons_type_local head s1 stail T
                    hArgs.1 hTailCollectArgs.1 hTailCollectArgs.2
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hMergeNe)
                have hMergeRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (__str_collect_merge head
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_concat) s1)
                              stail))))
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) head)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_concat) s1)
                              stail)))) :=
                  str_collect_merge_cons_eval_rel_local M hM head s1
                    stail T hArgs.1 hTailCollectArgs.1
                    hTailCollectArgs.2
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hMergeNe)
                have hRightRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) head)
                            collectedTail)))
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) head)
                            tail))) :=
                  strConcat_smt_value_rel_right_congr M hM head
                    collectedTail tail T hArgs.1 hTailCollectTy hArgs.2
                    hTailRelEval
                have hAllRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (__str_collect_merge head
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_concat) s1)
                              stail))))
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) head)
                            tail))) :=
                  RuleProofs.smt_value_rel_trans _ _ _ hMergeRel
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hRightRel)
                have hOutEvalTy :
                    __smtx_typeof_value
                        (__smtx_model_eval M
                          (__eo_to_smt
                            (__str_collect_merge head
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp.str_concat) s1)
                                stail)))) =
                      SmtType.Seq T := by
                  simpa [hMergeTy] using
                    smt_model_eval_preserves_type_of_non_none M hM
                      (__eo_to_smt
                        (__str_collect_merge head
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) s1)
                            stail))) (by
                        unfold term_has_non_none_type
                        rw [hMergeTy]
                        simp)
                rcases seq_value_canonical hOutEvalTy with
                  ⟨outSs, hOutEval⟩
                refine ⟨outSs, ?_, ?_, ?_, ?_⟩
                · rw [__str_collect, hLen, eo_ite_true]
                  simpa [collectedTail, hCollectedTail] using hOutEval
                · rw [__str_collect, hLen, eo_ite_true]
                  simpa [collectedTail, hCollectedTail] using hMergeTy
                · simpa using hCollectList
                · rw [hOutEval, hEval] at hAllRel; exact hAllRel
            | _ =>
                cases head <;>
                  simp [collectedTail, hCollectedTail, __str_collect_merge]
                    at hMergeNe
        | String str =>
            cases str with
            | nil =>
                have hEmptyTy :
                    __smtx_typeof (__eo_to_smt (Term.String [])) =
                      SmtType.Seq T := by
                  simpa [collectedTail, hCollectedTail] using
                    hTailCollectTy
                have hMergeTy :
                    __smtx_typeof
                        (__eo_to_smt
                          (__str_collect_merge head (Term.String []))) =
                      SmtType.Seq T :=
                  str_collect_merge_empty_type_local head T hArgs.1
                    hEmptyTy
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hMergeNe)
                have hMergeRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (__str_collect_merge head (Term.String []))))
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) head)
                            (Term.String [])))) :=
                  str_collect_merge_empty_eval_rel_local M head
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hMergeNe)
                have hRightRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) head)
                            collectedTail)))
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) head)
                            tail))) :=
                  strConcat_smt_value_rel_right_congr M hM head
                    collectedTail tail T hArgs.1 hTailCollectTy hArgs.2
                    hTailRelEval
                have hAllRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (__str_collect_merge head (Term.String []))))
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) head)
                            tail))) :=
                  RuleProofs.smt_value_rel_trans _ _ _ hMergeRel
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hRightRel)
                have hOutEvalTy :
                    __smtx_typeof_value
                        (__smtx_model_eval M
                          (__eo_to_smt
                            (__str_collect_merge head (Term.String [])))) =
                      SmtType.Seq T := by
                  simpa [hMergeTy] using
                    smt_model_eval_preserves_type_of_non_none M hM
                      (__eo_to_smt
                        (__str_collect_merge head (Term.String []))) (by
                        unfold term_has_non_none_type
                        rw [hMergeTy]
                        simp)
                rcases seq_value_canonical hOutEvalTy with
                  ⟨outSs, hOutEval⟩
                refine ⟨outSs, ?_, ?_, ?_, ?_⟩
                · rw [__str_collect, hLen, eo_ite_true]
                  simpa [collectedTail, hCollectedTail] using hOutEval
                · rw [__str_collect, hLen, eo_ite_true]
                  simpa [collectedTail, hCollectedTail] using hMergeTy
                · simpa using hCollectList
                · rw [hOutEval, hEval] at hAllRel; exact hAllRel
            | cons c cs =>
                simp [collectedTail, hCollectedTail, __eo_is_list,
                  __eo_get_nil_rec, __eo_is_list_nil,
                  __eo_is_list_nil_str_concat, __eo_eq, __eo_requires,
                  __eo_is_ok, native_teq, native_ite, SmtEval.native_ite,
                  SmtEval.native_not]
                  at hTailCollectList
        | _ =>
            cases head <;>
              simp [collectedTail, hCollectedTail, __str_collect_merge]
                at hMergeNe
      · have hElseNe :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail ≠
              Term.Stuck :=
          eo_ite_else_ne_stuck_of_ne_stuck _ _ _ hIteNe hLen
        have hElseEq :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail :=
          eo_mk_apply_eq_apply_of_ne_stuck _ _ hElseNe
        have hOutTy :
            __smtx_typeof
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) head)
                    collectedTail)) =
              SmtType.Seq T :=
          strConcat_typeof_concat_of_seq head collectedTail T
            hArgs.1 hTailCollectTy
        have hRightRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) head)
                    collectedTail)))
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) head)
                    tail))) :=
          strConcat_smt_value_rel_right_congr M hM head collectedTail
            tail T hArgs.1 hTailCollectTy hArgs.2 hTailRelEval
        have hOutEvalTy :
            __smtx_typeof_value
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) head)
                      collectedTail))) =
              SmtType.Seq T := by
          have hsimpa :=
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head)
                  collectedTail)) (by
                unfold term_has_non_none_type
                rw [hOutTy]
                simp)
          rw [hOutTy] at hsimpa
          exact hsimpa
        rcases seq_value_canonical hOutEvalTy with ⟨outSs, hOutEval⟩
        refine ⟨outSs, ?_, ?_, ?_, ?_⟩
        · rw [__str_collect, hLen, eo_ite_false, hElseEq]
          exact hOutEval
        · rw [__str_collect, hLen, eo_ite_false, hElseEq]
          exact hOutTy
        · simpa using hCollectList
        · rw [hOutEval, hEval] at hRightRel; exact hRightRel
  | case3 t _hStuck _hNotConcat =>
      intro ss T hList hTy hEval hCollect
      have hReq :
          __eo_requires t (__seq_empty (__eo_typeof t)) t ≠
            Term.Stuck := by
        simpa [__str_collect] using hCollect
      have hCollectEq :
          __str_collect t = t := by
        simpa [__str_collect] using
          eo_requires_eq_result_of_ne_stuck t (__seq_empty (__eo_typeof t))
            t hReq
      refine ⟨ss, ?_, ?_, ?_, ?_⟩
      · simpa [hCollectEq] using hEval
      · simpa [hCollectEq] using hTy
      · simpa [hCollectEq] using hList
      · exact RuleProofs.smt_value_rel_refl (SmtValue.Seq ss)

theorem str_collect_singleton_elim_eval_rel_local
    (M : SmtModel) (hM : model_wf M)
    (parts : Term) (ss : SmtSeq) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true)
    (hTy : __smtx_typeof (__eo_to_smt parts) = SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt parts) = SmtValue.Seq ss)
    (hCollect :
      __str_collect parts ≠ Term.Stuck) :
    ∃ outSs,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect parts))) =
        SmtValue.Seq outSs ∧
      RuleProofs.smt_value_rel (SmtValue.Seq outSs) (SmtValue.Seq ss) := by
  rcases str_collect_eval_rel_local M hM parts ss T hList hTy hEval
      hCollect with
    ⟨collectedSs, hCollectEval, hCollectTy, hCollectList,
      hCollectRel⟩
  have hSingletonRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect parts))))
        (__smtx_model_eval M (__eo_to_smt (__str_collect parts))) :=
    strConcat_singleton_elim_rel_eval_local M hM (__str_collect parts)
      T hCollectList hCollectTy
  have hAllRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect parts))))
        (SmtValue.Seq ss) :=
    RuleProofs.smt_value_rel_trans _ _ _ hSingletonRel
      (by simpa [hCollectEval] using hCollectRel)
  rcases smt_value_rel_seq_right hAllRel with
    ⟨outSs, hOutEval, hOutRel⟩
  exact ⟨outSs, hOutEval, by
    simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using
      hOutRel⟩

theorem strConcat_singleton_elim_type_local
    (c : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) c = Term.Boolean true)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)) =
      SmtType.Seq T := by
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))) =
    SmtType.Seq T
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.str_concat :=
            strConcat_is_list_cons_head_eq_of_true g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.str_concat) tail =
                Term.Boolean true :=
            strConcat_is_list_tail_true_of_cons_self head tail hList
          have hTypes := strConcat_args_of_seq_type head tail T hcTy
          cases hNil : __eo_is_list_nil (Term.UOp UserOp.str_concat) tail
          all_goals
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
              native_ite, native_teq]
          case Boolean b =>
            cases b
            · exact hcTy
            · exact hTypes.1
          all_goals
            have hTailNe : tail ≠ Term.Stuck :=
              term_ne_stuck_of_smt_seq_type_local hTypes.2
            cases tail <;>
              simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                __eo_eq, native_teq] at hNil hTailNe
            case UOp1 op A =>
              cases op <;> simp at hNil
      | _ =>
          simpa [__eo_list_singleton_elim_2] using hcTy
  | _ =>
      simpa [__eo_list_singleton_elim_2] using hcTy

theorem str_collect_type_local :
    ∀ (parts : Term) (T : SmtType),
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true ->
      __smtx_typeof (__eo_to_smt parts) = SmtType.Seq T ->
      __str_collect parts ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__str_collect parts)) =
        SmtType.Seq T := by
  intro parts
  induction parts using __str_collect.induct with
  | case1 =>
      intro T hList _hTy _hCollect
      simp [__eo_is_list] at hList
  | case2 head tail ih =>
      intro T hList hTy hCollect
      have hArgs := strConcat_args_of_seq_type head tail T hTy
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        strConcat_is_list_tail_true_of_cons_self head tail hList
      have hTailCollectNe :
          __str_collect tail ≠ Term.Stuck :=
        str_collect_tail_ne_stuck_of_cons_ne_stuck_local head tail
          hCollect
      have hTailCollectTy :
          __smtx_typeof (__eo_to_smt (__str_collect tail)) =
            SmtType.Seq T :=
        ih T hTailList hArgs.2 hTailCollectNe
      have hTailCollectList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__str_collect tail) =
            Term.Boolean true :=
        str_collect_is_list_true_of_ne_stuck_local tail hTailList
          hTailCollectNe
      let collectedTail := __str_collect tail
      have hIteNe :
          __eo_ite (__eo_is_eq (__eo_len head) (Term.Numeral 1))
              (__str_collect_merge head collectedTail)
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail) ≠
            Term.Stuck := by
        simpa [__str_collect, collectedTail] using hCollect
      rcases eo_ite_cases_of_ne_stuck
          (__eo_is_eq (__eo_len head) (Term.Numeral 1))
          (__str_collect_merge head collectedTail)
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_concat) head)
            collectedTail) hIteNe with hLen | hLen
      · have hMergeNe :
            __str_collect_merge head collectedTail ≠ Term.Stuck :=
          eo_ite_then_ne_stuck_of_ne_stuck _ _ _ hIteNe hLen
        cases hCollectedTail : collectedTail with
        | Apply f stail =>
            cases f with
            | Apply g s1 =>
                have hg : g = Term.UOp UserOp.str_concat :=
                  strConcat_is_list_cons_head_eq_of_true g s1 stail
                    (by simpa [collectedTail, hCollectedTail] using
                      hTailCollectList)
                subst g
                have hTailCollectArgs :=
                  strConcat_args_of_seq_type s1 stail T
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hTailCollectTy)
                rw [__str_collect, hLen, eo_ite_true]
                simpa [collectedTail, hCollectedTail] using
                  str_collect_merge_cons_type_local head s1 stail T
                    hArgs.1 hTailCollectArgs.1 hTailCollectArgs.2
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hMergeNe)
            | _ =>
                cases head <;>
                  simp [collectedTail, hCollectedTail, __str_collect_merge]
                    at hMergeNe
        | String str =>
            cases str with
            | nil =>
                have hEmptyTy :
                    __smtx_typeof (__eo_to_smt (Term.String [])) =
                      SmtType.Seq T := by
                  simpa [collectedTail, hCollectedTail] using
                    hTailCollectTy
                rw [__str_collect, hLen, eo_ite_true]
                simpa [collectedTail, hCollectedTail] using
                  str_collect_merge_empty_type_local head T hArgs.1
                    hEmptyTy
                    (by
                      simpa [collectedTail, hCollectedTail] using
                        hMergeNe)
            | cons c cs =>
                simp [collectedTail, hCollectedTail, __eo_is_list,
                  __eo_get_nil_rec, __eo_is_list_nil,
                  __eo_is_list_nil_str_concat, __eo_eq, __eo_requires,
                  __eo_is_ok, native_teq, native_ite, SmtEval.native_ite,
                  SmtEval.native_not]
                  at hTailCollectList
        | _ =>
            cases head <;>
              simp [collectedTail, hCollectedTail, __str_collect_merge]
                at hMergeNe
      · have hElseNe :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail ≠
              Term.Stuck :=
          eo_ite_else_ne_stuck_of_ne_stuck _ _ _ hIteNe hLen
        have hElseEq :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head)
                collectedTail :=
          eo_mk_apply_eq_apply_of_ne_stuck _ _ hElseNe
        rw [__str_collect, hLen, eo_ite_false, hElseEq]
        exact strConcat_typeof_concat_of_seq head collectedTail T
          hArgs.1 hTailCollectTy
  | case3 t _hStuck _hNotConcat =>
      intro T _hList hTy hCollect
      have hReq :
          __eo_requires t (__seq_empty (__eo_typeof t)) t ≠
            Term.Stuck := by
        simpa [__str_collect] using hCollect
      have hCollectEq :
          __str_collect t = t := by
        simpa [__str_collect] using
          eo_requires_eq_result_of_ne_stuck t (__seq_empty (__eo_typeof t))
            t hReq
      simpa [hCollectEq] using hTy

theorem str_collect_singleton_elim_type_local
    (parts : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true)
    (hTy : __smtx_typeof (__eo_to_smt parts) = SmtType.Seq T)
    (hCollect :
      __str_collect parts ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect parts))) =
      SmtType.Seq T := by
  have hCollectList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_collect parts) =
        Term.Boolean true :=
    str_collect_is_list_true_of_ne_stuck_local parts hList hCollect
  have hCollectTy :
      __smtx_typeof (__eo_to_smt (__str_collect parts)) =
        SmtType.Seq T :=
    str_collect_type_local parts T hList hTy hCollect
  exact strConcat_singleton_elim_type_local (__str_collect parts) T
    hCollectList hCollectTy

theorem smt_value_rel_of_native_includes_local
    {r s : SmtRegLan}
    (hrs : NativeIncludes r s) (hsr : NativeIncludes s r) :
    RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    rw [← native_str_in_re_eq_model] at hMem ⊢
    exact hsr str hValid hMem
  · intro hMem
    rw [← native_str_in_re_eq_model] at hMem ⊢
    exact hrs str hValid hMem

theorem smt_value_rel_re_concat_consume_local
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat r s))
      (SmtValue.RegLan (native_re_concat r' s')) := by
  exact smt_value_rel_of_native_includes_local
    (native_includes_concat (native_includes_of_smt_value_rel hr)
      (native_includes_of_smt_value_rel hs))
    (native_includes_concat
      (native_includes_of_smt_value_rel
        (RuleProofs.smt_value_rel_symm _ _ hr))
      (native_includes_of_smt_value_rel
        (RuleProofs.smt_value_rel_symm _ _ hs)))

theorem smt_value_rel_re_concat_assoc_consume_local
    (r s t : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_concat (native_re_concat r s) t))
      (SmtValue.RegLan (native_re_concat r (native_re_concat s t))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str _, ← native_str_in_re_eq_model str _]
  have hsimpa :=
    nativeListInRe_mk_concat_assoc str r s t
  try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
  exact hsimpa

theorem native_str_in_re_re_concat_assoc_consume_local
    (str : native_String) (r s t : SmtRegLan) :
    native_str_in_re str (native_re_concat (native_re_concat r s) t) =
      native_str_in_re str (native_re_concat r (native_re_concat s t)) := by
  by_cases hValid : native_string_valid str = true
  · have hsimpa := nativeListInRe_mk_concat_assoc str r s t; (try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢); exact hsimpa
  · simp [native_str_in_re, hValid]

theorem native_str_in_re_re_union_right_none_consume_local
    (str : native_String) (r : SmtRegLan) :
    native_str_in_re str (native_re_union r native_re_none) =
      native_str_in_re str r := by
  have hUnionNoneRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan (native_re_union r native_re_none))
        (SmtValue.RegLan r) := by
    apply smt_value_rel_of_native_includes_local
    · exact native_includes_union_left r native_re_none
    · intro xs _hValid hMem
      simpa [native_str_in_re_re_union, native_str_in_re_re_none] using hMem
  by_cases hValid : native_string_valid str = true
  · simpa only [native_str_in_re_eq_model] using
      smt_value_rel_reglan_valid_eq hUnionNoneRel hValid
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_inter_right_all_consume_local
    (str : native_String) (r : SmtRegLan) :
    native_str_in_re str (native_re_inter r native_re_all) =
      native_str_in_re str r := by
  have hInterAllRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan (native_re_inter r native_re_all))
        (SmtValue.RegLan r) := by
    apply smt_value_rel_of_native_includes_local
    · intro xs hValid hMem
      rw [native_str_in_re_re_inter]
      simp [hMem, native_str_in_re_re_all xs hValid]
    · exact native_includes_inter_left r native_re_all
  by_cases hValid : native_string_valid str = true
  · simpa only [native_str_in_re_eq_model] using
      smt_value_rel_reglan_valid_eq hInterAllRel hValid
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_concat_union_right_none_consume_local
    (str : native_String) (r q : SmtRegLan) :
    native_str_in_re str
        (native_re_concat (native_re_union r native_re_none) q) =
      native_str_in_re str (native_re_concat r q) := by
  have hUnionNoneRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan (native_re_union r native_re_none))
        (SmtValue.RegLan r) := by
    apply smt_value_rel_of_native_includes_local
    · exact native_includes_union_left r native_re_none
    · intro xs _hValid hMem
      simpa [native_str_in_re_re_union, native_str_in_re_re_none] using hMem
  have hConcatRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_re_concat (native_re_union r native_re_none) q))
        (SmtValue.RegLan (native_re_concat r q)) :=
    smt_value_rel_re_concat_consume_local hUnionNoneRel
      (RuleProofs.smt_value_rel_refl (SmtValue.RegLan q))
  by_cases hValid : native_string_valid str = true
  · simpa only [native_str_in_re_eq_model] using
      smt_value_rel_reglan_valid_eq hConcatRel hValid
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_concat_inter_right_all_consume_local
    (str : native_String) (r q : SmtRegLan) :
    native_str_in_re str
        (native_re_concat (native_re_inter r native_re_all) q) =
      native_str_in_re str (native_re_concat r q) := by
  have hInterAllRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan (native_re_inter r native_re_all))
        (SmtValue.RegLan r) := by
    apply smt_value_rel_of_native_includes_local
    · intro xs hValid hMem
      rw [native_str_in_re_re_inter]
      simp [hMem, native_str_in_re_re_all xs hValid]
    · exact native_includes_inter_left r native_re_all
  have hConcatRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_re_concat (native_re_inter r native_re_all) q))
        (SmtValue.RegLan (native_re_concat r q)) :=
    smt_value_rel_re_concat_consume_local hInterAllRel
      (RuleProofs.smt_value_rel_refl (SmtValue.RegLan q))
  by_cases hValid : native_string_valid str = true
  · simpa only [native_str_in_re_eq_model] using
      smt_value_rel_reglan_valid_eq hConcatRel hValid
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem smt_value_rel_re_mult_consume_local
    {r r' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_mult r))
      (SmtValue.RegLan (native_re_mult r')) := by
  exact smt_value_rel_of_native_includes_local
    (native_includes_star_mono (native_includes_of_smt_value_rel hr))
    (native_includes_star_mono
      (native_includes_of_smt_value_rel
        (RuleProofs.smt_value_rel_symm _ _ hr)))

theorem smt_value_rel_re_union_consume_local
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_union r s))
      (SmtValue.RegLan (native_re_union r' s')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str _, ← native_str_in_re_eq_model str _]
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    native_str_in_re_eq_model, native_str_in_re_eq_model,
    smt_value_rel_reglan_valid_eq hr hValid,
    smt_value_rel_reglan_valid_eq hs hValid]
  rw [native_str_in_re_eq_model, native_str_in_re_eq_model]

theorem smt_value_rel_re_inter_consume_local
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_inter r s))
      (SmtValue.RegLan (native_re_inter r' s')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  rw [← native_str_in_re_eq_model str _, ← native_str_in_re_eq_model str _]
  rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
    native_str_in_re_eq_model, native_str_in_re_eq_model,
    smt_value_rel_reglan_valid_eq hr hValid,
    smt_value_rel_reglan_valid_eq hs hValid]
  rw [native_str_in_re_eq_model, native_str_in_re_eq_model]

theorem smt_value_rel_boolean_eq_consume_local
    {b c : native_Bool}
    (hRel :
      RuleProofs.smt_value_rel (SmtValue.Boolean b)
        (SmtValue.Boolean c)) :
    b = c := by
  cases b <;> cases c <;>
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq]
      at hRel ⊢

theorem smt_value_rel_boolean_of_eq_consume_local
    {b c : native_Bool}
    (h : b = c) :
    RuleProofs.smt_value_rel (SmtValue.Boolean b)
      (SmtValue.Boolean c) := by
  subst c
  exact RuleProofs.smt_value_rel_refl _

theorem smt_value_rel_str_to_re_of_seq_rel_consume_local
    {ss ss' : SmtSeq}
    (hRel : RuleProofs.smt_value_rel (SmtValue.Seq ss)
      (SmtValue.Seq ss')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_str_to_re (native_unpack_string ss)))
      (SmtValue.RegLan (native_str_to_re (native_unpack_string ss'))) := by
  have hSeq : RuleProofs.smt_seq_rel ss ss' := by
    simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using hRel
  have hEq : ss = ss' := (RuleProofs.smt_seq_rel_iff_eq ss ss').1 hSeq
  subst ss
  exact RuleProofs.smt_value_rel_refl _

theorem smt_value_rel_reglan_right_consume_local
    {v : SmtValue} {r : SmtRegLan}
    (hRel : RuleProofs.smt_value_rel v (SmtValue.RegLan r)) :
    ∃ r', v = SmtValue.RegLan r' ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan r') (SmtValue.RegLan r) := by
  cases v <;>
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq]
      at hRel
  case RegLan r' =>
    refine ⟨r', rfl, ?_⟩
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change SmtValue.Boolean (nativeReExtEqConsume r' r) =
      SmtValue.Boolean true
    simpa [nativeReExtEqConsume] using hRel

theorem reConcat_singleton_elim_eval_rel_consume_local
    (M : SmtModel) (c : Term) (rv : SmtRegLan)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) c =
        Term.Boolean true)
    (hEval : __smtx_model_eval M (__eo_to_smt c) = SmtValue.RegLan rv) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) c)) =
        SmtValue.RegLan outRv ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan rv) := by
  have hRel :=
    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_rel_eval M c
      hList (by
        exact ⟨rv, hEval⟩)
  rcases smt_value_rel_reglan_right_consume_local
      (by simpa [hEval] using hRel) with
    ⟨outRv, hOutEval, hOutRel⟩
  exact ⟨outRv, hOutEval, hOutRel⟩

theorem eval_str_to_re_reglan_consume_local
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) := by
  change __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtValue.RegLan (native_str_to_re (native_unpack_string ss))
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hEval,
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy]

theorem eval_re_concat_reglan_consume_local
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
      SmtValue.RegLan (native_re_concat ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_concat ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_concat, hAEval, hBEval]

theorem eval_re_union_reglan_consume_local
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
      SmtValue.RegLan (native_re_union ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_union ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_union, hAEval, hBEval]

theorem eval_re_inter_reglan_consume_local
    (M : SmtModel) (a b : Term) (ra rb : SmtRegLan)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
      SmtValue.RegLan (native_re_inter ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_inter ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_inter, hAEval, hBEval]

theorem eval_re_mult_reglan_consume_local
    (M : SmtModel) (body : Term) (rv : SmtRegLan)
    (hEval : __smtx_model_eval M (__eo_to_smt body) = SmtValue.RegLan rv) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) body)) =
      SmtValue.RegLan (native_re_mult rv) := by
  change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt body)) =
    SmtValue.RegLan (native_re_mult rv)
  simp [__smtx_model_eval, __smtx_model_eval_re_mult, hEval]

theorem smt_typeof_str_to_re_of_seq_consume_local
    (s : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt s) =
        SmtType.Seq SmtType.Char) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hTy, native_ite, native_Teq]

theorem str_to_re_arg_type_of_reglan_consume_local
    (s : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan at hTy
  exact seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
    (typeof_str_to_re_eq (__eo_to_smt s)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

theorem smt_typeof_re_concat_of_reglan_consume_local
    (a b : Term)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
      SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan
  rw [typeof_re_concat_eq]
  simp [hATy, hBTy, native_ite, native_Teq]

theorem smt_typeof_re_union_of_reglan_consume_local
    (a b : Term)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
      SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan
  rw [typeof_re_union_eq]
  simp [hATy, hBTy, native_ite, native_Teq]

theorem smt_typeof_re_inter_of_reglan_consume_local
    (a b : Term)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
      SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan
  rw [typeof_re_inter_eq]
  simp [hATy, hBTy, native_ite, native_Teq]

theorem smt_typeof_re_mult_of_reglan_consume_local
    (body : Term)
    (hTy : __smtx_typeof (__eo_to_smt body) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) body)) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt body)) =
    SmtType.RegLan
  rw [typeof_re_mult_eq]
  simp [hTy, native_ite, native_Teq]

theorem re_unflatten_str_finish_eval_rel_local
    (M : SmtModel) (hM : model_wf M)
    (acc unflatB : Term) (accSs : SmtSeq)
    (rb rb' : SmtRegLan)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc =
        Term.Boolean true)
    (hAccTy :
      __smtx_typeof (__eo_to_smt acc) =
        SmtType.Seq SmtType.Char)
    (hAccEval :
      __smtx_model_eval M (__eo_to_smt acc) =
        SmtValue.Seq accSs)
    (hUnflatBTy :
      __smtx_typeof (__eo_to_smt unflatB) = SmtType.RegLan)
    (hUnflatBEval :
      __smtx_model_eval M (__eo_to_smt unflatB) =
        SmtValue.RegLan rb')
    (hUnflatBRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rb')
        (SmtValue.RegLan rb))
    (hCollect : __str_collect acc ≠ Term.Stuck) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (__eo_list_singleton_elim
                    (Term.UOp UserOp.str_concat) (__str_collect acc))))
              unflatB)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (__eo_list_singleton_elim
                    (Term.UOp UserOp.str_concat) (__str_collect acc))))
              unflatB)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs)) rb)) := by
  let collectedString :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
      (__str_collect acc)
  let headRe := Term.Apply (Term.UOp UserOp.str_to_re) collectedString
  rcases str_collect_singleton_elim_eval_rel_local M hM acc accSs
      SmtType.Char hAccList hAccTy hAccEval hCollect with
    ⟨collectedSs, hCollectedEval, hCollectedRel⟩
  have hCollectedTy :
      __smtx_typeof (__eo_to_smt collectedString) =
        SmtType.Seq SmtType.Char := by
    simpa [collectedString] using
      str_collect_singleton_elim_type_local acc SmtType.Char hAccList
        hAccTy hCollect
  have hHeadEval :
      __smtx_model_eval M (__eo_to_smt headRe) =
        SmtValue.RegLan
          (native_str_to_re (native_unpack_string collectedSs)) := by
    simpa [headRe, collectedString] using
      eval_str_to_re_reglan_consume_local M collectedString collectedSs
        (by simpa [collectedString] using hCollectedEval) (by
          change __smtx_typeof_value (SmtValue.Seq collectedSs) =
            SmtType.Seq SmtType.Char
          rw [← hCollectedEval]
          simpa [hCollectedTy] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt collectedString) (by
                unfold term_has_non_none_type
                rw [hCollectedTy]
                simp))
  have hHeadTy :
      __smtx_typeof (__eo_to_smt headRe) = SmtType.RegLan := by
    simpa [headRe] using
      smt_typeof_str_to_re_of_seq_consume_local collectedString
        hCollectedTy
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat) headRe)
              unflatB)) =
        SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string collectedSs)) rb') :=
    eval_re_concat_reglan_consume_local M headRe unflatB
      (native_str_to_re (native_unpack_string collectedSs)) rb'
      hHeadEval hUnflatBEval
  have hFullTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat) headRe)
              unflatB)) =
        SmtType.RegLan :=
    smt_typeof_re_concat_of_reglan_consume_local headRe unflatB
      hHeadTy hUnflatBTy
  have hHeadRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string collectedSs)))
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string accSs))) :=
    smt_value_rel_str_to_re_of_seq_rel_consume_local hCollectedRel
  have hFullRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string collectedSs)) rb'))
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs)) rb)) :=
    smt_value_rel_re_concat_consume_local hHeadRel hUnflatBRel
  exact ⟨native_re_concat
      (native_str_to_re (native_unpack_string collectedSs)) rb',
    by simpa [headRe, collectedString] using hFullEval,
    by simpa [headRe, collectedString] using hFullTy,
    hFullRel⟩

theorem str_re_consume_side_smt_type
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    __smtx_typeof (__eo_to_smt side) = SmtType.Bool := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hRTy, _hEqBool⟩
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation strIn
      side (by simpa [strIn] using hEqTrans) with
    ⟨hSameTy, _hStrInNN⟩
  have hStrInTy :
      __smtx_typeof (__eo_to_smt strIn) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hSTy, hRTy, native_ite, native_Teq]
  rw [← hSameTy, hStrInTy]

theorem str_re_consume_eq_translation_of_types
    (s r side : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hSideTy : __smtx_typeof (__eo_to_smt side) = SmtType.Bool) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
        side) := by
  apply RuleProofs.eo_has_smt_translation_of_has_bool_type
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
      __smtx_typeof (__eo_to_smt side)
    rw [typeof_str_in_re_eq, hSideTy]
    simp [hSTy, hRTy, native_ite, native_Teq]
  · change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) ≠
      SmtType.None
    rw [typeof_str_in_re_eq]
    simp [hSTy, hRTy, native_ite, native_Teq]

theorem str_re_consume_side_eval_bool
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    ∃ b,
      __smtx_model_eval M (__eo_to_smt side) =
        SmtValue.Boolean b := by
  have hSideTy := str_re_consume_side_smt_type s r side hEqTrans
  have hSideEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt side)) =
        SmtType.Bool := by
    simpa [hSideTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt side) (by
        unfold term_has_non_none_type
        rw [hSideTy]
        simp)
  exact bool_value_canonical hSideEvalTy

theorem str_re_consume_model_rel_of_side_eq_str_in_re
    (M : SmtModel) (s r side : Term)
    (hSideEq :
      side =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  subst side
  exact RuleProofs.smt_value_rel_refl _

theorem str_re_consume_model_rel_of_consume_identity
    (M : SmtModel) (s r side : Term)
    (hSide : side = __str_re_consume s r)
    (hIdentity :
      __str_re_consume s r =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M s r side
  rw [hSide, hIdentity]

theorem str_re_consume_model_rel_of_side_false
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSideFalse : side = Term.Boolean false)
    (hInputFalse :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        native_str_in_re (native_unpack_string ss) rv = false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, rv, hSEval, hREval, hStrInEval⟩
  have hNativeFalse := hInputFalse ss rv hSEval hREval
  subst side
  rw [hStrInEval, hNativeFalse]
  change RuleProofs.smt_value_rel
    (SmtValue.Boolean false)
    (__smtx_model_eval M (SmtTerm.Boolean false))
  rw [__smtx_model_eval.eq_1]
  exact RuleProofs.smt_value_rel_refl _

theorem native_str_in_re_eq_of_seq_reglan_rel
    {ss ss' : SmtSeq} {rv rv' : SmtRegLan}
    (hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char)
    (hSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq ss') (SmtValue.Seq ss))
    (hRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rv') (SmtValue.RegLan rv)) :
    native_str_in_re (native_unpack_string ss') rv' =
      native_str_in_re (native_unpack_string ss) rv := by
  have hSeq : RuleProofs.smt_seq_rel ss' ss := by
    simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using hSeqRel
  have hSeqEq : ss' = ss :=
    (RuleProofs.smt_seq_rel_iff_eq ss' ss).1 hSeq
  subst ss'
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSeqTy
  simpa only [native_str_in_re_eq_model] using
    smt_value_rel_reglan_valid_eq hRegRel hValid

theorem native_str_in_re_eq_of_seq_reglan_rel_symm
    {ss ss' : SmtSeq} {rv rv' : SmtRegLan}
    (hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char)
    (hSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq ss') (SmtValue.Seq ss))
    (hRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rv') (SmtValue.RegLan rv)) :
    native_str_in_re (native_unpack_string ss) rv =
      native_str_in_re (native_unpack_string ss') rv' := by
  exact (native_str_in_re_eq_of_seq_reglan_rel hSeqTy hSeqRel
    hRegRel).symm

theorem native_str_in_re_eq_of_seq_reglan_rel_chain
    {ss midSs nextSs : SmtSeq}
    {rv midRv nextRv : SmtRegLan}
    (hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char)
    (hMidSeqTy :
      __smtx_typeof_value (SmtValue.Seq midSs) =
        SmtType.Seq SmtType.Char)
    (hMidSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq midSs) (SmtValue.Seq ss))
    (hMidRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan midRv) (SmtValue.RegLan rv))
    (hNextSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq nextSs)
        (SmtValue.Seq midSs))
    (hNextRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan nextRv)
        (SmtValue.RegLan midRv)) :
    native_str_in_re (native_unpack_string ss) rv =
      native_str_in_re (native_unpack_string nextSs) nextRv := by
  calc
    native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string midSs) midRv :=
      native_str_in_re_eq_of_seq_reglan_rel_symm hSeqTy hMidSeqRel
        hMidRegRel
    _ = native_str_in_re (native_unpack_string nextSs) nextRv :=
      native_str_in_re_eq_of_seq_reglan_rel_symm hMidSeqTy hNextSeqRel
        hNextRegRel

theorem str_re_consume_model_rel_of_side_str_in_re_rel
    (M : SmtModel) (hM : model_wf M)
    (s r side s' r' : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSideEq :
      side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r')
    (hSideRel :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∃ ss' rv',
            __smtx_model_eval M (__eo_to_smt s') = SmtValue.Seq ss' ∧
            __smtx_model_eval M (__eo_to_smt r') = SmtValue.RegLan rv' ∧
            RuleProofs.smt_value_rel (SmtValue.Seq ss') (SmtValue.Seq ss) ∧
            RuleProofs.smt_value_rel (SmtValue.RegLan rv')
              (SmtValue.RegLan rv)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, _hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, rv, hSEval, hREval, hStrInEval⟩
  rcases hSideRel ss rv hSEval hREval with
    ⟨ss', rv', hSEval', hREval', hSeqRel, hRegRel⟩
  have hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hNativeEq :
      native_str_in_re (native_unpack_string ss') rv' =
        native_str_in_re (native_unpack_string ss) rv :=
    native_str_in_re_eq_of_seq_reglan_rel hSeqTy hSeqRel hRegRel
  have hSeqEq : ss' = ss := by
    have hSeq : RuleProofs.smt_seq_rel ss' ss := by
      simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using hSeqRel
    exact (RuleProofs.smt_seq_rel_iff_eq ss' ss).1 hSeq
  subst ss'
  subst side
  rw [hStrInEval]
  change RuleProofs.smt_value_rel
    (SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv))
    (__smtx_model_eval M
      (SmtTerm.str_in_re (__eo_to_smt s') (__eo_to_smt r')))
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval', hREval',
    model_str_in_re_unpack_eq_string_of_value_type ss rv' hSeqTy]
  simpa [hNativeEq] using
    RuleProofs.smt_value_rel_refl
      (SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv))

theorem str_re_consume_model_rel_of_side_native_eval
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSideEval :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          __smtx_model_eval M (__eo_to_smt side) =
            SmtValue.Boolean
              (native_str_in_re (native_unpack_string ss) rv)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, rv, hSEval, hREval, hStrInEval⟩
  rw [hStrInEval, hSideEval ss rv hSEval hREval]
  exact RuleProofs.smt_value_rel_refl _

theorem str_re_consume_model_rel_of_re_none_result
    (M : SmtModel) (hM : model_wf M)
    (s side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.UOp UserOp.re_none)))
          side))
    (hSideFalse : side = Term.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.UOp UserOp.re_none))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_false M hM s
    (Term.UOp UserOp.re_none) side hEqTrans hSideFalse
  intro ss rv _hSEval hREval
  change __smtx_model_eval M SmtTerm.re_none = SmtValue.RegLan rv at hREval
  rw [__smtx_model_eval.eq_105] at hREval
  cases hREval
  exact native_str_in_re_re_none (native_unpack_string ss)

theorem str_re_consume_model_rel_of_re_all_result
    (M : SmtModel) (hM : model_wf M)
    (s side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.UOp UserOp.re_all)))
          side))
    (hSideEq :
      side =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String []))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.UOp UserOp.re_all))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_translation_facts s (Term.UOp UserOp.re_all) side
      hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, _hRTy, _hEqBool⟩
  apply str_re_consume_model_rel_of_side_native_eval M hM s
    (Term.UOp UserOp.re_all) side hEqTrans
  intro ss rv hSEval hREval
  have hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSeqTy
  change __smtx_model_eval M SmtTerm.re_all = SmtValue.RegLan rv at hREval
  rw [__smtx_model_eval.eq_106] at hREval
  cases hREval
  have hInputTrue :
      native_str_in_re (native_unpack_string ss) native_re_all = true :=
    native_str_in_re_re_all (native_unpack_string ss) hValid
  rw [hSideEq, hInputTrue]
  change __smtx_model_eval M
      (SmtTerm.str_in_re (SmtTerm.String [])
        (SmtTerm.str_to_re (SmtTerm.String []))) =
    SmtValue.Boolean true
  have hEmptyValid : native_string_valid ([] : native_String) = true := by
    rfl
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
    __smtx_model_eval_str_to_re,
    Smtm.native_str_in_re, native_re_str_valid, native_str_to_re, impl_native_re_of_list,
    native_re_nullable]

theorem str_re_consume_rec_re_none_eq
    (s fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s (Term.UOp UserOp.re_none) fuel =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (Term.UOp UserOp.re_none) := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec] at hS hFuel ⊢

theorem str_re_consume_rec_re_all_eq
    (s fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s (Term.UOp UserOp.re_all) fuel =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (Term.UOp UserOp.re_all) := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec] at hS hFuel ⊢

theorem str_re_consume_rec_re_none_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.UOp UserOp.re_none)))
          side))
    (hSide : side = __str_re_consume_rec s (Term.UOp UserOp.re_none) fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.UOp UserOp.re_none))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideEq :
      side =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
          (Term.UOp UserOp.re_none) := by
    rw [hSide, str_re_consume_rec_re_none_eq s fuel hS hFuel]
  exact str_re_consume_model_rel_of_side_eq_str_in_re M s
    (Term.UOp UserOp.re_none) side hSideEq

theorem str_re_consume_rec_re_all_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.UOp UserOp.re_all)))
          side))
    (hSide : side = __str_re_consume_rec s (Term.UOp UserOp.re_all) fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.UOp UserOp.re_all))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideEq :
      side =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
          (Term.UOp UserOp.re_all) := by
    rw [hSide, str_re_consume_rec_re_all_eq s fuel hS hFuel]
  exact str_re_consume_model_rel_of_side_eq_str_in_re M s
    (Term.UOp UserOp.re_all) side hSideEq

theorem native_re_concat_left_empty_local (r : SmtRegLan) :
    native_re_concat (native_str_to_re []) r = r := by
  cases r <;> simp [native_re_concat, native_str_to_re, impl_native_re_of_list,
   ]

theorem native_re_concat_right_empty_local (r : SmtRegLan) :
    native_re_concat r (native_str_to_re []) = r := by
  cases r <;> simp [native_re_concat, native_str_to_re, impl_native_re_of_list,
   ]

theorem nativeListInRe_char_self_local
    (c : native_Char) (hc : native_char_valid c = true) :
    nativeListInRe [c] (SmtRegLan.char c) = true := by
  simp [nativeListInRe, native_re_deriv, native_re_nullable]

theorem nativeListInRe_re_of_list_self_local :
    ∀ pat : native_String,
      native_string_valid pat = true ->
        nativeListInRe pat (impl_native_re_of_list pat) = true
  | [], _ => by
      simp [impl_native_re_of_list, nativeListInRe, native_re_nullable]
  | c :: cs, hValid => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hHead : nativeListInRe [c] (SmtRegLan.char c) = true :=
        nativeListInRe_char_self_local c hc
      have hTail : nativeListInRe cs (impl_native_re_of_list cs) = true :=
        nativeListInRe_re_of_list_self_local cs hcs
      have hConcat :
          nativeListInRe (c :: cs)
              (native_re_mk_concat (SmtRegLan.char c)
                (impl_native_re_of_list cs)) = true :=
        (nativeListInRe_mk_concat_true_iff_exists_append (c :: cs)
          (SmtRegLan.char c) (impl_native_re_of_list cs)).2
          ⟨[c], cs, rfl, hHead, hTail⟩
      simpa [impl_native_re_of_list] using hConcat

theorem native_str_in_re_str_to_re_self_local
    (pat : native_String)
    (hValid : native_string_valid pat = true) :
    native_str_in_re pat (native_str_to_re pat) = true := by
  simpa [native_str_in_re, hValid, native_str_to_re, nativeListInRe] using
    nativeListInRe_re_of_list_self_local pat hValid

theorem smt_value_rel_str_to_re_append_consume_local
    (xs ys : native_String) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_concat (native_str_to_re xs) (native_str_to_re ys)))
      (SmtValue.RegLan (native_str_to_re (xs ++ ys))) := by
  exact smt_value_rel_str_to_re_append xs ys

theorem native_str_in_re_str_to_re_concat_left_local
    (xs ys : native_String) (r : SmtRegLan)
    (hXsValid : native_string_valid xs = true) :
    native_str_in_re (xs ++ ys) (native_re_concat (native_str_to_re xs) r) =
      native_str_in_re ys r := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    by_cases hAppendValid : native_string_valid (xs ++ ys) = true
    · have hListMem :
          nativeListInRe (xs ++ ys)
              (native_re_mk_concat (native_str_to_re xs) r) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, hAppendValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append (xs ++ ys)
            (native_str_to_re xs) r).1 hListMem with
        ⟨left, right, hAppend, hLeft, hRight⟩
      have hLeftValid : native_string_valid left = true :=
        native_string_valid_append_left left right (by
          simpa [hAppend] using hAppendValid)
      have hLeftMem :
          native_str_in_re left (native_str_to_re xs) = true := by
        simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
      have hLeftEq : left = xs :=
        native_str_in_re_str_to_re_eq hLeftValid hLeftMem
      subst left
      have hRightEq : right = ys := by
        exact List.append_cancel_left hAppend
      subst right
      have hYsValid : native_string_valid ys = true :=
        native_string_valid_append_right xs ys hAppendValid
      simpa [native_str_in_re, hYsValid, nativeListInRe] using hRight
    · simp [native_str_in_re, hAppendValid] at hMem
  · intro hMem
    by_cases hYsValid : native_string_valid ys = true
    · have hAppendValid : native_string_valid (xs ++ ys) = true := by
        exact native_string_valid_append hXsValid hYsValid
      have hXsMem :
          native_str_in_re xs (native_str_to_re xs) = true :=
        native_str_in_re_str_to_re_self_local xs hXsValid
      exact native_str_in_re_re_concat_intro xs ys
        (native_str_to_re xs) r hXsMem hMem
    · simp [native_str_in_re, hYsValid] at hMem

theorem native_str_in_re_str_to_re_concat_prefix_false_of_tail_no_prefix_local
    (xs ys : native_String) (r : SmtRegLan)
    (hNoTail :
      ∀ pre suf : native_String,
        pre ++ suf = ys ->
          native_str_in_re pre r = false) :
    ∀ pre suf : native_String,
      pre ++ suf = xs ++ ys ->
        native_str_in_re pre
          (native_re_concat (native_str_to_re xs) r) = false := by
  intro pre suf hAppend
  by_cases hPreValid : native_string_valid pre = true
  · apply Bool.eq_false_iff.mpr
    intro hMem
    have hListMem :
        nativeListInRe pre
            (native_re_mk_concat (native_str_to_re xs) r) = true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hPreValid, native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append pre
          (native_str_to_re xs) r).1 hListMem with
      ⟨left, right, hSplit, hLeft, hRight⟩
    have hLeftValid : native_string_valid left = true :=
      native_string_valid_append_left left right (by
        simpa [hSplit] using hPreValid)
    have hLeftMem :
        native_str_in_re left (native_str_to_re xs) = true := by
      simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
    have hLeftEq : left = xs :=
      native_str_in_re_str_to_re_eq hLeftValid hLeftMem
    subst left
    have hRightAppend : right ++ suf = ys := by
      have hEq :
          xs ++ (right ++ suf) = xs ++ ys := by
        calc
        xs ++ (right ++ suf) = (xs ++ right) ++ suf := by
          simp [List.append_assoc]
        _ = pre ++ suf := by rw [hSplit]
        _ = xs ++ ys := hAppend
      exact List.append_cancel_left hEq
    have hRightValid : native_string_valid right = true :=
      native_string_valid_append_right xs right (by
        simpa [hSplit] using hPreValid)
    have hRightMem : native_str_in_re right r = true := by
      simpa [native_str_in_re, hRightValid, nativeListInRe] using hRight
    rw [hNoTail right suf hRightAppend] at hRightMem
    cases hRightMem
  · simp [native_str_in_re, hPreValid]

theorem native_str_in_re_re_concat_false_of_no_split_local
    (xs : native_String) (r1 r2 : SmtRegLan)
    (hNoSplit :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r1 = false) :
    native_str_in_re xs (native_re_concat r1 r2) = false := by
  by_cases hValid : native_string_valid xs = true
  · apply Bool.eq_false_iff.mpr
    intro hMem
    have hListMem :
        nativeListInRe xs (native_re_mk_concat r1 r2) = true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append xs r1 r2).1
          hListMem with
      ⟨pre, suf, hAppend, hPre, _hSuf⟩
    have hPreValid : native_string_valid pre = true :=
      native_string_valid_append_left pre suf (by
        simpa [hAppend] using hValid)
    have hPreMem : native_str_in_re pre r1 = true := by
      simpa [native_str_in_re, hPreValid, nativeListInRe] using hPre
    rw [hNoSplit pre suf hAppend] at hPreMem
    cases hPreMem
  · simp [native_str_in_re, hValid]

theorem native_str_in_re_re_concat_append_str_to_re_intro_local
    (pre suf : native_String) (r1 r2 : SmtRegLan)
    (hMem : native_str_in_re pre (native_re_concat r1 r2) = true)
    (hSufValid : native_string_valid suf = true) :
    native_str_in_re (pre ++ suf)
      (native_re_concat r1
        (native_re_concat r2 (native_str_to_re suf))) = true := by
  have hSufMem :
      native_str_in_re suf (native_str_to_re suf) = true :=
    native_str_in_re_str_to_re_self_local suf hSufValid
  have hAssocLeft :
      native_str_in_re (pre ++ suf)
        (native_re_concat (native_re_concat r1 r2)
          (native_str_to_re suf)) = true :=
    native_str_in_re_re_concat_intro pre suf
      (native_re_concat r1 r2) (native_str_to_re suf) hMem hSufMem
  by_cases hValid : native_string_valid (pre ++ suf) = true
  · have hListLeft :
        nativeListInRe (pre ++ suf)
          (native_re_mk_concat (native_re_mk_concat r1 r2)
            (native_str_to_re suf)) = true := by
      have hsimpa := hAssocLeft
      try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
      exact hsimpa
    have hListRight :
        nativeListInRe (pre ++ suf)
          (native_re_mk_concat r1
            (native_re_mk_concat r2 (native_str_to_re suf))) = true := by
      simpa [nativeListInRe_mk_concat_assoc (pre ++ suf) r1 r2
        (native_str_to_re suf)] using hListLeft
    have hsimpa := hListRight
    try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
    exact hsimpa
  · simp [native_str_in_re, hValid] at hAssocLeft

theorem native_str_in_re_re_concat_union_eq_or_local
    (xs : native_String) (r1 r2 q : SmtRegLan) :
    native_str_in_re xs (native_re_concat (native_re_union r1 r2) q) =
      (native_str_in_re xs (native_re_concat r1 q) ||
        native_str_in_re xs (native_re_concat r2 q)) := by
  by_cases hValid : native_string_valid xs = true
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hMem
      have hListMem :
          nativeListInRe xs
              (native_re_mk_concat (native_re_union r1 r2) q) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (native_re_union r1 r2) q).1 hListMem with
        ⟨pre, suf, hAppend, hPreUnion, hSuf⟩
      have hPreValid : native_string_valid pre = true :=
        native_string_valid_append_left pre suf (by
          simpa [hAppend] using hValid)
      have hSufValid : native_string_valid suf = true :=
        native_string_valid_append_right pre suf (by
          simpa [hAppend] using hValid)
      have hPreUnionNative :
          native_str_in_re pre (native_re_union r1 r2) = true := by
        simpa [native_str_in_re, hPreValid, nativeListInRe] using hPreUnion
      rw [native_str_in_re_re_union] at hPreUnionNative
      rw [Bool.or_eq_true] at hPreUnionNative
      rcases hPreUnionNative with hPreLeft | hPreRight
      · have hSufNative : native_str_in_re suf q = true := by
          simpa [native_str_in_re, hSufValid, nativeListInRe] using hSuf
        have hLeft :
            native_str_in_re xs (native_re_concat r1 q) = true := by
          have hIntro :=
            native_str_in_re_re_concat_intro pre suf r1 q hPreLeft
              hSufNative
          simpa [hAppend] using hIntro
        simp [hLeft]
      · have hSufNative : native_str_in_re suf q = true := by
          simpa [native_str_in_re, hSufValid, nativeListInRe] using hSuf
        have hRight :
            native_str_in_re xs (native_re_concat r2 q) = true := by
          have hIntro :=
            native_str_in_re_re_concat_intro pre suf r2 q hPreRight
              hSufNative
          simpa [hAppend] using hIntro
        simp [hRight]
    · intro hMem
      rw [Bool.or_eq_true] at hMem
      rcases hMem with hLeft | hRight
      · have hListLeft :
            nativeListInRe xs (native_re_mk_concat r1 q) = true := by
          have hsimpa := hLeft
          try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append xs r1 q).1
            hListLeft with
          ⟨pre, suf, hAppend, hPre, hSuf⟩
        have hPreValid : native_string_valid pre = true :=
          native_string_valid_append_left pre suf (by
            simpa [hAppend] using hValid)
        have hPreUnion :
            nativeListInRe pre (native_re_union r1 r2) = true := by
          have hPreNative : native_str_in_re pre r1 = true := by
            simpa [native_str_in_re, hPreValid, nativeListInRe] using hPre
          have hUnionNative :
              native_str_in_re pre (native_re_union r1 r2) = true := by
            rw [native_str_in_re_re_union, hPreNative]
            rfl
          simpa [native_str_in_re, hPreValid, nativeListInRe] using
            hUnionNative
        have hListUnion :
            nativeListInRe xs
                (native_re_mk_concat (native_re_union r1 r2) q) = true :=
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (native_re_union r1 r2) q).2
            ⟨pre, suf, hAppend, hPreUnion, hSuf⟩
        have hsimpa := hListUnion
        try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
      · have hListRight :
            nativeListInRe xs (native_re_mk_concat r2 q) = true := by
          have hsimpa := hRight
          try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append xs r2 q).1
            hListRight with
          ⟨pre, suf, hAppend, hPre, hSuf⟩
        have hPreValid : native_string_valid pre = true :=
          native_string_valid_append_left pre suf (by
            simpa [hAppend] using hValid)
        have hPreUnion :
            nativeListInRe pre (native_re_union r1 r2) = true := by
          have hPreNative : native_str_in_re pre r2 = true := by
            simpa [native_str_in_re, hPreValid, nativeListInRe] using hPre
          have hUnionNative :
              native_str_in_re pre (native_re_union r1 r2) = true := by
            rw [native_str_in_re_re_union, hPreNative]
            cases native_str_in_re pre r1 <;> rfl
          simpa [native_str_in_re, hPreValid, nativeListInRe] using
            hUnionNative
        have hListUnion :
            nativeListInRe xs
                (native_re_mk_concat (native_re_union r1 r2) q) = true :=
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (native_re_union r1 r2) q).2
            ⟨pre, suf, hAppend, hPreUnion, hSuf⟩
        have hsimpa := hListUnion
        try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
  · have hInvalid : native_string_valid xs = false := by
      cases h : native_string_valid xs <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_concat_union_left_no_prefix_local
    (xs : native_String) (r1 r2 q : SmtRegLan)
    (hNoLeft :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r1 = false) :
    native_str_in_re xs (native_re_concat (native_re_union r1 r2) q) =
      native_str_in_re xs (native_re_concat r2 q) := by
  rw [native_str_in_re_re_concat_union_eq_or_local]
  have hLeftFalse :
      native_str_in_re xs (native_re_concat r1 q) = false :=
    native_str_in_re_re_concat_false_of_no_split_local xs r1 q hNoLeft
  rw [hLeftFalse]
  rfl

theorem native_str_in_re_re_concat_union_right_no_prefix_local
    (xs : native_String) (r1 r2 q : SmtRegLan)
    (hNoRight :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r2 = false) :
    native_str_in_re xs (native_re_concat (native_re_union r1 r2) q) =
      native_str_in_re xs (native_re_concat r1 q) := by
  rw [native_str_in_re_re_concat_union_eq_or_local]
  have hRightFalse :
      native_str_in_re xs (native_re_concat r2 q) = false :=
    native_str_in_re_re_concat_false_of_no_split_local xs r2 q hNoRight
  rw [hRightFalse]
  cases native_str_in_re xs (native_re_concat r1 q) <;> rfl

theorem native_str_in_re_re_concat_union_same_residual_local
    (xs tail : native_String) (r1 r2 q : SmtRegLan)
    (hLeft :
      native_str_in_re xs (native_re_concat r1 q) =
        native_str_in_re tail q)
    (hRight :
      native_str_in_re xs (native_re_concat r2 q) =
        native_str_in_re tail q) :
    native_str_in_re xs (native_re_concat (native_re_union r1 r2) q) =
      native_str_in_re tail q := by
  rw [native_str_in_re_re_concat_union_eq_or_local, hLeft, hRight]
  cases native_str_in_re tail q <;> rfl

theorem native_str_in_re_re_concat_inter_false_of_left_no_split_local
    (xs : native_String) (r1 r2 q : SmtRegLan)
    (hNoLeft :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r1 = false) :
    native_str_in_re xs (native_re_concat (native_re_inter r1 r2) q) =
      false := by
  exact native_str_in_re_re_concat_false_of_no_split_local xs
    (native_re_inter r1 r2) q
    (fun pre suf hAppend => by
      rw [native_str_in_re_re_inter, hNoLeft pre suf hAppend]
      rfl)

theorem native_str_in_re_re_concat_inter_false_of_right_no_split_local
    (xs : native_String) (r1 r2 q : SmtRegLan)
    (hNoRight :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r2 = false) :
    native_str_in_re xs (native_re_concat (native_re_inter r1 r2) q) =
      false := by
  exact native_str_in_re_re_concat_false_of_no_split_local xs
    (native_re_inter r1 r2) q
    (fun pre suf hAppend => by
      rw [native_str_in_re_re_inter, hNoRight pre suf hAppend]
      cases native_str_in_re pre r1 <;> rfl)

theorem native_str_in_re_re_concat_inter_same_residual_local
    (xs tail : native_String) (r1 r2 q : SmtRegLan)
    (hTailValid : native_string_valid tail = true)
    (hLeft :
      native_str_in_re xs (native_re_concat r1 q) =
        native_str_in_re tail q)
    (hRight :
      native_str_in_re xs (native_re_concat r2 q) =
        native_str_in_re tail q)
    (hLeftTail :
      native_str_in_re xs
        (native_re_concat r1 (native_str_to_re tail)) = true)
    (hRightTail :
      native_str_in_re xs
        (native_re_concat r2 (native_str_to_re tail)) = true) :
    native_str_in_re xs (native_re_concat (native_re_inter r1 r2) q) =
      native_str_in_re tail q := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    by_cases hXsValid : native_string_valid xs = true
    · have hListMem :
          nativeListInRe xs
              (native_re_mk_concat (native_re_inter r1 r2) q) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, hXsValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (native_re_inter r1 r2) q).1 hListMem with
        ⟨pre, suf, hAppend, hPreInter, hSuf⟩
      have hPreValid : native_string_valid pre = true :=
        native_string_valid_append_left pre suf (by
          simpa [hAppend] using hXsValid)
      have hSufValid : native_string_valid suf = true :=
        native_string_valid_append_right pre suf (by
          simpa [hAppend] using hXsValid)
      have hPreInterNative :
          native_str_in_re pre (native_re_inter r1 r2) = true := by
        simpa [native_str_in_re, hPreValid, nativeListInRe] using
          hPreInter
      rw [native_str_in_re_re_inter] at hPreInterNative
      rw [Bool.and_eq_true] at hPreInterNative
      have hSufNative : native_str_in_re suf q = true := by
        simpa [native_str_in_re, hSufValid, nativeListInRe] using hSuf
      have hLeftConcat :
          native_str_in_re xs (native_re_concat r1 q) = true := by
        have hIntro :=
          native_str_in_re_re_concat_intro pre suf r1 q
            hPreInterNative.1 hSufNative
        simpa [hAppend] using hIntro
      rw [hLeft] at hLeftConcat
      exact hLeftConcat
    · simp [native_str_in_re, hXsValid] at hMem
  · intro hTailMem
    by_cases hXsValid : native_string_valid xs = true
    · have hLeftList :
          nativeListInRe xs
              (native_re_mk_concat r1 (native_str_to_re tail)) = true := by
        have hsimpa := hLeftTail
        try simp [native_str_in_re, hXsValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
      have hRightList :
          nativeListInRe xs
              (native_re_mk_concat r2 (native_str_to_re tail)) = true := by
        have hsimpa := hRightTail
        try simp [native_str_in_re, hXsValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append xs r1
            (native_str_to_re tail)).1 hLeftList with
        ⟨preL, sufL, hAppendL, hPreL, hSufL⟩
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append xs r2
            (native_str_to_re tail)).1 hRightList with
        ⟨preR, sufR, hAppendR, hPreR, hSufR⟩
      have hPreLValid : native_string_valid preL = true :=
        native_string_valid_append_left preL sufL (by
          simpa [hAppendL] using hXsValid)
      have hPreRValid : native_string_valid preR = true :=
        native_string_valid_append_left preR sufR (by
          simpa [hAppendR] using hXsValid)
      have hSufLValid : native_string_valid sufL = true :=
        native_string_valid_append_right preL sufL (by
          simpa [hAppendL] using hXsValid)
      have hSufRValid : native_string_valid sufR = true :=
        native_string_valid_append_right preR sufR (by
          simpa [hAppendR] using hXsValid)
      have hSufLMem :
          native_str_in_re sufL (native_str_to_re tail) = true := by
        simpa [native_str_in_re, hSufLValid, nativeListInRe] using hSufL
      have hSufRMem :
          native_str_in_re sufR (native_str_to_re tail) = true := by
        simpa [native_str_in_re, hSufRValid, nativeListInRe] using hSufR
      have hSufLEq : sufL = tail :=
        native_str_in_re_str_to_re_eq hSufLValid hSufLMem
      have hSufREq : sufR = tail :=
        native_str_in_re_str_to_re_eq hSufRValid hSufRMem
      subst sufL
      subst sufR
      have hPreEq : preL = preR := by
        apply List.append_cancel_right
        rw [hAppendL, hAppendR]
      subst preR
      have hPreLNative : native_str_in_re preL r1 = true := by
        simpa [native_str_in_re, hPreLValid, nativeListInRe] using hPreL
      have hPreRNative : native_str_in_re preL r2 = true := by
        simpa [native_str_in_re, hPreLValid, nativeListInRe] using hPreR
      have hPreInter :
          native_str_in_re preL (native_re_inter r1 r2) = true := by
        rw [native_str_in_re_re_inter, hPreLNative, hPreRNative]
        rfl
      have hIntro :=
        native_str_in_re_re_concat_intro preL tail (native_re_inter r1 r2) q
          hPreInter hTailMem
      simpa [hAppendL] using hIntro
    · simp [native_str_in_re, hXsValid] at hLeftTail

theorem nativeListInRe_raw_star_cons_decomp_local
    {c : native_Char} {cs : List native_Char} {r : SmtRegLan} :
    nativeListInRe (c :: cs) (SmtRegLan.star r) = true ->
      ∃ xs1 xs2,
        xs1 ++ xs2 = cs ∧
        nativeListInRe (c :: xs1) r = true ∧
        nativeListInRe xs2 (SmtRegLan.star r) = true := by
  intro h
  have hConcat :
      nativeListInRe cs
          (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
        true := by
    simpa [nativeListInRe, native_re_deriv] using h
  rcases
      (nativeListInRe_mk_concat_true_iff_exists_append cs
        (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
    ⟨xs1, xs2, hAppend, hHead, hTail⟩
  exact ⟨xs1, xs2, hAppend, by simpa [nativeListInRe] using hHead,
    hTail⟩

theorem native_str_in_re_re_mult_empty_local (r : SmtRegLan) :
    native_str_in_re [] (native_re_mult r) = true := by
  cases r <;> simp [native_str_in_re, native_string_valid, nativeListInRe,
    native_re_mult, native_re_nullable]

theorem nativeListInRe_re_mult_nonempty_prefix_decomp_local
    (xs : native_String) (r : SmtRegLan)
    (hStar : nativeListInRe xs (native_re_mult r) = true)
    (hNe : xs ≠ []) :
    ∃ pre suf : native_String,
      pre ++ suf = xs ∧
      pre ≠ [] ∧
      nativeListInRe pre r = true ∧
      nativeListInRe suf (native_re_mult r) = true := by
  cases xs with
  | nil =>
      exact False.elim (hNe rfl)
  | cons c cs =>
      cases r with
      | empty =>
          have hNil : c :: cs = [] :=
            (nativeListInRe_epsilon_iff (c :: cs)).1 (by
              simpa [native_re_mult, native_re_mk_star] using hStar)
          cases hNil
      | epsilon =>
          have hNil : c :: cs = [] :=
            (nativeListInRe_epsilon_iff (c :: cs)).1 (by
              simpa [native_re_mult, native_re_mk_star] using hStar)
          cases hNil
      | star body =>
          refine ⟨c :: cs, [], by simp, by simp, ?_, ?_⟩
          · simpa [native_re_mult, native_re_mk_star] using hStar
          · simp [nativeListInRe, native_re_mult,
              native_re_nullable]
      | char d =>
          rcases nativeListInRe_raw_star_cons_decomp_local
              (r := SmtRegLan.char d)
              (by simpa [native_re_mult, native_re_mk_star] using hStar)
            with ⟨preTail, suf, hAppend, hHead, hSuf⟩
          exact ⟨c :: preTail, suf, by simp [hAppend], by simp,
            by simpa using hHead,
            by simpa [native_re_mult, native_re_mk_star] using hSuf⟩
      | range lo hi =>
          rcases nativeListInRe_raw_star_cons_decomp_local
              (r := SmtRegLan.range lo hi)
              (by simpa [native_re_mult, native_re_mk_star] using hStar)
            with ⟨preTail, suf, hAppend, hHead, hSuf⟩
          exact ⟨c :: preTail, suf, by simp [hAppend], by simp,
            by simpa using hHead,
            by simpa [native_re_mult, native_re_mk_star] using hSuf⟩
      | allchar =>
          rcases nativeListInRe_raw_star_cons_decomp_local
              (r := SmtRegLan.allchar)
              (by simpa [native_re_mult, native_re_mk_star] using hStar)
            with ⟨preTail, suf, hAppend, hHead, hSuf⟩
          exact ⟨c :: preTail, suf, by simp [hAppend], by simp,
            by simpa using hHead,
            by simpa [native_re_mult, native_re_mk_star] using hSuf⟩
      | concat r1 r2 =>
          rcases nativeListInRe_raw_star_cons_decomp_local
              (r := SmtRegLan.concat r1 r2)
              (by simpa [native_re_mult, native_re_mk_star] using hStar)
            with ⟨preTail, suf, hAppend, hHead, hSuf⟩
          exact ⟨c :: preTail, suf, by simp [hAppend], by simp,
            by simpa using hHead,
            by simpa [native_re_mult, native_re_mk_star] using hSuf⟩
      | union r1 r2 =>
          rcases nativeListInRe_raw_star_cons_decomp_local
              (r := SmtRegLan.union r1 r2)
              (by simpa [native_re_mult, native_re_mk_star] using hStar)
            with ⟨preTail, suf, hAppend, hHead, hSuf⟩
          exact ⟨c :: preTail, suf, by simp [hAppend], by simp,
            by simpa using hHead,
            by simpa [native_re_mult, native_re_mk_star] using hSuf⟩
      | inter r1 r2 =>
          rcases nativeListInRe_raw_star_cons_decomp_local
              (r := SmtRegLan.inter r1 r2)
              (by simpa [native_re_mult, native_re_mk_star] using hStar)
            with ⟨preTail, suf, hAppend, hHead, hSuf⟩
          exact ⟨c :: preTail, suf, by simp [hAppend], by simp,
            by simpa using hHead,
            by simpa [native_re_mult, native_re_mk_star] using hSuf⟩
      | comp body =>
          rcases nativeListInRe_raw_star_cons_decomp_local
              (r := SmtRegLan.comp body)
              (by simpa [native_re_mult, native_re_mk_star] using hStar)
            with ⟨preTail, suf, hAppend, hHead, hSuf⟩
          exact ⟨c :: preTail, suf, by simp [hAppend], by simp,
            by simpa using hHead,
            by simpa [native_re_mult, native_re_mk_star] using hSuf⟩

theorem nativeListInRe_re_mult_nonempty_prefix_local
    (xs : native_String) (r : SmtRegLan)
    (hStar : nativeListInRe xs (native_re_mult r) = true)
    (hNe : xs ≠ []) :
    ∃ pre suf : native_String,
      pre ++ suf = xs ∧ pre ≠ [] ∧ nativeListInRe pre r = true := by
  rcases nativeListInRe_re_mult_nonempty_prefix_decomp_local xs r hStar
      hNe with
    ⟨pre, suf, hAppend, hPreNe, hPreMem, _hSufMem⟩
  exact ⟨pre, suf, hAppend, hPreNe, hPreMem⟩

theorem StrInReConsumeInternal.list_all_reverse_eq_consume_local {α : Type}
    (p : α -> Bool) :
    ∀ xs : List α, xs.reverse.all p = xs.all p
  | [] => by simp
  | x :: xs => by
      rw [List.reverse_cons, List.all_append]
      rw [StrInReConsumeInternal.list_all_reverse_eq_consume_local p xs]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      exact Bool.and_comm (xs.all p) (p x)

theorem StrInReConsumeInternal.native_string_valid_reverse_consume_local
    (str : native_String) :
    native_string_valid str.reverse = native_string_valid str := by
  simpa [native_string_valid] using
    StrInReConsumeInternal.list_all_reverse_eq_consume_local native_char_valid str

def StrInReConsumeInternal.native_re_reverse_raw_consume_local :
    SmtRegLan -> SmtRegLan
  | SmtRegLan.empty => SmtRegLan.empty
  | SmtRegLan.epsilon => SmtRegLan.epsilon
  | SmtRegLan.char c => SmtRegLan.char c
  | SmtRegLan.range lo hi => SmtRegLan.range lo hi
  | SmtRegLan.allchar => SmtRegLan.allchar
  | SmtRegLan.concat r s =>
      SmtRegLan.concat (StrInReConsumeInternal.native_re_reverse_raw_consume_local s)
        (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)
  | SmtRegLan.union r s =>
      SmtRegLan.union (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)
        (StrInReConsumeInternal.native_re_reverse_raw_consume_local s)
  | SmtRegLan.inter r s =>
      SmtRegLan.inter (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)
        (StrInReConsumeInternal.native_re_reverse_raw_consume_local s)
  | SmtRegLan.star r =>
      SmtRegLan.star (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)
  | SmtRegLan.comp r =>
      SmtRegLan.comp (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)

theorem StrInReConsumeInternal.native_str_in_re_reverse_str_to_re_consume_local
    (xs pat : native_String) :
    native_str_in_re xs.reverse (native_str_to_re pat.reverse) =
      native_str_in_re xs (native_str_to_re pat) := by
  by_cases hValid : native_string_valid xs = true
  · have hRevValid : native_string_valid xs.reverse = true := by
      simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local xs] using hValid
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hMem
      have hEqRev :
          xs.reverse = pat.reverse :=
        native_str_in_re_str_to_re_eq hRevValid hMem
      have hEq : xs = pat := by
        have h := congrArg List.reverse hEqRev
        simpa using h
      subst xs
      exact native_str_in_re_str_to_re_self_local pat hValid
    · intro hMem
      have hEq : xs = pat :=
        native_str_in_re_str_to_re_eq hValid hMem
      subst xs
      exact native_str_in_re_str_to_re_self_local pat.reverse hRevValid
  · have hRevInvalid : native_string_valid xs.reverse = false := by
      cases h : native_string_valid xs <;> simp [h] at hValid
      simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local xs, h]
    have hInvalid : native_string_valid xs = false := by
      cases h : native_string_valid xs <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid, hRevInvalid]

theorem StrInReConsumeInternal.nativeListInRe_raw_star_once_consume_local :
    (xs : List native_Char) -> (r : SmtRegLan) ->
      nativeListInRe xs r = true ->
        nativeListInRe xs (SmtRegLan.star r) = true
  | [], r, _hMem => by
      simp [nativeListInRe, native_re_nullable]
  | c :: cs, r, hMem => by
      have hDer : nativeListInRe cs (native_re_deriv c r) = true := by
        simpa [nativeListInRe] using hMem
      have hNil : nativeListInRe [] (SmtRegLan.star r) = true := by
        simp [nativeListInRe, native_re_nullable]
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) =
            true :=
        (nativeListInRe_mk_concat_true_iff_exists_append cs
          (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨cs, [], by simp, hDer, hNil⟩
      simpa [nativeListInRe, native_re_deriv] using hConcat

theorem StrInReConsumeInternal.nativeListInRe_char_length_one_consume_local
    (xs : native_String) (c : SmtValue)
    (hMem : nativeListInRe xs (SmtRegLan.char c) = true) :
    xs.length = 1 := by
  exact nativeListInRe_char_true_length xs c hMem

theorem StrInReConsumeInternal.nativeListInRe_range_length_one_consume_local
    (xs : native_String) (lo hi : SmtValue)
    (hMem : nativeListInRe xs (SmtRegLan.range lo hi) = true) :
    xs.length = 1 := by
  exact nativeListInRe_range_true_length xs lo hi hMem

theorem StrInReConsumeInternal.nativeListInRe_reverse_char_consume_local
    (xs : native_String) (c : SmtValue) :
    nativeListInRe xs.reverse (SmtRegLan.char c) =
      nativeListInRe xs (SmtRegLan.char c) := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_nullable]
  | cons x xs =>
      cases xs with
      | nil =>
          simp [nativeListInRe, native_re_deriv]
      | cons y ys =>
          have hLeft :
              nativeListInRe (x :: y :: ys).reverse (SmtRegLan.char c) =
                false := by
            apply Bool.eq_false_iff.mpr
            intro hMem
            have hLen :=
              StrInReConsumeInternal.nativeListInRe_char_length_one_consume_local
                (x :: y :: ys).reverse c hMem
            simp at hLen
          have hRight :
              nativeListInRe (x :: y :: ys) (SmtRegLan.char c) =
                false := by
            apply Bool.eq_false_iff.mpr
            intro hMem
            have hLen :=
              StrInReConsumeInternal.nativeListInRe_char_length_one_consume_local
                (x :: y :: ys) c hMem
            simp at hLen
          rw [hLeft, hRight]

theorem StrInReConsumeInternal.nativeListInRe_reverse_range_consume_local
    (xs : native_String) (lo hi : SmtValue) :
    nativeListInRe xs.reverse (SmtRegLan.range lo hi) =
      nativeListInRe xs (SmtRegLan.range lo hi) := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_nullable]
  | cons x xs =>
      cases xs with
      | nil =>
          simp [nativeListInRe, native_re_deriv, Bool.and_assoc]
      | cons y ys =>
          have hLeft :
              nativeListInRe (x :: y :: ys).reverse
                  (SmtRegLan.range lo hi) =
                false := by
            apply Bool.eq_false_iff.mpr
            intro hMem
            have hLen :=
              StrInReConsumeInternal.nativeListInRe_range_length_one_consume_local
                (x :: y :: ys).reverse lo hi hMem
            simp at hLen
          have hRight :
              nativeListInRe (x :: y :: ys) (SmtRegLan.range lo hi) =
                false := by
            apply Bool.eq_false_iff.mpr
            intro hMem
            have hLen :=
              StrInReConsumeInternal.nativeListInRe_range_length_one_consume_local
                (x :: y :: ys) lo hi hMem
            simp at hLen
          rw [hLeft, hRight]

theorem StrInReConsumeInternal.nativeListInRe_reverse_allchar_consume_local
    (xs : native_String) :
    nativeListInRe xs.reverse native_re_allchar =
      nativeListInRe xs native_re_allchar := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    have hFacts := (nativeListInRe_allchar_true_iff xs.reverse).1 hMem
    apply (nativeListInRe_allchar_true_iff xs).2
    constructor
    · simpa using hFacts.1
    · simpa [StrInReConsumeInternal.list_all_reverse_eq_consume_local native_char_valid xs] using
        hFacts.2
  · intro hMem
    have hFacts := (nativeListInRe_allchar_true_iff xs).1 hMem
    apply (nativeListInRe_allchar_true_iff xs.reverse).2
    constructor
    · simpa using hFacts.1
    · simpa [StrInReConsumeInternal.list_all_reverse_eq_consume_local native_char_valid xs] using
        hFacts.2

theorem StrInReConsumeInternal.nativeListInRe_reverse_epsilon_consume_local
    (xs : native_String) :
    nativeListInRe xs.reverse SmtRegLan.epsilon =
      nativeListInRe xs SmtRegLan.epsilon := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    have hRevNil : xs.reverse = [] :=
      (nativeListInRe_epsilon_iff xs.reverse).1 hMem
    have hNil : xs = [] := by
      have h := congrArg List.reverse hRevNil
      simpa using h
    exact (nativeListInRe_epsilon_iff xs).2 hNil
  · intro hMem
    have hNil : xs = [] := (nativeListInRe_epsilon_iff xs).1 hMem
    subst xs
    simp [nativeListInRe, native_re_nullable]

theorem StrInReConsumeInternal.nativeListInRe_raw_union_consume_local :
    ∀ (xs : native_String) (r s : SmtRegLan),
      nativeListInRe xs (SmtRegLan.union r s) =
        (nativeListInRe xs r || nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable]
  | c :: cs, r, s => by
      change
        nativeListInRe cs
            (native_re_mk_union (native_re_deriv c r)
              (native_re_deriv c s)) =
          (nativeListInRe cs (native_re_deriv c r) ||
            nativeListInRe cs (native_re_deriv c s))
      rw [nativeListInRe_mk_union]

theorem StrInReConsumeInternal.nativeListInRe_raw_inter_consume_local :
    ∀ (xs : native_String) (r s : SmtRegLan),
      nativeListInRe xs (SmtRegLan.inter r s) =
        (nativeListInRe xs r && nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable]
  | c :: cs, r, s => by
      change
        nativeListInRe cs
            (native_re_mk_inter (native_re_deriv c r)
              (native_re_deriv c s)) =
          (nativeListInRe cs (native_re_deriv c r) &&
            nativeListInRe cs (native_re_deriv c s))
      rw [nativeListInRe_mk_inter]

theorem StrInReConsumeInternal.nativeListInRe_raw_comp_consume_local :
    ∀ (xs : native_String) (r : SmtRegLan),
      nativeListInRe xs (SmtRegLan.comp r) =
        Bool.not (nativeListInRe xs r)
  | [], r => by
      cases r <;> simp [nativeListInRe, native_re_nullable]
  | c :: cs, r => by
      have hComp := nativeListInRe_mk_comp cs (native_re_deriv c r)
      simpa [nativeListInRe, native_re_deriv,
        StrInReConsumeInternal.nativeListInRe_raw_comp_consume_local cs] using hComp

theorem StrInReConsumeInternal.nativeListInRe_raw_concat_true_iff_exists_append_consume_local :
    ∀ (xs : native_String) (r s : SmtRegLan),
      nativeListInRe xs (SmtRegLan.concat r s) = true ↔
        ∃ xs₁ xs₂ : native_String,
          xs₁ ++ xs₂ = xs ∧
            nativeListInRe xs₁ r = true ∧
            nativeListInRe xs₂ s = true
  | [], r, s => by
      constructor
      · intro h
        have hParts :
            native_re_nullable r = true ∧ native_re_nullable s = true := by
          simpa [nativeListInRe, native_re_nullable, Bool.and_eq_true]
            using h
        exact ⟨[], [], by rfl, by simpa [nativeListInRe] using hParts.1,
          by simpa [nativeListInRe] using hParts.2⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp [nativeListInRe, native_re_nullable] at hLeft hRight ⊢
                simp [hLeft, hRight]
            | cons _ _ =>
                simp at hAppend
        | cons _ _ =>
            simp at hAppend
  | c :: cs, r, s => by
      constructor
      · intro h
        have hDer :
            nativeListInRe cs
                (native_re_mk_union
                  (native_re_mk_concat (native_re_deriv c r) s)
                  (if native_re_nullable r then native_re_deriv c s
                    else SmtRegLan.empty)) =
              true := by
          simpa [nativeListInRe, native_re_deriv] using h
        rw [nativeListInRe_mk_union] at hDer
        have hDerCases :
            nativeListInRe cs
                  (native_re_mk_concat (native_re_deriv c r) s) =
                true ∨
              nativeListInRe cs
                  (if native_re_nullable r then native_re_deriv c s
                    else SmtRegLan.empty) =
                true := by
          cases hA :
              nativeListInRe cs
                (native_re_mk_concat (native_re_deriv c r) s) <;>
            cases hB :
              nativeListInRe cs
                (if native_re_nullable r then native_re_deriv c s
                  else SmtRegLan.empty) <;>
            simp [hA, hB] at hDer ⊢
        rcases hDerCases with hLeft | hRight
        · rcases
            (nativeListInRe_mk_concat_true_iff_exists_append cs
              (native_re_deriv c r) s).1 hLeft with
            ⟨xs₁, xs₂, hAppend, hHead, hTail⟩
          exact ⟨c :: xs₁, xs₂, by simp [hAppend],
            by simpa [nativeListInRe] using hHead, hTail⟩
        · cases hNull : native_re_nullable r
          · simp [hNull, nativeListInRe_empty] at hRight
          · have hR : nativeListInRe [] r = true := by
              simpa [nativeListInRe] using hNull
            have hS : nativeListInRe (c :: cs) s = true := by
              simpa [hNull, nativeListInRe] using hRight
            exact ⟨[], c :: cs, by rfl, hR, hS⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases hAppend
            have hNull : native_re_nullable r = true := by
              simpa [nativeListInRe] using hLeft
            have hS : nativeListInRe cs (native_re_deriv c s) = true := by
              simpa [nativeListInRe] using hRight
            have hUnion :
                nativeListInRe cs
                    (native_re_mk_union
                      (native_re_mk_concat (native_re_deriv c r) s)
                      (if native_re_nullable r then native_re_deriv c s
                        else SmtRegLan.empty)) =
                  true := by
              rw [nativeListInRe_mk_union]
              simp [hNull, hS]
            simpa [nativeListInRe, native_re_deriv] using hUnion
        | cons x xs₁ =>
            cases hAppend
            have hHead : nativeListInRe xs₁ (native_re_deriv c r) = true := by
              simpa [nativeListInRe] using hLeft
            have hConcat :
                nativeListInRe (xs₁ ++ xs₂)
                    (native_re_mk_concat (native_re_deriv c r) s) =
                  true :=
              (nativeListInRe_mk_concat_true_iff_exists_append
                (xs₁ ++ xs₂) (native_re_deriv c r) s).2
                ⟨xs₁, xs₂, by rfl, hHead, hRight⟩
            have hUnion :
                nativeListInRe (xs₁ ++ xs₂)
                    (native_re_mk_union
                      (native_re_mk_concat (native_re_deriv c r) s)
                      (if native_re_nullable r then native_re_deriv c s
                        else SmtRegLan.empty)) =
                  true := by
              rw [nativeListInRe_mk_union]
              simp [hConcat]
            simpa [nativeListInRe, native_re_deriv] using hUnion

theorem StrInReConsumeInternal.nativeListInRe_reverse_raw_concat_consume_local
    (xs : native_String) (r1 r2 rr1 rr2 : SmtRegLan)
    (h1 : ∀ ys,
      nativeListInRe ys.reverse rr1 = nativeListInRe ys r1)
    (h2 : ∀ ys,
      nativeListInRe ys.reverse rr2 = nativeListInRe ys r2) :
    nativeListInRe xs.reverse (SmtRegLan.concat rr2 rr1) =
      nativeListInRe xs (SmtRegLan.concat r1 r2) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    rcases
        (StrInReConsumeInternal.nativeListInRe_raw_concat_true_iff_exists_append_consume_local
          xs.reverse rr2 rr1).1 hMem with
      ⟨ys2, ys1, hAppend, hYs2, hYs1⟩
    have hRevAppend :
        ys1.reverse ++ ys2.reverse = xs := by
      have h := congrArg List.reverse hAppend
      simpa [List.reverse_append] using h
    have hLeft : nativeListInRe ys1.reverse r1 = true := by
      have h' :
          nativeListInRe ys1 rr1 = nativeListInRe ys1.reverse r1 := by
        simpa using h1 ys1.reverse
      rw [← h']
      exact hYs1
    have hRight : nativeListInRe ys2.reverse r2 = true := by
      have h' :
          nativeListInRe ys2 rr2 = nativeListInRe ys2.reverse r2 := by
        simpa using h2 ys2.reverse
      rw [← h']
      exact hYs2
    exact
      (StrInReConsumeInternal.nativeListInRe_raw_concat_true_iff_exists_append_consume_local
        xs r1 r2).2
        ⟨ys1.reverse, ys2.reverse, hRevAppend, hLeft, hRight⟩
  · intro hMem
    rcases
        (StrInReConsumeInternal.nativeListInRe_raw_concat_true_iff_exists_append_consume_local
          xs r1 r2).1 hMem with
      ⟨ys1, ys2, hAppend, hYs1, hYs2⟩
    have hRevAppend :
        ys2.reverse ++ ys1.reverse = xs.reverse := by
      rw [← hAppend, List.reverse_append]
    have hLeft : nativeListInRe ys2.reverse rr2 = true := by
      rw [h2 ys2]
      exact hYs2
    have hRight : nativeListInRe ys1.reverse rr1 = true := by
      rw [h1 ys1]
      exact hYs1
    exact
      (StrInReConsumeInternal.nativeListInRe_raw_concat_true_iff_exists_append_consume_local
        xs.reverse rr2 rr1).2
        ⟨ys2.reverse, ys1.reverse, hRevAppend, hLeft, hRight⟩

theorem StrInReConsumeInternal.nativeListInRe_raw_star_nonempty_prefix_decomp_consume_local
    (xs : native_String) (r : SmtRegLan)
    (hStar : nativeListInRe xs (SmtRegLan.star r) = true)
    (hNe : xs ≠ []) :
    ∃ pre suf : native_String,
      pre ++ suf = xs ∧
      pre ≠ [] ∧
      nativeListInRe pre r = true ∧
      nativeListInRe suf (SmtRegLan.star r) = true := by
  cases xs with
  | nil => exact False.elim (hNe rfl)
  | cons c cs =>
      rcases nativeListInRe_raw_star_cons_decomp_local (r := r) hStar with
        ⟨preTail, suf, hAppend, hHead, hSuf⟩
      exact ⟨c :: preTail, suf, by simp [hAppend], by simp, hHead,
        hSuf⟩

theorem StrInReConsumeInternal.nativeListInRe_reverse_raw_star_consume_local
    (r rr : SmtRegLan)
    (h : ∀ ys,
      nativeListInRe ys.reverse rr = nativeListInRe ys r) :
    ∀ xs : native_String,
      nativeListInRe xs.reverse (SmtRegLan.star rr) =
        nativeListInRe xs (SmtRegLan.star r)
  | [] => by
      simp [nativeListInRe, native_re_nullable]
  | c :: cs => by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hRevNe : (c :: cs).reverse ≠ [] := by simp
        rcases
            StrInReConsumeInternal.nativeListInRe_raw_star_nonempty_prefix_decomp_consume_local
              (c :: cs).reverse rr hMem hRevNe with
          ⟨pre, suf, hAppend, hPreNe, hPreMem, hSufMem⟩
        have hOrigAppend : suf.reverse ++ pre.reverse = c :: cs := by
          have hRev := congrArg List.reverse hAppend
          simpa [List.reverse_append] using hRev
        have hPreR : nativeListInRe pre.reverse r = true := by
          have hEq :
              nativeListInRe pre rr =
                nativeListInRe pre.reverse r := by
            simpa using h pre.reverse
          rw [← hEq]
          exact hPreMem
        have hSufR :
            nativeListInRe suf.reverse (SmtRegLan.star r) = true := by
          have hRec :=
            StrInReConsumeInternal.nativeListInRe_reverse_raw_star_consume_local r rr h suf.reverse
          have hLeft :
              nativeListInRe (suf.reverse).reverse (SmtRegLan.star rr) =
                true := by
            simpa using hSufMem
          rw [← hRec]
          exact hLeft
        have hPreStar :
            nativeListInRe pre.reverse (SmtRegLan.star r) = true :=
          StrInReConsumeInternal.nativeListInRe_raw_star_once_consume_local pre.reverse r hPreR
        have hJoin :
            nativeListInRe (suf.reverse ++ pre.reverse)
                (SmtRegLan.star r) = true :=
          nativeListInRe_raw_star_append suf.reverse pre.reverse r
            hSufR hPreStar
        simpa [hOrigAppend] using hJoin
      · intro hMem
        have hNe : c :: cs ≠ [] := by simp
        rcases
            StrInReConsumeInternal.nativeListInRe_raw_star_nonempty_prefix_decomp_consume_local
              (c :: cs) r hMem hNe with
          ⟨pre, suf, hAppend, hPreNe, hPreMem, hSufMem⟩
        have hRevAppend : suf.reverse ++ pre.reverse = (c :: cs).reverse := by
          rw [← hAppend, List.reverse_append]
        have hPreRR : nativeListInRe pre.reverse rr = true := by
          rw [h pre]
          exact hPreMem
        have hSufRR :
            nativeListInRe suf.reverse (SmtRegLan.star rr) = true := by
          have hRec := StrInReConsumeInternal.nativeListInRe_reverse_raw_star_consume_local r rr h suf
          rw [hRec]
          exact hSufMem
        have hPreStar :
            nativeListInRe pre.reverse (SmtRegLan.star rr) = true :=
          StrInReConsumeInternal.nativeListInRe_raw_star_once_consume_local pre.reverse rr hPreRR
        have hJoin :
            nativeListInRe (suf.reverse ++ pre.reverse)
                (SmtRegLan.star rr) = true :=
          nativeListInRe_raw_star_append suf.reverse pre.reverse rr
            hSufRR hPreStar
        simpa [hRevAppend] using hJoin
termination_by xs => xs.length
decreasing_by
  all_goals
    have hLenEq := congrArg List.length hAppend
    simp only [List.length_append, List.length_reverse, List.length_cons]
      at hLenEq ⊢
    have hPreLen : 0 < pre.length := by
      cases pre with
      | nil => exact False.elim (hPreNe rfl)
      | cons _ _ => simp
    omega

theorem StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local :
    ∀ (r : SmtRegLan) (xs : native_String),
      nativeListInRe xs.reverse (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) =
        nativeListInRe xs r
  | SmtRegLan.empty, xs => by
      simp [StrInReConsumeInternal.native_re_reverse_raw_consume_local, nativeListInRe_empty]
  | SmtRegLan.epsilon, xs => by
      simpa [StrInReConsumeInternal.native_re_reverse_raw_consume_local] using
        StrInReConsumeInternal.nativeListInRe_reverse_epsilon_consume_local xs
  | SmtRegLan.char c, xs => by
      simpa [StrInReConsumeInternal.native_re_reverse_raw_consume_local] using
        StrInReConsumeInternal.nativeListInRe_reverse_char_consume_local xs c
  | SmtRegLan.range lo hi, xs => by
      simpa [StrInReConsumeInternal.native_re_reverse_raw_consume_local] using
        StrInReConsumeInternal.nativeListInRe_reverse_range_consume_local xs lo hi
  | SmtRegLan.allchar, xs => by
      have hsimpa :=
        StrInReConsumeInternal.nativeListInRe_reverse_allchar_consume_local xs
      try simp [StrInReConsumeInternal.native_re_reverse_raw_consume_local] at hsimpa ⊢
      exact hsimpa
  | SmtRegLan.concat r s, xs => by
      simpa [StrInReConsumeInternal.native_re_reverse_raw_consume_local] using
        StrInReConsumeInternal.nativeListInRe_reverse_raw_concat_consume_local xs r s
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local s)
          (StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local r)
          (StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local s)
  | SmtRegLan.union r s, xs => by
      simp [StrInReConsumeInternal.native_re_reverse_raw_consume_local,
        StrInReConsumeInternal.nativeListInRe_raw_union_consume_local,
        StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local r xs,
        StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local s xs]
  | SmtRegLan.inter r s, xs => by
      simp [StrInReConsumeInternal.native_re_reverse_raw_consume_local,
        StrInReConsumeInternal.nativeListInRe_raw_inter_consume_local,
        StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local r xs,
        StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local s xs]
  | SmtRegLan.star r, xs => by
      simpa [StrInReConsumeInternal.native_re_reverse_raw_consume_local] using
        StrInReConsumeInternal.nativeListInRe_reverse_raw_star_consume_local r
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)
          (StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local r) xs
  | SmtRegLan.comp r, xs => by
      rw [StrInReConsumeInternal.native_re_reverse_raw_consume_local]
      rw [StrInReConsumeInternal.nativeListInRe_raw_comp_consume_local]
      rw [StrInReConsumeInternal.nativeListInRe_raw_comp_consume_local]
      rw [StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local r xs]

theorem StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local
    (xs : native_String) (r : SmtRegLan) :
    native_str_in_re xs.reverse (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) =
      native_str_in_re xs r := by
  by_cases hValid : native_string_valid xs = true
  · have hRevValid : native_string_valid xs.reverse = true := by
      simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local xs] using hValid
    simpa [native_str_in_re, hValid, hRevValid] using
      StrInReConsumeInternal.nativeListInRe_reverse_re_consume_local r xs
  · have hInvalid : native_string_valid xs = false := by
      cases h : native_string_valid xs <;> simp [h] at hValid ⊢
    have hRevInvalid : native_string_valid xs.reverse = false := by
      simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local xs] using hInvalid
    simp [native_str_in_re, hRevInvalid, hInvalid]

theorem StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local
    (xs : native_String) (r : SmtRegLan) :
    native_str_in_re xs r =
      native_str_in_re xs.reverse (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) := by
  exact (StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local xs r).symm

theorem StrInReConsumeInternal.smt_value_rel_native_re_reverse_raw_consume_local
    {r s : SmtRegLan}
    (hRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s)) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (StrInReConsumeInternal.native_re_reverse_raw_consume_local r))
      (SmtValue.RegLan (StrInReConsumeInternal.native_re_reverse_raw_consume_local s)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hRevValid : native_string_valid str.reverse = true := by
    simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local str] using hValid
  have hR :
      native_str_in_re str (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) =
        native_str_in_re str.reverse r := by
    have h := StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local str.reverse r
    simpa using h
  have hS :
      native_str_in_re str (StrInReConsumeInternal.native_re_reverse_raw_consume_local s) =
        native_str_in_re str.reverse s := by
    have h := StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local str.reverse s
    simpa using h
  rw [← native_str_in_re_eq_model str _, ← native_str_in_re_eq_model str _]
  rw [hR, hS]
  simpa only [native_str_in_re_eq_model] using
    smt_value_rel_reglan_valid_eq hRel hRevValid

theorem StrInReConsumeInternal.smt_value_rel_native_re_reverse_raw_str_to_re_consume_local
    (xs : native_String) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (StrInReConsumeInternal.native_re_reverse_raw_consume_local (native_str_to_re xs)))
      (SmtValue.RegLan (native_str_to_re xs.reverse)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hRevValid : native_string_valid str.reverse = true := by
    simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local str] using hValid
  have hRaw :
      native_str_in_re str
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local (native_str_to_re xs)) =
        native_str_in_re str.reverse (native_str_to_re xs) := by
    have h := StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local str.reverse
      (native_str_to_re xs)
    simpa using h
  have hStrToRe :
      native_str_in_re str (native_str_to_re xs.reverse) =
        native_str_in_re str.reverse (native_str_to_re xs) := by
    have h := StrInReConsumeInternal.native_str_in_re_reverse_str_to_re_consume_local
      str.reverse xs
    simpa using h
  rw [← native_str_in_re_eq_model str _, ← native_str_in_re_eq_model str _]
  rw [hRaw, hStrToRe]

theorem StrInReConsumeInternal.smt_value_rel_native_re_reverse_raw_reverse_raw_consume_local
    (r : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (StrInReConsumeInternal.native_re_reverse_raw_consume_local
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)))
      (SmtValue.RegLan r) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq]
  intro str hValid
  have hRevValid : native_string_valid str.reverse = true := by
    simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local str] using hValid
  have hFirst :
      native_str_in_re str
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local
            (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)) =
        native_str_in_re str.reverse
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) := by
    have h := StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local str.reverse
      (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)
    simpa using h
  have hSecond :
      native_str_in_re str.reverse
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) =
        native_str_in_re str r := by
    have h := StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local str r
    simpa using h
  rw [← native_str_in_re_eq_model str _, ← native_str_in_re_eq_model str _]
  rw [hFirst, hSecond]

theorem StrInReConsumeInternal.native_str_in_re_false_of_reverse_re_false_consume_local
    (xs : native_String) (r : SmtRegLan)
    (hFalse :
      native_str_in_re xs.reverse (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) =
        false) :
    native_str_in_re xs r = false := by
  rw [StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local xs r]
  exact hFalse

theorem StrInReConsumeInternal.native_str_in_re_reverse_re_false_of_false_consume_local
    (xs : native_String) (r : SmtRegLan)
    (hFalse : native_str_in_re xs r = false) :
    native_str_in_re xs.reverse (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) =
      false := by
  rw [StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local xs r]
  exact hFalse

theorem StrInReConsumeInternal.native_str_in_re_eq_of_unpack_reverse_reglan_rel_consume_local
    {ss revSs : SmtSeq} {rv revRv : SmtRegLan}
    (hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char)
    (hRevUnpack :
      native_unpack_string revSs = (native_unpack_string ss).reverse)
    (hRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan revRv)
        (SmtValue.RegLan (StrInReConsumeInternal.native_re_reverse_raw_consume_local rv))) :
    native_str_in_re (native_unpack_string ss) rv =
      native_str_in_re (native_unpack_string revSs) revRv := by
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSeqTy
  have hRevValid :
      native_string_valid (native_unpack_string revSs) = true := by
    rw [hRevUnpack]
    simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local
      (native_unpack_string ss)] using hValid
  calc
    native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string ss).reverse
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local rv) :=
      StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local
        (native_unpack_string ss) rv
    _ = native_str_in_re (native_unpack_string revSs)
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local rv) := by
      rw [hRevUnpack]
    _ = native_str_in_re (native_unpack_string revSs) revRv :=
      (by
        simpa only [native_str_in_re_eq_model] using
          (smt_value_rel_reglan_valid_eq hRegRel hRevValid).symm)

def StrInReConsumeInternal.consume_atom_chain_term (atoms : List Term) (e : Term) :
    Term :=
  atoms.foldr
    (fun a acc => Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) acc)
    e

theorem StrInReConsumeInternal.consume_atom_chain_cons (a : Term) (xs : List Term)
    (e : Term) :
    StrInReConsumeInternal.consume_atom_chain_term (a :: xs) e =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a)
        (StrInReConsumeInternal.consume_atom_chain_term xs e) := rfl

theorem StrInReConsumeInternal.consume_atom_chain_append (xs ys : List Term) (e : Term) :
    StrInReConsumeInternal.consume_atom_chain_term (xs ++ ys) e =
      StrInReConsumeInternal.consume_atom_chain_term xs (StrInReConsumeInternal.consume_atom_chain_term ys e) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.cons_append, StrInReConsumeInternal.consume_atom_chain_cons, ih,
        StrInReConsumeInternal.consume_atom_chain_cons]

theorem StrInReConsumeInternal.consume_str_is_empty_ne_stuck {e : Term}
    (he : __str_is_empty e = Term.Boolean true) : e ≠ Term.Stuck := by
  intro h
  subst e
  simp [__str_is_empty] at he

theorem StrInReConsumeInternal.consume_str_is_empty_cases (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    (∃ U,
        e = Term.UOp1 UserOp1.seq_empty
          (Term.Apply (Term.UOp UserOp.Seq) U)) ∨
      e = Term.String [] := by
  unfold __str_is_empty at he
  split at he
  · cases he
  · next U => exact Or.inl ⟨U, rfl⟩
  · exact Or.inr rfl
  · cases he

theorem StrInReConsumeInternal.consume_eo_is_list_nil_str_concat_of_str_is_empty
    (e : Term) (he : __str_is_empty e = Term.Boolean true) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat) e =
      Term.Boolean true := by
  rcases StrInReConsumeInternal.consume_str_is_empty_cases e he with ⟨U, rfl⟩ | rfl
  · simp [__eo_is_list_nil, __eo_is_list_nil_str_concat]
  · simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
      native_teq]

theorem StrInReConsumeInternal.consume_eo_get_nil_rec_atom_chain (xs : List Term)
    (e : Term) (he : __str_is_empty e = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.str_concat)
        (StrInReConsumeInternal.consume_atom_chain_term xs e) =
      e := by
  induction xs with
  | nil =>
      exact eo_get_nil_rec_str_concat_eq_of_nil_true e
        (StrInReConsumeInternal.consume_eo_is_list_nil_str_concat_of_str_is_empty e he)
  | cons a xs ih =>
      rw [StrInReConsumeInternal.consume_atom_chain_cons]
      change __eo_requires (Term.UOp UserOp.str_concat)
          (Term.UOp UserOp.str_concat)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
            (StrInReConsumeInternal.consume_atom_chain_term xs e)) = e
      rw [ih]
      exact eo_requires_self_eq_of_ne_stuck (Term.UOp UserOp.str_concat)
        e (by simp)

theorem StrInReConsumeInternal.consume_eo_is_list_atom_chain (xs : List Term) (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (StrInReConsumeInternal.consume_atom_chain_term xs e) =
      Term.Boolean true := by
  exact eo_is_list_true_of_get_nil_rec_ne_stuck
    (Term.UOp UserOp.str_concat) (StrInReConsumeInternal.consume_atom_chain_term xs e) (by
      rw [StrInReConsumeInternal.consume_eo_get_nil_rec_atom_chain xs e he]
      exact StrInReConsumeInternal.consume_str_is_empty_ne_stuck he)

theorem StrInReConsumeInternal.consume_eo_list_rev_rec_atom_chain (xs : List Term)
    (e acc : Term) (he : __str_is_empty e = Term.Boolean true)
    (hacc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (StrInReConsumeInternal.consume_atom_chain_term xs e) acc =
      StrInReConsumeInternal.consume_atom_chain_term xs.reverse acc := by
  induction xs generalizing acc with
  | nil =>
      rcases StrInReConsumeInternal.consume_str_is_empty_cases e he with ⟨U, rfl⟩ | rfl
      · simp [StrInReConsumeInternal.consume_atom_chain_term, __eo_list_rev_rec]
      · simp [StrInReConsumeInternal.consume_atom_chain_term, __eo_list_rev_rec]
  | cons a xs ih =>
      rw [StrInReConsumeInternal.consume_atom_chain_cons]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) a
        (StrInReConsumeInternal.consume_atom_chain_term xs e) acc hacc]
      rw [ih (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) acc)
        (by simp)]
      rw [List.reverse_cons, StrInReConsumeInternal.consume_atom_chain_append]
      rfl

theorem StrInReConsumeInternal.consume_eo_list_rev_atom_chain (xs : List Term) (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (StrInReConsumeInternal.consume_atom_chain_term xs e) =
      StrInReConsumeInternal.consume_atom_chain_term xs.reverse e := by
  have hList := StrInReConsumeInternal.consume_eo_is_list_atom_chain xs e he
  have hGet := StrInReConsumeInternal.consume_eo_get_nil_rec_atom_chain xs e he
  rw [__eo_list_rev, hList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_list_rev_rec (StrInReConsumeInternal.consume_atom_chain_term xs e)
      (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
        (StrInReConsumeInternal.consume_atom_chain_term xs e))) (by decide)]
  rw [hGet]
  exact StrInReConsumeInternal.consume_eo_list_rev_rec_atom_chain xs e e he
    (StrInReConsumeInternal.consume_str_is_empty_ne_stuck he)

theorem StrInReConsumeInternal.consume_concat_unpack (M : SmtModel) (x y : Term)
    (sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    ∃ sxy,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
        SmtValue.Seq sxy ∧
      native_unpack_seq sxy =
        native_unpack_seq sx ++ native_unpack_seq sy := by
  rw [smtx_model_eval_str_concat_term_eq, hx, hy]
  simp only [__smtx_model_eval_str_concat]
  exact ⟨_, rfl, by rw [Smtm.native_unpack_pack_seq]; rfl⟩

private noncomputable def consume_seq_elem_val (M : SmtModel)
    (a : Term) : SmtValue :=
  match a with
  | Term.Apply (Term.UOp UserOp.seq_unit) e =>
      __smtx_model_eval M (__eo_to_smt e)
  | Term.String [ch] => SmtValue.Char ch
  | _ => SmtValue.NotValue

theorem StrInReConsumeInternal.consume_eval_seq_unit_atom (M : SmtModel) (e : Term) :
    ∃ sa,
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        SmtValue.Seq sa ∧
      native_unpack_seq sa =
        [consume_seq_elem_val M (Term.Apply (Term.UOp UserOp.seq_unit) e)] := by
  rw [show
    __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e) =
      SmtTerm.seq_unit (__eo_to_smt e) from rfl]
  rw [show
    __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M (__eo_to_smt e))
          (SmtSeq.empty
            (__smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt e))))) from by
        simp only [__smtx_model_eval]]
  exact ⟨_, rfl, by simp [native_unpack_seq, consume_seq_elem_val]⟩

theorem StrInReConsumeInternal.consume_eval_char_atom (M : SmtModel)
    (ch : native_Char) :
    ∃ sa,
      __smtx_model_eval M (__eo_to_smt (Term.String [ch])) =
        SmtValue.Seq sa ∧
      native_unpack_seq sa =
        [consume_seq_elem_val M (Term.String [ch])] := by
  rw [show __eo_to_smt (Term.String [ch]) = SmtTerm.String [ch] from rfl]
  simp only [__smtx_model_eval]
  exact ⟨native_pack_string [ch], rfl, by
    simp [consume_seq_elem_val, native_pack_string, native_pack_seq,
      native_unpack_seq]⟩

theorem StrInReConsumeInternal.consume_str_is_empty_eval_unpack_nil (M : SmtModel)
    (e : Term) (s : SmtSeq)
    (hemp : __str_is_empty e = Term.Boolean true)
    (hev : __smtx_model_eval M (__eo_to_smt e) = SmtValue.Seq s) :
    native_unpack_seq s = [] := by
  unfold __str_is_empty at hemp
  split at hemp
  · exact Term.noConfusion hemp
  · rename_i U
    rw [show
      __eo_to_smt
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) U)) =
        __eo_to_smt_seq_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U)) from rfl]
      at hev
    simp only [__eo_to_smt_type, __smtx_typeof_guard, native_ite] at hev
    split at hev
    · simp only [__eo_to_smt_seq_empty, __smtx_model_eval] at hev
      exact SmtValue.noConfusion hev
    · rw [show
        __eo_to_smt_seq_empty (SmtType.Seq (__eo_to_smt_type U)) =
          SmtTerm.seq_empty (__eo_to_smt_type U) from rfl,
        show
          __smtx_model_eval M (SmtTerm.seq_empty (__eo_to_smt_type U)) =
            SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U)) from by
              simp only [__smtx_model_eval]] at hev
      injection hev with hev
      rw [← hev]
      rfl
  · rw [show __eo_to_smt (Term.String []) = SmtTerm.String [] from rfl,
      show
        __smtx_model_eval M (SmtTerm.String []) =
          SmtValue.Seq (native_pack_string []) from by
            simp only [__smtx_model_eval]] at hev
    injection hev with hev
    rw [← hev]
    simp [native_pack_string, native_pack_seq, native_unpack_seq]
  · simp at hemp

theorem StrInReConsumeInternal.consume_atom_eval_unpack (M : SmtModel) (a : Term)
    (hShape :
      (∃ ch, a = Term.String [ch]) ∨
        (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)) :
    ∀ sa,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa ->
      native_unpack_seq sa = [consume_seq_elem_val M a] := by
  intro sa hEval
  rcases hShape with ⟨ch, rfl⟩ | ⟨e, rfl⟩
  · rcases StrInReConsumeInternal.consume_eval_char_atom M ch with ⟨sa0, hEval0, hUnp⟩
    rw [hEval] at hEval0
    cases hEval0
    exact hUnp
  · rcases StrInReConsumeInternal.consume_eval_seq_unit_atom M e with ⟨sa0, hEval0, hUnp⟩
    rw [hEval] at hEval0
    cases hEval0
    exact hUnp

theorem StrInReConsumeInternal.consume_chain_unpack_td (M : SmtModel) (ex : Term)
    (htermempty : __str_is_empty ex = Term.Boolean true) :
    ∀ (xs : List Term) (sc : SmtSeq),
      __smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_atom_chain_term xs ex)) =
        SmtValue.Seq sc ->
      (∀ a ∈ xs,
        ∀ sa,
          __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa ->
          native_unpack_seq sa = [consume_seq_elem_val M a]) ->
      native_unpack_seq sc = xs.map (consume_seq_elem_val M) := by
  intro xs
  induction xs with
  | nil =>
      intro sc hc _
      rw [show StrInReConsumeInternal.consume_atom_chain_term [] ex = ex from rfl] at hc
      simpa using StrInReConsumeInternal.consume_str_is_empty_eval_unpack_nil M ex sc htermempty hc
  | cons a xs ih =>
      intro sc hc hatoms
      rw [StrInReConsumeInternal.consume_atom_chain_cons] at hc
      obtain ⟨⟨sa, hsa⟩, ⟨sc', hsc'⟩⟩ :=
        strConcat_args_eval_seq_of_concat_eval_seq M a
          (StrInReConsumeInternal.consume_atom_chain_term xs ex) ⟨sc, hc⟩
      obtain ⟨sxy, hsxy, hsxynil⟩ :=
        StrInReConsumeInternal.consume_concat_unpack M a (StrInReConsumeInternal.consume_atom_chain_term xs ex) sa sc'
          hsa hsc'
      have heq : sc = sxy := by
        rw [hc] at hsxy
        injection hsxy
      rw [heq, hsxynil, hatoms a (by simp) sa hsa,
        ih sc' hsc' (fun a' h' => hatoms a' (by simp [h']))]
      simp

structure StrInReConsumeInternal.ConsumeIntroWordView (M : SmtModel) (t : Term)
    (S : SmtSeq) (T : SmtType) where
  atoms : List Term
  ex : Term
  hflat :
    __str_flatten (__str_nary_intro t) =
      StrInReConsumeInternal.consume_atom_chain_term atoms ex
  hlen : __str_value_len t = Term.Numeral (Int.ofNat atoms.length)
  hunp : native_unpack_seq S = atoms.map (consume_seq_elem_val M)
  hexEmpty : __str_is_empty ex = Term.Boolean true
  hAtomTy :
    ∀ a ∈ atoms, __smtx_typeof (__eo_to_smt a) = SmtType.Seq T
  hAtomShape :
    ∀ a ∈ atoms,
      (∃ ch, a = Term.String [ch]) ∨
        (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)

theorem StrInReConsumeInternal.consume_atom_chain_string_atoms_eq_substrWord :
    ∀ w : native_String,
      StrInReConsumeInternal.consume_atom_chain_term (w.map (fun ch => Term.String [ch]))
          (Term.String []) =
        substrWord w 0 w.length
  | [] => by
      rfl
  | c :: cs => by
      rw [show (c :: cs).length = cs.length + 1 from rfl,
        List.map_cons, StrInReConsumeInternal.consume_atom_chain_cons, substrWord,
        extractString_zero_cons,
        show (0 : native_Int) + 1 = 1 by simp, substrWord_cons_tail,
        StrInReConsumeInternal.consume_atom_chain_string_atoms_eq_substrWord cs]

theorem StrInReConsumeInternal.consume_char_atoms_unpack (M : SmtModel)
    (w : native_String) :
    w.map SmtValue.Char =
      (w.map (fun ch => Term.String [ch])).map
        (consume_seq_elem_val M) := by
  induction w with
  | nil => rfl
  | cons ch rest ih =>
      simp [consume_seq_elem_val, ih]

theorem StrInReConsumeInternal.consume_unpack_pack_string_map (w : native_String) :
    native_unpack_seq (native_pack_string w) =
      w.map SmtValue.Char := by
  simp [native_pack_string, Smtm.native_unpack_pack_seq]

theorem StrInReConsumeInternal.consume_char_atoms_type (w : native_String)
    (T : SmtType)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.String w)) = SmtType.Seq T) :
    ∀ a ∈ w.map (fun ch => Term.String [ch]),
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
  have hT : T = SmtType.Char := string_seq_type_char_local w T hTy
  intro a ha
  rcases List.mem_map.1 ha with ⟨ch, hMem, rfl⟩
  rw [hT]
  have hValid : native_string_valid w = true :=
    native_string_valid_of_smtx_typeof_eo_string w (by
      simpa [hT] using hTy)
  have hCharValid : native_char_valid ch = true := by
    unfold native_string_valid at hValid
    exact List.all_eq_true.1 hValid ch hMem
  change __smtx_typeof (SmtTerm.String [ch]) =
    SmtType.Seq SmtType.Char
  rw [__smtx_typeof.eq_4]
  simp [native_string_valid, hCharValid, native_ite]

theorem StrInReConsumeInternal.consume_char_atoms_shape (w : native_String) :
    ∀ a ∈ w.map (fun ch => Term.String [ch]),
      (∃ ch, a = Term.String [ch]) ∨
        (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e) := by
  intro a ha
  rcases List.mem_map.1 ha with ⟨ch, _hMem, rfl⟩
  exact Or.inl ⟨ch, rfl⟩

theorem StrInReConsumeInternal.consume_str_value_len_string (w : native_String) :
    __str_value_len (Term.String w) =
      Term.Numeral (Int.ofNat w.length) := by
  simp [__str_value_len, __eo_requires, __eo_is_str,
    __eo_is_str_internal, __eo_len, native_str_len, native_teq,
    SmtEval.native_ite, SmtEval.native_and, SmtEval.native_not]

def StrInReConsumeInternal.consume_intro_word_view_string
    (M : SmtModel) (w : native_String) (S : SmtSeq) (T : SmtType)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.String w)) = SmtType.Seq T)
    (hEval :
      __smtx_model_eval M (__eo_to_smt (Term.String w)) =
        SmtValue.Seq S) :
    StrInReConsumeInternal.ConsumeIntroWordView M (Term.String w) S T := by
  refine {
    atoms := w.map (fun ch => Term.String [ch]),
    ex := Term.String [],
    hflat := ?_,
    hlen := by simpa using StrInReConsumeInternal.consume_str_value_len_string w,
    hunp := ?_,
    hexEmpty := by simp [__str_is_empty],
    hAtomTy := StrInReConsumeInternal.consume_char_atoms_type w T hTy,
    hAtomShape := StrInReConsumeInternal.consume_char_atoms_shape w
  }
  · cases w with
    | nil =>
        rw [str_flatten_nary_intro_empty]
        rfl
    | cons c cs =>
        rw [str_flatten_nary_intro_cons,
          ← StrInReConsumeInternal.consume_atom_chain_string_atoms_eq_substrWord (c :: cs)]
  · rw [show __eo_to_smt (Term.String w) = SmtTerm.String w from rfl] at hEval
    simp only [__smtx_model_eval] at hEval
    injection hEval with hS
    rw [← hS, StrInReConsumeInternal.consume_unpack_pack_string_map,
      StrInReConsumeInternal.consume_char_atoms_unpack]

theorem StrInReConsumeInternal.consume_intro_word_view_list_rev_eval_reverse_string
    (M : SmtModel) (t : Term) (S revS : SmtSeq) (T : SmtType)
    (v : StrInReConsumeInternal.ConsumeIntroWordView M t S T)
    (hRevEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro t)))) =
        SmtValue.Seq revS) :
    native_unpack_string revS = (native_unpack_string S).reverse := by
  have hRevEvalChain :
      __smtx_model_eval M
          (__eo_to_smt
            (StrInReConsumeInternal.consume_atom_chain_term v.atoms.reverse v.ex)) =
        SmtValue.Seq revS := by
    simpa [v.hflat, StrInReConsumeInternal.consume_eo_list_rev_atom_chain v.atoms v.ex
      v.hexEmpty] using hRevEval
  have hRevUnpack :
      native_unpack_seq revS =
        v.atoms.reverse.map (consume_seq_elem_val M) :=
    StrInReConsumeInternal.consume_chain_unpack_td M v.ex v.hexEmpty v.atoms.reverse revS
      hRevEvalChain
      (by
        intro a ha sa hEval
        exact StrInReConsumeInternal.consume_atom_eval_unpack M a
          (v.hAtomShape a (List.mem_reverse.mp ha)) sa hEval)
  unfold native_unpack_string
  rw [hRevUnpack, v.hunp]
  simp [List.map_reverse]

theorem StrInReConsumeInternal.consume_native_unpack_string_eq_of_seq_rel
    {ss ss' : SmtSeq}
    (hRel :
      RuleProofs.smt_value_rel (SmtValue.Seq ss') (SmtValue.Seq ss)) :
    native_unpack_string ss' = native_unpack_string ss := by
  have hSeq : RuleProofs.smt_seq_rel ss' ss := by
    simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using hRel
  have hEq : ss' = ss := (RuleProofs.smt_seq_rel_iff_eq ss' ss).1 hSeq
  subst ss'
  rfl

theorem StrInReConsumeInternal.consume_intro_word_view_reverse_native_bridge
    (M : SmtModel) (t : Term) (S revS : SmtSeq) (T : SmtType)
    (rv revRv : SmtRegLan)
    (hSeqTy :
      __smtx_typeof_value (SmtValue.Seq S) =
        SmtType.Seq SmtType.Char)
    (v : StrInReConsumeInternal.ConsumeIntroWordView M t S T)
    (hRevEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro t)))) =
        SmtValue.Seq revS)
    (hRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan revRv)
        (SmtValue.RegLan (StrInReConsumeInternal.native_re_reverse_raw_consume_local rv))) :
    native_str_in_re (native_unpack_string S) rv =
      native_str_in_re (native_unpack_string revS) revRv := by
  have hRevUnpack :
      native_unpack_string revS = (native_unpack_string S).reverse :=
    StrInReConsumeInternal.consume_intro_word_view_list_rev_eval_reverse_string M t S revS T v
      hRevEval
  exact StrInReConsumeInternal.native_str_in_re_eq_of_unpack_reverse_reglan_rel_consume_local
    hSeqTy hRevUnpack hRegRel

theorem StrInReConsumeInternal.consume_intro_word_view_flat_rel_reverse_native_bridge
    (M : SmtModel) (t : Term) (ss flatSs revSs : SmtSeq)
    (T : SmtType) (rv revRv : SmtRegLan)
    (hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char)
    (hFlatRel :
      RuleProofs.smt_value_rel (SmtValue.Seq flatSs) (SmtValue.Seq ss))
    (v : StrInReConsumeInternal.ConsumeIntroWordView M t flatSs T)
    (hRevEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro t)))) =
        SmtValue.Seq revSs)
    (hRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan revRv)
        (SmtValue.RegLan (StrInReConsumeInternal.native_re_reverse_raw_consume_local rv))) :
    native_str_in_re (native_unpack_string ss) rv =
      native_str_in_re (native_unpack_string revSs) revRv := by
  have hFlatUnpack :
      native_unpack_string flatSs = native_unpack_string ss :=
    StrInReConsumeInternal.consume_native_unpack_string_eq_of_seq_rel hFlatRel
  have hFlatSeqTy :
      __smtx_typeof_value (SmtValue.Seq flatSs) =
        SmtType.Seq SmtType.Char := by
    have hSeq : RuleProofs.smt_seq_rel flatSs ss := by
      simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using
        hFlatRel
    have hEq : flatSs = ss :=
      (RuleProofs.smt_seq_rel_iff_eq flatSs ss).1 hSeq
    subst flatSs
    exact hSeqTy
  have hBridge :
      native_str_in_re (native_unpack_string flatSs) rv =
        native_str_in_re (native_unpack_string revSs) revRv :=
    StrInReConsumeInternal.consume_intro_word_view_reverse_native_bridge M t flatSs revSs T rv
      revRv hFlatSeqTy v hRevEval hRegRel
  simpa [hFlatUnpack] using hBridge

theorem StrInReConsumeInternal.consume_string_flat_rel_reverse_native_bridge
    (M : SmtModel) (w : native_String)
    (ss flatSs revSs : SmtSeq) (T : SmtType)
    (rv revRv : SmtRegLan)
    (hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.String w)) = SmtType.Seq T)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt (Term.String w)) =
        SmtValue.Seq ss)
    (hFlatRel :
      RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
        (SmtValue.Seq ss))
    (hRevEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro (Term.String w))))) =
        SmtValue.Seq revSs)
    (hRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan revRv)
        (SmtValue.RegLan (StrInReConsumeInternal.native_re_reverse_raw_consume_local rv))) :
    native_str_in_re (native_unpack_string ss) rv =
      native_str_in_re (native_unpack_string revSs) revRv := by
  have hFlatEq : flatSs = ss := by
    have hSeq : RuleProofs.smt_seq_rel flatSs ss := by
      simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using
        hFlatRel
    exact (RuleProofs.smt_seq_rel_iff_eq flatSs ss).1 hSeq
  subst flatSs
  exact StrInReConsumeInternal.consume_intro_word_view_flat_rel_reverse_native_bridge M
    (Term.String w) ss ss revSs T rv revRv hSeqTy
    (RuleProofs.smt_value_rel_refl (SmtValue.Seq ss))
    (StrInReConsumeInternal.consume_intro_word_view_string M w ss T hTy hSEval) hRevEval
    hRegRel

theorem native_str_in_re_re_mult_concat_eq_tail_of_no_prefix_local
    (xs : native_String) (r tail : SmtRegLan)
    (hNoPrefix :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
        pre ≠ [] ->
          native_str_in_re pre r = false) :
    native_str_in_re xs (native_re_concat (native_re_mult r) tail) =
      native_str_in_re xs tail := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    by_cases hValid : native_string_valid xs = true
    · have hListMem :
          nativeListInRe xs
              (native_re_mk_concat (native_re_mult r) tail) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (native_re_mult r) tail).1 hListMem with
        ⟨starPre, suf, hAppend, hStarPre, hSuf⟩
      by_cases hStarPreEmpty : starPre = []
      · subst starPre
        simp at hAppend
        subst suf
        simpa [native_str_in_re, hValid, nativeListInRe] using hSuf
      · rcases
          nativeListInRe_re_mult_nonempty_prefix_local starPre r hStarPre
            hStarPreEmpty with
          ⟨chunk, rest, hChunkAppend, hChunkNe, hChunkMem⟩
        have hChunkValid : native_string_valid chunk = true :=
          native_string_valid_append_left chunk (rest ++ suf) (by
            rw [← List.append_assoc, hChunkAppend, hAppend]
            exact hValid)
        have hChunkNative : native_str_in_re chunk r = true := by
          simpa [native_str_in_re, hChunkValid, nativeListInRe] using
            hChunkMem
        have hChunkFalse :
            native_str_in_re chunk r = false :=
          hNoPrefix chunk (rest ++ suf) (by
            rw [← List.append_assoc, hChunkAppend, hAppend]) hChunkNe
        rw [hChunkFalse] at hChunkNative
        cases hChunkNative
    · simp [native_str_in_re, hValid] at hMem
  · intro hTail
    exact native_str_in_re_re_concat_intro [] xs
      (native_re_mult r) tail
      (native_str_in_re_re_mult_empty_local r) hTail

theorem native_str_in_re_re_mult_concat_nonempty_decomp_local
    (xs : native_String) (r tail : SmtRegLan)
    (hTailFalse : native_str_in_re xs tail = false)
    (hMem :
      native_str_in_re xs
        (native_re_concat (native_re_mult r) tail) = true) :
    ∃ pre suf : native_String,
      pre ++ suf = xs ∧
      pre ≠ [] ∧
      native_str_in_re pre r = true ∧
      native_str_in_re suf (native_re_concat (native_re_mult r) tail) =
        true := by
  by_cases hValid : native_string_valid xs = true
  · have hListMem :
        nativeListInRe xs
          (native_re_mk_concat (native_re_mult r) tail) = true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append xs
          (native_re_mult r) tail).1 hListMem with
      ⟨starPre, suf, hAppend, hStarPre, hSuf⟩
    by_cases hStarPreEmpty : starPre = []
    · subst starPre
      simp at hAppend
      subst suf
      have hTailTrue : native_str_in_re xs tail = true := by
        simpa [native_str_in_re, hValid, nativeListInRe] using hSuf
      rw [hTailFalse] at hTailTrue
      cases hTailTrue
    · rcases
        nativeListInRe_re_mult_nonempty_prefix_decomp_local starPre r
          hStarPre hStarPreEmpty with
        ⟨chunk, rest, hChunkAppend, hChunkNe, hChunkMem, hRestStar⟩
      have hChunkValid : native_string_valid chunk = true :=
        native_string_valid_append_left chunk (rest ++ suf) (by
          rw [← List.append_assoc, hChunkAppend, hAppend]
          exact hValid)
      have hRestValid : native_string_valid rest = true :=
        let hStarPreValid : native_string_valid starPre = true :=
          native_string_valid_append_left starPre suf (by
            simpa [hAppend] using hValid)
        let hChunkRestValid : native_string_valid (chunk ++ rest) = true := by
          simpa [hChunkAppend] using hStarPreValid
        native_string_valid_append_right chunk rest hChunkRestValid
      have hSufValid : native_string_valid suf = true :=
        native_string_valid_append_right starPre suf (by
          simpa [hAppend] using hValid)
      have hChunkNative :
          native_str_in_re chunk r = true := by
        simpa [native_str_in_re, hChunkValid, nativeListInRe] using
          hChunkMem
      have hRestStarNative :
          native_str_in_re rest (native_re_mult r) = true := by
        simpa [native_str_in_re, hRestValid, nativeListInRe] using
          hRestStar
      have hSufNative : native_str_in_re suf tail = true := by
        simpa [native_str_in_re, hSufValid, nativeListInRe] using hSuf
      have hResidualNative :
          native_str_in_re (rest ++ suf)
            (native_re_concat (native_re_mult r) tail) = true :=
        native_str_in_re_re_concat_intro rest suf (native_re_mult r) tail
          hRestStarNative hSufNative
      exact ⟨chunk, rest ++ suf, by
        rw [← List.append_assoc, hChunkAppend, hAppend],
        hChunkNe, hChunkNative, hResidualNative⟩
  · simp [native_str_in_re, hValid] at hMem

theorem native_str_in_re_re_mult_concat_cons_local
    (xs : native_String) (r tail : SmtRegLan)
    (hMem :
      native_str_in_re xs
        (native_re_concat r (native_re_concat (native_re_mult r) tail)) =
        true) :
    native_str_in_re xs (native_re_concat (native_re_mult r) tail) =
      true := by
  by_cases hValid : native_string_valid xs = true
  · have hListMem :
        nativeListInRe xs
          (native_re_mk_concat r
            (native_re_concat (native_re_mult r) tail)) = true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append xs r
          (native_re_concat (native_re_mult r) tail)).1 hListMem with
      ⟨pre, suf, hAppend, hPre, hSuf⟩
    have hPreValid : native_string_valid pre = true :=
      native_string_valid_append_left pre suf (by
        simpa [hAppend] using hValid)
    have hSufValid : native_string_valid suf = true :=
      native_string_valid_append_right pre suf (by
        simpa [hAppend] using hValid)
    have hPreNative : native_str_in_re pre r = true := by
      simpa [native_str_in_re, hPreValid, nativeListInRe] using hPre
    have hPreStar : native_str_in_re pre (native_re_mult r) = true :=
      native_includes_star_self r pre hPreValid hPreNative
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append suf
          (native_re_mult r) tail).1
          (by have hsimpa := hSuf; (try simp [native_re_concat] at hsimpa ⊢); exact hsimpa) with
      ⟨starPart, tailPart, hSufAppend, hStarPart, hTailPart⟩
    have hPreStarList :
        nativeListInRe pre (native_re_mult r) = true := by
      simpa [native_str_in_re, hPreValid, nativeListInRe] using hPreStar
    have hStarAppend :
        nativeListInRe (pre ++ starPart) (native_re_mult r) = true := by
      have hsimpa :=
        nativeListInRe_mk_star_append pre starPart r
          (by have hsimpa := hPreStarList; (try simp [native_re_mult] at hsimpa ⊢); exact hsimpa)
          (by have hsimpa := hStarPart; (try simp [native_re_mult] at hsimpa ⊢); exact hsimpa)
      try simp [native_re_mult] at hsimpa ⊢
      exact hsimpa
    have hWholeList :
        nativeListInRe xs
          (native_re_mk_concat (native_re_mult r) tail) = true := by
      refine (nativeListInRe_mk_concat_true_iff_exists_append xs
        (native_re_mult r) tail).2 ?_
      refine ⟨pre ++ starPart, tailPart, ?_, hStarAppend, hTailPart⟩
      rw [List.append_assoc, hSufAppend, hAppend]
    have hWhole :=
      show native_str_in_re xs (native_re_concat (native_re_mult r) tail) =
        true by
        have hsimpa := hWholeList
        try simp [native_str_in_re, hValid, native_re_concat] at hsimpa ⊢
        exact hsimpa
    exact hWhole
  · simp [native_str_in_re, hValid] at hMem

theorem native_str_in_re_re_mult_concat_residual_eq_local
    (xs tailStr : native_String) (r tail : SmtRegLan)
    (hTailFalse : native_str_in_re xs tail = false)
    (hResidual :
      native_str_in_re xs
          (native_re_concat r (native_re_concat (native_re_mult r) tail)) =
        native_str_in_re tailStr
          (native_re_concat (native_re_mult r) tail)) :
    native_str_in_re xs (native_re_concat (native_re_mult r) tail) =
      native_str_in_re tailStr (native_re_concat (native_re_mult r) tail) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    rcases native_str_in_re_re_mult_concat_nonempty_decomp_local xs r tail
        hTailFalse hMem with
      ⟨pre, suf, hAppend, _hPreNe, hPre, hSuf⟩
    have hConcat :
        native_str_in_re xs
            (native_re_concat r
              (native_re_concat (native_re_mult r) tail)) = true := by
      have hIntro :=
        native_str_in_re_re_concat_intro pre suf r
          (native_re_concat (native_re_mult r) tail) hPre hSuf
      simpa [hAppend] using hIntro
    rw [hResidual] at hConcat
    exact hConcat
  · intro hTailMem
    have hConcat :
        native_str_in_re xs
            (native_re_concat r
              (native_re_concat (native_re_mult r) tail)) = true := by
      rw [hResidual]
      exact hTailMem
    exact native_str_in_re_re_mult_concat_cons_local xs r tail hConcat

theorem native_str_in_re_re_mult_residual_eq_nonempty_local
    (xs tailStr : native_String) (r : SmtRegLan)
    (hXsNe : xs ≠ [])
    (hResidual :
      native_str_in_re xs (native_re_concat r (native_re_mult r)) =
        native_str_in_re tailStr (native_re_mult r)) :
    native_str_in_re xs (native_re_mult r) =
      native_str_in_re tailStr (native_re_mult r) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    by_cases hValid : native_string_valid xs = true
    · have hListMem :
          nativeListInRe xs (native_re_mult r) = true := by
        simpa [native_str_in_re, hValid, nativeListInRe] using hMem
      rcases nativeListInRe_re_mult_nonempty_prefix_decomp_local xs r
          hListMem hXsNe with
        ⟨pre, suf, hAppend, _hPreNe, hPre, hSuf⟩
      have hPreValid : native_string_valid pre = true :=
        native_string_valid_append_left pre suf (by
          simpa [hAppend] using hValid)
      have hSufValid : native_string_valid suf = true :=
        native_string_valid_append_right pre suf (by
          simpa [hAppend] using hValid)
      have hPreNative : native_str_in_re pre r = true := by
        simpa [native_str_in_re, hPreValid, nativeListInRe] using hPre
      have hSufNative :
          native_str_in_re suf (native_re_mult r) = true := by
        simpa [native_str_in_re, hSufValid, nativeListInRe] using hSuf
      have hConcat :
          native_str_in_re xs
              (native_re_concat r (native_re_mult r)) = true := by
        have hIntro :=
          native_str_in_re_re_concat_intro pre suf r (native_re_mult r)
            hPreNative hSufNative
        simpa [hAppend] using hIntro
      rw [hResidual] at hConcat
      exact hConcat
    · simp [native_str_in_re, hValid] at hMem
  · intro hMem
    have hConcat :
        native_str_in_re xs (native_re_concat r (native_re_mult r)) =
          true := by
      rw [hResidual]
      exact hMem
    have hCons :
        native_str_in_re xs
            (native_re_concat (native_re_mult r) (native_str_to_re [])) =
          true := by
      apply native_str_in_re_re_mult_concat_cons_local xs r
        (native_str_to_re [])
      simpa [native_re_concat_right_empty_local] using hConcat
    simpa [native_re_concat_right_empty_local] using hCons

theorem native_str_in_re_re_mult_concat_no_prefix_local
    (xs : native_String) (r tail : SmtRegLan)
    (hTailNoPrefix :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre tail = false)
    (hConsNoPrefix :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre
            (native_re_concat r (native_re_concat (native_re_mult r) tail)) =
            false) :
    ∀ pre suf : native_String,
      pre ++ suf = xs ->
        native_str_in_re pre (native_re_concat (native_re_mult r) tail) =
          false := by
  intro pre suf hAppend
  apply Bool.eq_false_iff.mpr
  intro hPreMem
  have hTailFalse : native_str_in_re pre tail = false :=
    hTailNoPrefix pre suf hAppend
  rcases native_str_in_re_re_mult_concat_nonempty_decomp_local pre r tail
      hTailFalse hPreMem with
    ⟨chunk, rest, hChunkAppend, _hChunkNe, hChunk, hRest⟩
  have hConsMem :
      native_str_in_re pre
          (native_re_concat r (native_re_concat (native_re_mult r) tail)) =
        true := by
    have hIntro :=
      native_str_in_re_re_concat_intro chunk rest r
        (native_re_concat (native_re_mult r) tail) hChunk hRest
    simpa [hChunkAppend] using hIntro
  rw [hConsNoPrefix pre suf hAppend] at hConsMem
  cases hConsMem

theorem native_str_in_re_re_concat_no_prefix_of_residual_local
    (xs tail : native_String) (r1 r2 : SmtRegLan)
    (hXsValid : native_string_valid xs = true)
    (hResidual :
      ∀ q : SmtRegLan,
        native_str_in_re xs (native_re_concat r1 q) =
          native_str_in_re tail q)
    (hTailNoPrefix :
      ∀ pre suf : native_String,
        pre ++ suf = tail ->
          native_str_in_re pre r2 = false) :
    ∀ pre suf : native_String,
      pre ++ suf = xs ->
        native_str_in_re pre (native_re_concat r1 r2) = false := by
  intro pre suf hAppend
  apply Bool.eq_false_iff.mpr
  intro hPreMem
  have hSufValid : native_string_valid suf = true :=
    native_string_valid_append_right pre suf (by
      simpa [hAppend] using hXsValid)
  have hWholeMem :
      native_str_in_re xs
        (native_re_concat r1
          (native_re_concat r2 (native_str_to_re suf))) = true := by
    have hAppendMem :=
      native_str_in_re_re_concat_append_str_to_re_intro_local pre suf
        r1 r2 hPreMem hSufValid
    simpa [hAppend] using hAppendMem
  have hTailFalse :
      native_str_in_re tail
        (native_re_concat r2 (native_str_to_re suf)) = false :=
    native_str_in_re_re_concat_false_of_no_split_local tail r2
      (native_str_to_re suf) hTailNoPrefix
  have hResidualEq :=
    hResidual (native_re_concat r2 (native_str_to_re suf))
  rw [hResidualEq, hTailFalse] at hWholeMem
  cases hWholeMem

theorem native_str_in_re_re_concat_no_prefix_of_residual_suffix_local
    (xs tail : native_String) (r1 r2 : SmtRegLan)
    (hXsValid : native_string_valid xs = true)
    (hResidual :
      ∀ suf : native_String,
        native_string_valid suf = true ->
          native_str_in_re xs
              (native_re_concat r1
                (native_re_concat r2 (native_str_to_re suf))) =
            native_str_in_re tail
              (native_re_concat r2 (native_str_to_re suf)))
    (hTailNoPrefix :
      ∀ pre suf : native_String,
        pre ++ suf = tail ->
          native_str_in_re pre r2 = false) :
    ∀ pre suf : native_String,
      pre ++ suf = xs ->
        native_str_in_re pre (native_re_concat r1 r2) = false := by
  intro pre suf hAppend
  apply Bool.eq_false_iff.mpr
  intro hPreMem
  have hSufValid : native_string_valid suf = true :=
    native_string_valid_append_right pre suf (by
      simpa [hAppend] using hXsValid)
  have hWholeMem :
      native_str_in_re xs
        (native_re_concat r1
          (native_re_concat r2 (native_str_to_re suf))) = true := by
    have hAppendMem :=
      native_str_in_re_re_concat_append_str_to_re_intro_local pre suf
        r1 r2 hPreMem hSufValid
    simpa [hAppend] using hAppendMem
  have hTailFalse :
      native_str_in_re tail
        (native_re_concat r2 (native_str_to_re suf)) = false :=
    native_str_in_re_re_concat_false_of_no_split_local tail r2
      (native_str_to_re suf) hTailNoPrefix
  have hResidualEq := hResidual suf hSufValid
  rw [hResidualEq, hTailFalse] at hWholeMem
  cases hWholeMem

theorem native_str_in_re_re_union_false_of_both_local
    (xs : native_String) (r1 r2 : SmtRegLan)
    (hLeft : native_str_in_re xs r1 = false)
    (hRight : native_str_in_re xs r2 = false) :
    native_str_in_re xs (native_re_union r1 r2) = false := by
  rw [native_str_in_re_re_union, hLeft, hRight]
  rfl

theorem native_str_in_re_re_union_false_of_no_split_local
    (xs : native_String) (r1 r2 : SmtRegLan)
    (hLeft :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r1 = false)
    (hRight :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r2 = false) :
    ∀ pre suf : native_String,
      pre ++ suf = xs ->
        native_str_in_re pre (native_re_union r1 r2) = false := by
  intro pre suf hAppend
  exact native_str_in_re_re_union_false_of_both_local pre r1 r2
    (hLeft pre suf hAppend) (hRight pre suf hAppend)

theorem native_str_in_re_re_inter_false_of_left_local
    (xs : native_String) (r1 r2 : SmtRegLan)
    (hLeft : native_str_in_re xs r1 = false) :
    native_str_in_re xs (native_re_inter r1 r2) = false := by
  rw [native_str_in_re_re_inter, hLeft]
  rfl

theorem native_str_in_re_re_inter_false_of_right_local
    (xs : native_String) (r1 r2 : SmtRegLan)
    (hRight : native_str_in_re xs r2 = false) :
    native_str_in_re xs (native_re_inter r1 r2) = false := by
  rw [native_str_in_re_re_inter, hRight]
  cases native_str_in_re xs r1 <;> rfl

theorem native_str_in_re_re_inter_false_of_left_no_split_local
    (xs : native_String) (r1 r2 : SmtRegLan)
    (hLeft :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r1 = false) :
    ∀ pre suf : native_String,
      pre ++ suf = xs ->
        native_str_in_re pre (native_re_inter r1 r2) = false := by
  intro pre suf hAppend
  exact native_str_in_re_re_inter_false_of_left_local pre r1 r2
    (hLeft pre suf hAppend)

theorem native_str_in_re_re_inter_false_of_right_no_split_local
    (xs : native_String) (r1 r2 : SmtRegLan)
    (hRight :
      ∀ pre suf : native_String,
        pre ++ suf = xs ->
          native_str_in_re pre r2 = false) :
    ∀ pre suf : native_String,
      pre ++ suf = xs ->
        native_str_in_re pre (native_re_inter r1 r2) = false := by
  intro pre suf hAppend
  exact native_str_in_re_re_inter_false_of_right_local pre r1 r2
    (hRight pre suf hAppend)

theorem native_str_in_re_str_to_re_concat_singleton_false_local
    (c d : native_Char) (ys : native_String) (r : SmtRegLan)
    (hNe : c ≠ d) :
    native_str_in_re (c :: ys)
        (native_re_concat (native_str_to_re [d]) r) =
      false := by
  by_cases hValid : native_string_valid (c :: ys) = true
  · apply Bool.eq_false_iff.mpr
    intro hMem
    have hListMem :
        nativeListInRe (c :: ys)
            (native_re_mk_concat (native_str_to_re [d]) r) = true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hValid, native_re_concat, nativeListInRe] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append (c :: ys)
          (native_str_to_re [d]) r).1 hListMem with
      ⟨left, right, hAppend, hLeft, _hRight⟩
    have hLeftValid : native_string_valid left = true :=
      native_string_valid_append_left left right (by
        simpa [hAppend] using hValid)
    have hLeftMem :
        native_str_in_re left (native_str_to_re [d]) = true := by
      simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
    have hLeftEq : left = [d] :=
      native_str_in_re_str_to_re_eq hLeftValid hLeftMem
    subst left
    cases hAppend
    exact hNe rfl
  · simp [native_str_in_re, hValid]

theorem native_str_in_re_str_to_re_concat_singleton_prefix_false_local
    (c d : native_Char) (ys : native_String) (r : SmtRegLan)
    (hNe : c ≠ d) :
    ∀ pre suf : native_String,
      pre ++ suf = c :: ys ->
        native_str_in_re pre
          (native_re_concat (native_str_to_re [d]) r) = false := by
  intro pre suf hAppend
  cases pre with
  | nil =>
      cases r <;>
        simp [native_str_in_re, nativeListInRe, native_re_concat,
          native_str_to_re, impl_native_re_of_list, native_re_nullable]
  | cons p ps =>
      have hp : p = c := by
        cases hAppend
        rfl
      subst p
      exact native_str_in_re_str_to_re_concat_singleton_false_local c d ps
        r hNe

theorem native_str_in_re_re_allchar_concat_singleton_left_local
    (c : native_Char) (ys : native_String) (r : SmtRegLan)
    (hc : native_char_valid c = true) :
    native_str_in_re (c :: ys) (native_re_concat native_re_allchar r) =
      native_str_in_re ys r := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    by_cases hValid : native_string_valid (c :: ys) = true
    · have hListMem :
          nativeListInRe (c :: ys)
              (native_re_mk_concat native_re_allchar r) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, hValid, native_re_concat, nativeListInRe] at hsimpa ⊢
        exact hsimpa
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append (c :: ys)
            native_re_allchar r).1 hListMem with
        ⟨left, right, hAppend, hLeft, hRight⟩
      have hLeftFacts := (nativeListInRe_allchar_true_iff left).1 hLeft
      have hLeftLen : left.length = 1 := hLeftFacts.1
      cases left with
      | nil =>
          simp at hLeftLen
      | cons x xs =>
          cases xs with
          | nil =>
              simp at hAppend
              rcases hAppend with ⟨hx, hRightEq⟩
              subst x
              subst right
              have hYsValid : native_string_valid ys = true :=
                native_string_valid_append_right [c] ys hValid
              simpa [native_str_in_re, hYsValid, nativeListInRe] using hRight
          | cons _x2 _xs2 =>
              simp at hLeftLen
    · simp [native_str_in_re, hValid] at hMem
  · intro hMem
    have hAllchar : native_str_in_re [c] native_re_allchar = true := by
      have hList : nativeListInRe [c] native_re_allchar = true :=
        (nativeListInRe_allchar_true_iff [c]).2
          ⟨by simp, by simpa using hc⟩
      simpa [native_str_in_re, native_string_valid, hc, nativeListInRe]
        using hList
    exact native_str_in_re_re_concat_intro [c] ys native_re_allchar r
      hAllchar hMem

theorem native_str_in_re_re_allchar_concat_singleton_prefix_false_of_tail_no_prefix_local
    (c : native_Char) (ys : native_String) (r : SmtRegLan)
    (hNoTail :
      ∀ pre suf : native_String,
        pre ++ suf = ys ->
          native_str_in_re pre r = false) :
    ∀ pre suf : native_String,
      pre ++ suf = c :: ys ->
        native_str_in_re pre (native_re_concat native_re_allchar r) =
          false := by
  intro pre suf hAppend
  by_cases hPreValid : native_string_valid pre = true
  · apply Bool.eq_false_iff.mpr
    intro hMem
    have hListMem :
        nativeListInRe pre
            (native_re_mk_concat native_re_allchar r) = true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hPreValid, native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append pre
          native_re_allchar r).1 hListMem with
      ⟨left, right, hSplit, hLeft, hRight⟩
    have hLeftFacts := (nativeListInRe_allchar_true_iff left).1 hLeft
    have hLeftLen : left.length = 1 := hLeftFacts.1
    cases left with
    | nil =>
        simp at hLeftLen
    | cons x xs =>
        cases xs with
        | nil =>
            have hRightAppend : right ++ suf = ys := by
              have hPreEq : pre = x :: right := by
                simpa using hSplit.symm
              subst pre
              cases hAppend
              rfl
            have hRightValid : native_string_valid right = true :=
              native_string_valid_append_right [x] right (by
                simpa [hSplit] using hPreValid)
            have hRightMem : native_str_in_re right r = true := by
              simpa [native_str_in_re, hRightValid, nativeListInRe]
                using hRight
            rw [hNoTail right suf hRightAppend] at hRightMem
            cases hRightMem
        | cons _x2 _xs2 =>
            simp at hLeftLen
  · simp [native_str_in_re, hPreValid]

theorem native_re_nullable_fold_empty_false_local
    (xs : List native_Char) :
    native_re_nullable
        (xs.foldl (fun acc c => native_re_deriv c acc) SmtRegLan.empty) =
      false := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simpa [native_re_deriv] using ih

theorem native_str_in_re_re_range_singleton_length_local
    {xs : native_String} {lo hi : native_Char}
    (hMem : native_str_in_re xs (native_re_range [lo] [hi]) = true) :
    xs.length = 1 := by
  have hList :
      nativeListInRe xs (native_re_range [lo] [hi]) = true :=
    by
      have h := (by simpa [native_str_in_re] using hMem :
        native_string_valid xs = true ∧
          nativeListInRe xs (native_re_range [lo] [hi]) = true)
      exact h.2
  exact nativeListInRe_re_range_true_length xs
    (impl_native_string_to_values [lo]) (impl_native_string_to_values [hi]) hList

theorem native_str_in_re_re_range_concat_singleton_left_true_local
    (c lo hi : native_Char) (ys : native_String) (r : SmtRegLan)
    (hHead :
      native_str_in_re [c] (native_re_range [lo] [hi]) = true) :
    native_str_in_re (c :: ys)
        (native_re_concat (native_re_range [lo] [hi]) r) =
      native_str_in_re ys r := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    by_cases hValid : native_string_valid (c :: ys) = true
    · have hListMem :
          nativeListInRe (c :: ys)
              (native_re_mk_concat (native_re_range [lo] [hi]) r) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, hValid, native_re_concat, nativeListInRe] at hsimpa ⊢
        exact hsimpa
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append (c :: ys)
            (native_re_range [lo] [hi]) r).1 hListMem with
        ⟨left, right, hAppend, hLeft, hRight⟩
      have hLeftValid : native_string_valid left = true :=
        native_string_valid_append_left left right (by
          simpa [hAppend] using hValid)
      have hLeftMem :
          native_str_in_re left (native_re_range [lo] [hi]) = true := by
        simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
      have hLeftLen : left.length = 1 :=
        native_str_in_re_re_range_singleton_length_local hLeftMem
      cases left with
      | nil =>
          simp at hLeftLen
      | cons x xs =>
          cases xs with
          | nil =>
              simp at hAppend
              rcases hAppend with ⟨hx, hRightEq⟩
              subst x
              subst right
              have hYsValid : native_string_valid ys = true :=
                native_string_valid_append_right [c] ys hValid
              simpa [native_str_in_re, hYsValid, nativeListInRe] using hRight
          | cons _x2 _xs2 =>
              simp at hLeftLen
    · simp [native_str_in_re, hValid] at hMem
  · intro hMem
    exact native_str_in_re_re_concat_intro [c] ys
      (native_re_range [lo] [hi]) r hHead hMem

theorem native_str_in_re_re_range_concat_singleton_prefix_false_of_tail_no_prefix_local
    (c lo hi : native_Char) (ys : native_String) (r : SmtRegLan)
    (hNoTail :
      ∀ pre suf : native_String,
        pre ++ suf = ys ->
          native_str_in_re pre r = false) :
    ∀ pre suf : native_String,
      pre ++ suf = c :: ys ->
        native_str_in_re pre
          (native_re_concat (native_re_range [lo] [hi]) r) = false := by
  intro pre suf hAppend
  by_cases hPreValid : native_string_valid pre = true
  · apply Bool.eq_false_iff.mpr
    intro hMem
    have hListMem :
        nativeListInRe pre
            (native_re_mk_concat (native_re_range [lo] [hi]) r) =
          true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hPreValid, native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append pre
          (native_re_range [lo] [hi]) r).1 hListMem with
      ⟨left, right, hSplit, hLeft, hRight⟩
    have hLeftValid : native_string_valid left = true :=
      native_string_valid_append_left left right (by
        simpa [hSplit] using hPreValid)
    have hLeftMem :
        native_str_in_re left (native_re_range [lo] [hi]) = true := by
      simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
    have hLeftLen : left.length = 1 :=
      native_str_in_re_re_range_singleton_length_local hLeftMem
    cases left with
    | nil =>
        simp at hLeftLen
    | cons x xs =>
        cases xs with
        | nil =>
            have hRightAppend : right ++ suf = ys := by
              have hPreEq : pre = x :: right := by
                simpa using hSplit.symm
              subst pre
              cases hAppend
              rfl
            have hRightValid : native_string_valid right = true :=
              native_string_valid_append_right [x] right (by
                simpa [hSplit] using hPreValid)
            have hRightMem : native_str_in_re right r = true := by
              simpa [native_str_in_re, hRightValid, nativeListInRe]
                using hRight
            rw [hNoTail right suf hRightAppend] at hRightMem
            cases hRightMem
        | cons _x2 _xs2 =>
            simp at hLeftLen
  · simp [native_str_in_re, hPreValid]

theorem native_str_in_re_re_range_concat_singleton_left_false_local
    (c lo hi : native_Char) (ys : native_String) (r : SmtRegLan)
    (hHead :
      native_str_in_re [c] (native_re_range [lo] [hi]) = false) :
    native_str_in_re (c :: ys)
        (native_re_concat (native_re_range [lo] [hi]) r) =
      false := by
  by_cases hValid : native_string_valid (c :: ys) = true
  · apply Bool.eq_false_iff.mpr
    intro hMem
    have hListMem :
        nativeListInRe (c :: ys)
            (native_re_mk_concat (native_re_range [lo] [hi]) r) = true := by
      have hsimpa := hMem
      try simp [native_str_in_re, hValid, native_re_concat, nativeListInRe] at hsimpa ⊢
      exact hsimpa
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append (c :: ys)
          (native_re_range [lo] [hi]) r).1 hListMem with
      ⟨left, right, hAppend, hLeft, _hRight⟩
    have hLeftValid : native_string_valid left = true :=
      native_string_valid_append_left left right (by
        simpa [hAppend] using hValid)
    have hLeftMem :
        native_str_in_re left (native_re_range [lo] [hi]) = true := by
      simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
    have hLeftLen : left.length = 1 :=
      native_str_in_re_re_range_singleton_length_local hLeftMem
    cases left with
    | nil =>
        simp at hLeftLen
    | cons x xs =>
        cases xs with
        | nil =>
            simp at hAppend
            rcases hAppend with ⟨hx, _hRightEq⟩
            subst x
            rw [hHead] at hLeftMem
            cases hLeftMem
        | cons _x2 _xs2 =>
            simp at hLeftLen
  · simp [native_str_in_re, hValid]

theorem native_str_in_re_re_range_concat_singleton_left_prefix_false_local
    (c lo hi : native_Char) (ys : native_String) (r : SmtRegLan)
    (hHead :
      native_str_in_re [c] (native_re_range [lo] [hi]) = false) :
    ∀ pre suf : native_String,
      pre ++ suf = c :: ys ->
        native_str_in_re pre
          (native_re_concat (native_re_range [lo] [hi]) r) = false := by
  intro pre suf hAppend
  cases pre with
  | nil =>
      cases r <;>
        simp [native_str_in_re, nativeListInRe, native_re_concat,
          native_re_range, native_re_nullable]
  | cons p ps =>
      have hp : p = c := by
        cases hAppend
        rfl
      subst p
      exact native_str_in_re_re_range_concat_singleton_left_false_local c
        lo hi ps r hHead

theorem native_unpack_string_pack_seq_concat_local
    (T : SmtType) (ss1 ss2 : SmtSeq) :
    native_unpack_string
        (native_pack_seq T
          (native_seq_concat (native_unpack_seq ss1) (native_unpack_seq ss2))) =
      native_unpack_string ss1 ++ native_unpack_string ss2 := by
  simp [native_unpack_string, native_seq_concat, Smtm.native_unpack_pack_seq,
    List.map_append]

theorem StrInReConsumeInternal.eval_str_concat_seq_cases_consume_local
    (M : SmtModel) (x y : Term) (ss : SmtSeq)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
        SmtValue.Seq ss) :
    ∃ sx sy,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ∧
      ss =
        native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_seq_concat (native_unpack_seq sx)
            (native_unpack_seq sy)) := by
  change __smtx_model_eval M
      (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) =
    SmtValue.Seq ss at hEval
  cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
    cases hy : __smtx_model_eval M (__eo_to_smt y) <;>
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hx, hy] at hEval
  case Seq.Seq sx sy =>
    exact ⟨sx, sy, rfl, rfl, hEval.symm⟩

theorem str_re_consume_str_to_re_singleton_no_prefix_of_evals_local
    (M : SmtModel) (hM : model_wf M)
    (s2 r : Term) (c d : native_Char)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hNe : c ≠ d) :
    ∀ ss rv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [d])))
              r)) =
        SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false := by
  intro ss rv hSEval hREval pre suf hAppend
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq
            (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq
          (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [d])))
              r)) =
        SmtValue.RegLan (native_re_concat (native_str_to_re [d]) rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.str_to_re (SmtTerm.String [d])) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat (native_str_to_re [d]) rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re, hRTailEval,
     ]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  have hAppend' :
      pre ++ suf = [c] ++ native_unpack_string ss2 := by
    rw [native_unpack_string_pack_seq_concat_local] at hAppend
    simpa [native_unpack_string_pack_string] using hAppend
  exact native_str_in_re_str_to_re_concat_singleton_prefix_false_local c d
    (native_unpack_string ss2) rvTail hNe pre suf hAppend'

theorem str_re_consume_str_to_re_concat_no_prefix_of_tail_no_prefix_evals_local
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r : Term)
    (hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq SmtType.Char)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hTailNoPrefix :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s2) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              native_str_in_re pre rv = false) :
    ∀ ss rv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) =
        SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s1))
              r)) =
        SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false := by
  intro ss rv hSEval hREval pre suf hAppend
  have hS1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS1Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s1) (by
        unfold term_has_non_none_type
        rw [hS1Ty]
        simp)
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS1EvalTy with
    ⟨ss1, hS1Eval, hSs1Ty⟩
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hSs1Unpack :
      native_unpack_seq ss1 =
        impl_native_string_to_values (native_unpack_string ss1) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char (by
      have hsimpa := hSs1Ty; (try simp at hsimpa ⊢); exact hsimpa)
  have hS1Valid : native_string_valid (native_unpack_string ss1) = true :=
    native_unpack_string_valid_of_typeof_seq_char (by
      have hsimpa := hS1EvalTy; (try simp [hS1Eval] at hsimpa ⊢); exact hsimpa)
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
            (native_seq_concat (native_unpack_seq ss1)
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
          (native_seq_concat (native_unpack_seq ss1)
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS1Eval,
      hS2Eval]
  have hHeadEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s1)) =
        SmtValue.RegLan (native_str_to_re (native_unpack_string ss1)) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (__eo_to_smt s1)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss1))
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hS1Eval,
      hSs1Unpack]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s1))
              r)) =
        SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string ss1)) rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.str_to_re (__eo_to_smt s1)) (__eo_to_smt r)) =
      SmtValue.RegLan
        (native_re_concat (native_str_to_re (native_unpack_string ss1))
          rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re, hS1Eval, hRTailEval, hSs1Unpack]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  have hAppend' :
      pre ++ suf =
        native_unpack_string ss1 ++ native_unpack_string ss2 := by
    simpa [native_unpack_string_pack_seq_concat_local] using hAppend
  exact
    native_str_in_re_str_to_re_concat_prefix_false_of_tail_no_prefix_local
      (native_unpack_string ss1) (native_unpack_string ss2) rvTail
      (hTailNoPrefix ss2 rvTail hS2Eval hRTailEval) pre suf hAppend'

theorem str_re_consume_str_to_re_concat_residual_of_tail_residual_evals_local
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r side : Term)
    (hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq SmtType.Char)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hTailResidual :
      ∀ q ss rv ss' qv,
        __smtx_model_eval M (__eo_to_smt s2) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ss' ->
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (native_unpack_string ss)
              (native_re_concat rv qv) =
            native_str_in_re (native_unpack_string ss') qv) :
    ∀ q ss rv ss' qv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) =
        SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s1))
              r)) =
        SmtValue.RegLan rv ->
      __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
        SmtValue.Seq ss' ->
      __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
        native_str_in_re (native_unpack_string ss)
            (native_re_concat rv qv) =
          native_str_in_re (native_unpack_string ss') qv := by
  intro q ss rv ss' qv hSEval hREval hTailEval hQEval
  have hS1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS1Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s1) (by
        unfold term_has_non_none_type
        rw [hS1Ty]
        simp)
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS1EvalTy with
    ⟨ss1, hS1Eval, hSs1Ty⟩
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hSs1Unpack :
      native_unpack_seq ss1 =
        impl_native_string_to_values (native_unpack_string ss1) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char (by
      have hsimpa := hSs1Ty; (try simp at hsimpa ⊢); exact hsimpa)
  have hS1Valid : native_string_valid (native_unpack_string ss1) = true :=
    native_unpack_string_valid_of_typeof_seq_char (by
      have hsimpa := hS1EvalTy; (try simp [hS1Eval] at hsimpa ⊢); exact hsimpa)
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
            (native_seq_concat (native_unpack_seq ss1)
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
          (native_seq_concat (native_unpack_seq ss1)
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS1Eval,
      hS2Eval]
  have hHeadEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s1)) =
        SmtValue.RegLan (native_str_to_re (native_unpack_string ss1)) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (__eo_to_smt s1)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss1))
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hS1Eval,
      hSs1Unpack]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s1))
              r)) =
        SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string ss1)) rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.str_to_re (__eo_to_smt s1)) (__eo_to_smt r)) =
      SmtValue.RegLan
        (native_re_concat (native_str_to_re (native_unpack_string ss1))
          rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re, hS1Eval, hRTailEval, hSs1Unpack]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  rw [native_unpack_string_pack_seq_concat_local]
  rw [native_str_in_re_re_concat_assoc_consume_local]
  rw [native_str_in_re_str_to_re_concat_left_local
    (native_unpack_string ss1) (native_unpack_string ss2)
    (native_re_concat rvTail qv) hS1Valid]
  exact hTailResidual q ss2 rvTail ss' qv hS2Eval hRTailEval
    hTailEval hQEval

theorem str_re_consume_range_singleton_no_prefix_of_evals_local
    (M : SmtModel) (hM : model_wf M)
    (s2 r : Term) (c lo hi : native_Char)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hHead :
      native_str_in_re [c] (native_re_range [lo] [hi]) = false) :
    ∀ ss rv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range)
                    (Term.String [lo]))
                  (Term.String [hi])))
              r)) =
        SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false := by
  intro ss rv hSEval hREval pre suf hAppend
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq
            (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq
          (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range)
                    (Term.String [lo]))
                  (Term.String [hi])))
              r)) =
        SmtValue.RegLan
          (native_re_concat (native_re_range [lo] [hi]) rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.re_range (SmtTerm.String [lo]) (SmtTerm.String [hi]))
          (__eo_to_smt r)) =
      SmtValue.RegLan
        (native_re_concat (native_re_range [lo] [hi]) rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_re_range, hRTailEval,
     ]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  have hAppend' :
      pre ++ suf = [c] ++ native_unpack_string ss2 := by
    rw [native_unpack_string_pack_seq_concat_local] at hAppend
    simpa [native_unpack_string_pack_string] using hAppend
  exact native_str_in_re_re_range_concat_singleton_left_prefix_false_local c
    lo hi (native_unpack_string ss2) rvTail hHead pre suf hAppend'

theorem eo_list_concat_eq_rec_of_lists_local
    (a z : Term)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_list_concat_rec a z := by
  have hzNe : z ≠ Term.Stuck := by
    intro hz
    subst z
    simp [__eo_is_list] at hListZ
  have hRecNe :
      __eo_list_concat_rec a z ≠ Term.Stuck :=
    eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.str_concat)
      a z hListA hzNe
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) =
    __eo_list_concat_rec a z
  rw [hListA, hListZ]
  simp [eo_requires_self_eq_of_ne_stuck]

theorem smt_typeof_eo_list_concat_str_concat_of_seq_local
    (a z : Term) (T : SmtType)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
      SmtType.Seq T := by
  rw [eo_list_concat_eq_rec_of_lists_local a z hListA hListZ]
  exact smt_typeof_list_concat_rec_str_concat_of_seq a z T hListA haTy
    hzTy

theorem eo_is_list_eo_list_concat_str_concat_local
    (a z : Term)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__eo_list_concat (Term.UOp UserOp.str_concat) a z) =
      Term.Boolean true := by
  rw [eo_list_concat_eq_rec_of_lists_local a z hListA hListZ]
  exact eo_list_concat_rec_is_list_true_of_lists
    (Term.UOp UserOp.str_concat) a z hListA hListZ

theorem smt_value_rel_eo_list_concat_str_concat_local
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (T : SmtType)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat a z))) := by
  rw [eo_list_concat_eq_rec_of_lists_local a z hListA hListZ]
  exact smt_value_rel_list_concat_rec_str_concat M hM a z T
    hListA haTy hzTy

theorem str_nary_intro_is_list_true_of_seq_local
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
      Term.Boolean true := by
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
    rw [hIntroEq, hApplyEq]
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) x nil (by decide) hNilList
  · have hIntroEq : __str_nary_intro x = x :=
      str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
    rw [hIntroEq]
    simpa using hListBool

theorem str_nary_intro_ne_stuck_of_seq_type_local
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __str_nary_intro x ≠ Term.Stuck := by
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, rfl⟩
    have hNN :
        __smtx_typeof (__eo_to_smt (mkConcat head tail)) ≠
          SmtType.None := by
      rw [hxTy]
      exact seq_ne_none T
    exact RuleProofs.term_ne_stuck_of_has_smt_translation
      (__str_nary_intro (mkConcat head tail))
      (str_nary_intro_concat_has_smt_translation head tail hNN)
  · have hxNe : x ≠ Term.Stuck :=
      term_ne_stuck_of_smt_type_seq x T hxTy
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
    have hNilNe : nil ≠ Term.Stuck := by
      have hNilEq : nil = __seq_empty (__eo_typeof x) := by
        simpa [nil] using strConcat_nil_eq_seq_empty_of_type hTy
      simpa [hNilEq] using
        seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
    rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
        (by decide) hxNe with ⟨isList, hListBool⟩
    cases isList
    · have hIntroEq :
          __str_nary_intro x =
            __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              nil := by
        simp [__str_nary_intro, __eo_list_singleton_intro, nil,
          hListBool, eo_ite_false, hNilList, __eo_requires,
          native_teq, native_ite, SmtEval.native_ite,
          SmtEval.native_not]
      have hApplyNe :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              nil ≠ Term.Stuck := by
        cases hNilCases : nil <;>
          simp [__eo_mk_apply, hNilCases] at hNilNe ⊢
      simpa [hIntroEq] using hApplyNe
    · have hIntroEq : __str_nary_intro x = x :=
        str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
      simpa [hIntroEq] using hxNe

theorem smt_typeof_str_nary_intro_seq_char_local
    (x : Term)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Seq SmtType.Char)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) =
      SmtType.Seq SmtType.Char := by
  have hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None :=
    seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x
      SmtType.Char hxTy type_inhabited_char (by
        simp [__smtx_type_wf, __smtx_type_wf_rec,
          __smtx_type_wf_component,
          native_inhabited_type_char, native_and])
  exact smt_typeof_str_nary_intro_of_seq_empty_typeof x SmtType.Char
    hxTy hEmptyNN hIntro

theorem str_list_concat_singleton_intro_eval_rel_local
    (M : SmtModel) (hM : model_wf M)
    (acc s : Term)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc =
        Term.Boolean true)
    (hAccTy :
      __smtx_typeof (__eo_to_smt acc) =
        SmtType.Seq SmtType.Char)
    (hSTy :
      __smtx_typeof (__eo_to_smt s) =
        SmtType.Seq SmtType.Char)
    (hIntro : __str_nary_intro s ≠ Term.Stuck) :
    ∃ outSs,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) acc
              (__str_nary_intro s))) =
        SmtValue.Seq outSs ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) acc
              (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_concat (Term.UOp UserOp.str_concat) acc
            (__str_nary_intro s)) =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel (SmtValue.Seq outSs)
        (__smtx_model_eval M (__eo_to_smt (mkConcat acc s))) := by
  have hIntroList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    str_nary_intro_is_list_true_of_seq_local s SmtType.Char hSTy hIntro
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_nary_intro_seq_char_local s hSTy hIntro
  have hConcatTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) acc
              (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_eo_list_concat_str_concat_of_seq_local acc
      (__str_nary_intro s) SmtType.Char hAccList hIntroList hAccTy
      hIntroTy
  have hConcatEvalTy :
      __smtx_typeof_value
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_list_concat (Term.UOp UserOp.str_concat) acc
                (__str_nary_intro s)))) =
        SmtType.Seq SmtType.Char := by
    simpa [hConcatTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt
          (__eo_list_concat (Term.UOp UserOp.str_concat) acc
            (__str_nary_intro s))) (by
          unfold term_has_non_none_type
          rw [hConcatTy]
          simp)
  rcases seq_value_canonical_with_char_type hConcatEvalTy with
    ⟨outSs, hOutEval, hOutSsTy⟩
  have hListConcatRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) acc
              (__str_nary_intro s))))
        (__smtx_model_eval M (__eo_to_smt (mkConcat acc
          (__str_nary_intro s)))) :=
    smt_value_rel_eo_list_concat_str_concat_local M hM acc
      (__str_nary_intro s) SmtType.Char hAccList hIntroList hAccTy
      hIntroTy
  have hIntroRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro s)))
        (__smtx_model_eval M (__eo_to_smt s)) :=
    smt_value_rel_str_nary_intro M hM s SmtType.Char hSTy hIntro
  have hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkConcat acc
          (__str_nary_intro s))))
        (__smtx_model_eval M (__eo_to_smt (mkConcat acc s))) :=
    smt_value_rel_str_concat_right_congr M hM acc (__str_nary_intro s)
      s SmtType.Char hAccTy hIntroTy hSTy hIntroRel
  have hRel :
      RuleProofs.smt_value_rel (SmtValue.Seq outSs)
        (__smtx_model_eval M (__eo_to_smt (mkConcat acc s))) := by
    have hTrans := RuleProofs.smt_value_rel_trans _ _ _
      hListConcatRel hRightRel
    simpa [hOutEval] using hTrans
  exact ⟨outSs, hOutEval, hConcatTy,
    eo_is_list_eo_list_concat_str_concat_local acc (__str_nary_intro s)
      hAccList hIntroList,
    hRel⟩

theorem str_list_concat_singleton_intro_str_to_re_rel_local
    (M : SmtModel) (hM : model_wf M)
    (acc s : Term) (accSs ss : SmtSeq)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc =
        Term.Boolean true)
    (hAccTy :
      __smtx_typeof (__eo_to_smt acc) =
        SmtType.Seq SmtType.Char)
    (hAccEval :
      __smtx_model_eval M (__eo_to_smt acc) =
        SmtValue.Seq accSs)
    (hSTy :
      __smtx_typeof (__eo_to_smt s) =
        SmtType.Seq SmtType.Char)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt s) =
        SmtValue.Seq ss)
    (hIntro : __str_nary_intro s ≠ Term.Stuck) :
    ∃ outSs,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) acc
              (__str_nary_intro s))) =
        SmtValue.Seq outSs ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) acc
              (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_concat (Term.UOp UserOp.str_concat) acc
            (__str_nary_intro s)) =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string outSs)))
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs))
            (native_str_to_re (native_unpack_string ss)))) := by
  rcases str_list_concat_singleton_intro_eval_rel_local M hM acc s
      hAccList hAccTy hSTy hIntro with
    ⟨outSs, hOutEval, hOutTy, hOutList, hOutRel⟩
  let packed :=
    native_pack_seq (__smtx_elem_typeof_seq_value accSs)
      (native_seq_concat (native_unpack_seq accSs)
        (native_unpack_seq ss))
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt (mkConcat acc s)) =
        SmtValue.Seq packed := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt acc) (__eo_to_smt s)) =
      SmtValue.Seq packed
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hAccEval,
      hSEval, packed]
  have hSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq outSs)
        (SmtValue.Seq packed) := by
    rw [hConcatEval] at hOutRel
    exact hOutRel
  have hOutStrRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string outSs)))
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string packed))) :=
    smt_value_rel_str_to_re_of_seq_rel_consume_local hSeqRel
  have hPackedUnpack :
      native_unpack_string packed =
        native_unpack_string accSs ++ native_unpack_string ss := by
    simpa [packed] using
      native_unpack_string_pack_seq_concat_local
        (__smtx_elem_typeof_seq_value accSs) accSs ss
  have hOutAppendRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string outSs)))
        (SmtValue.RegLan
          (native_str_to_re
            (native_unpack_string accSs ++ native_unpack_string ss))) := by
    simpa [hPackedUnpack, impl_native_string_to_values, List.map_append] using
      hOutStrRel
  have hConcatAppendRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs))
            (native_str_to_re (native_unpack_string ss))))
        (SmtValue.RegLan
          (native_str_to_re
            (native_unpack_string accSs ++ native_unpack_string ss))) :=
    smt_value_rel_str_to_re_append_consume_local
      (native_unpack_string accSs) (native_unpack_string ss)
  have hAppendConcatRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_str_to_re
            (native_unpack_string accSs ++ native_unpack_string ss)))
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs))
            (native_str_to_re (native_unpack_string ss)))) :=
    RuleProofs.smt_value_rel_symm _ _ hConcatAppendRel
  exact ⟨outSs, hOutEval, hOutTy, hOutList,
    RuleProofs.smt_value_rel_trans _ _ _ hOutAppendRel
      hAppendConcatRel⟩

theorem str_nary_intro_str_to_re_rel_local
    (M : SmtModel) (hM : model_wf M)
    (s : Term) (ss : SmtSeq)
    (hSTy :
      __smtx_typeof (__eo_to_smt s) =
        SmtType.Seq SmtType.Char)
    (hSEval :
      __smtx_model_eval M (__eo_to_smt s) =
        SmtValue.Seq ss)
    (hIntro : __str_nary_intro s ≠ Term.Stuck) :
    ∃ introSs,
      __smtx_model_eval M (__eo_to_smt (__str_nary_intro s)) =
        SmtValue.Seq introSs ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) =
        SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string introSs)))
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string ss))) := by
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_nary_intro_seq_char_local s hSTy hIntro
  have hIntroEvalTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char := by
    simpa [hIntroTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt (__str_nary_intro s)) (by
          unfold term_has_non_none_type
          rw [hIntroTy]
          simp)
  rcases seq_value_canonical_with_char_type hIntroEvalTy with
    ⟨introSs, hIntroEval, hIntroSsTy⟩
  have hIntroSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq introSs)
        (SmtValue.Seq ss) := by
    have hRel :=
      smt_value_rel_str_nary_intro M hM s SmtType.Char hSTy hIntro
    simpa [hIntroEval, hSEval] using hRel
  exact ⟨introSs, hIntroEval, hIntroTy,
    str_nary_intro_is_list_true_of_seq_local s SmtType.Char hSTy hIntro,
    smt_value_rel_str_to_re_of_seq_rel_consume_local hIntroSeqRel⟩

theorem re_unflatten_false_re_mult_eval_rel_step_local
    (M : SmtModel) (hM : model_wf M)
    (body : Term) (rv flatRv : SmtRegLan)
    (hBodyEval :
      __smtx_model_eval M (__eo_to_smt body) =
        SmtValue.RegLan rv)
    (hUnflatTy :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              body)) =
        SmtType.RegLan)
    (hUnflatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              body)) =
        SmtValue.RegLan flatRv)
    (hUnflatList :
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true) body) =
        Term.Boolean true)
    (hUnflatRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRv)
        (SmtValue.RegLan rv)) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              (Term.Apply (Term.UOp UserOp.re_mult) body))) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              (Term.Apply (Term.UOp UserOp.re_mult) body))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan (native_re_mult rv)) := by
  let unflatBody :=
    __re_unflatten (Term.Boolean true) body
  let elimBody :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat) unflatBody
  have hElimTy :
      __smtx_typeof (__eo_to_smt elimBody) = SmtType.RegLan := by
    simpa [elimBody, unflatBody] using
      RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type
        unflatBody (by simpa [unflatBody] using hUnflatList)
        (by simpa [unflatBody] using hUnflatTy)
  rcases reConcat_singleton_elim_eval_rel_consume_local M unflatBody flatRv
      (by simpa [unflatBody] using hUnflatList)
      (by simpa [unflatBody] using hUnflatEval) with
    ⟨elimRv, hElimEval, hElimRel⟩
  have hElimBodyRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan elimRv)
        (SmtValue.RegLan rv) :=
    RuleProofs.smt_value_rel_trans _ _ _ hElimRel hUnflatRel
  have hElimNe : elimBody ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation elimBody (by
      unfold RuleProofs.eo_has_smt_translation
      rw [hElimTy]
      simp)
  have hMkNe :
      __eo_mk_apply (Term.UOp UserOp.re_mult) elimBody ≠ Term.Stuck := by
    cases hElim : elimBody <;>
      simp [hElim, __eo_mk_apply] at hElimNe ⊢
  have hMkEq :
      __eo_mk_apply (Term.UOp UserOp.re_mult) elimBody =
        Term.Apply (Term.UOp UserOp.re_mult) elimBody :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.re_mult)
      elimBody hMkNe
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) elimBody)) =
        SmtValue.RegLan (native_re_mult elimRv) :=
    eval_re_mult_reglan_consume_local M elimBody elimRv
      (by simpa [elimBody] using hElimEval)
  have hFullTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) elimBody)) =
        SmtType.RegLan :=
    smt_typeof_re_mult_of_reglan_consume_local elimBody hElimTy
  have hFullRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan (native_re_mult elimRv))
        (SmtValue.RegLan (native_re_mult rv)) :=
    smt_value_rel_re_mult_consume_local hElimBodyRel
  refine ⟨native_re_mult elimRv, ?_, ?_, hFullRel⟩
  · simpa [__re_unflatten, unflatBody, elimBody, eo_ite_false, hMkEq]
      using hFullEval
  · simpa [__re_unflatten, unflatBody, elimBody, eo_ite_false, hMkEq]
      using hFullTy

theorem re_unflatten_false_re_inter_eval_rel_step_local
    (M : SmtModel) (hM : model_wf M)
    (c1 c2 : Term) (rv1 rv2 flatRv1 flatRv2 : SmtRegLan)
    (hC1Eval :
      __smtx_model_eval M (__eo_to_smt c1) =
        SmtValue.RegLan rv1)
    (hC2Eval :
      __smtx_model_eval M (__eo_to_smt c2) =
        SmtValue.RegLan rv2)
    (hUnflatC1Ty :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              c1)) =
        SmtType.RegLan)
    (hUnflatC1Eval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              c1)) =
        SmtValue.RegLan flatRv1)
    (hUnflatC1List :
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true) c1) =
        Term.Boolean true)
    (hUnflatC1Rel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRv1)
        (SmtValue.RegLan rv1))
    (hUnflatC2Ty :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              c2)) =
        SmtType.RegLan)
    (hUnflatC2Eval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              c2)) =
        SmtValue.RegLan flatRv2)
    (hUnflatC2Rel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRv2)
        (SmtValue.RegLan rv2)) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) c1) c2))) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) c1) c2))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan (native_re_inter rv1 rv2)) := by
  let unflatC1 :=
    __re_unflatten (Term.Boolean true) c1
  let elimC1 :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat) unflatC1
  let unflatC2 :=
    __re_unflatten (Term.Boolean false) c2
  have hElimTy :
      __smtx_typeof (__eo_to_smt elimC1) = SmtType.RegLan := by
    simpa [elimC1, unflatC1] using
      RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type
        unflatC1 (by simpa [unflatC1] using hUnflatC1List)
        (by simpa [unflatC1] using hUnflatC1Ty)
  rcases reConcat_singleton_elim_eval_rel_consume_local M unflatC1
      flatRv1 (by simpa [unflatC1] using hUnflatC1List)
      (by simpa [unflatC1] using hUnflatC1Eval) with
    ⟨elimRv1, hElimEval, hElimRel⟩
  have hElimRelC1 :
      RuleProofs.smt_value_rel (SmtValue.RegLan elimRv1)
        (SmtValue.RegLan rv1) :=
    RuleProofs.smt_value_rel_trans _ _ _ hElimRel hUnflatC1Rel
  have hElimNe : elimC1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation elimC1 (by
      unfold RuleProofs.eo_has_smt_translation
      rw [hElimTy]
      simp)
  have hUnflatC2Ne : unflatC2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation unflatC2 (by
      unfold RuleProofs.eo_has_smt_translation
      rw [show __smtx_typeof (__eo_to_smt unflatC2) = SmtType.RegLan by
        simpa [unflatC2] using hUnflatC2Ty]
      simp)
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.re_inter) elimC1 ≠ Term.Stuck := by
    cases hElim : elimC1 <;>
      simp [hElim, __eo_mk_apply] at hElimNe ⊢
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.re_inter) elimC1 =
        Term.Apply (Term.UOp UserOp.re_inter) elimC1 :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.re_inter)
      elimC1 hInnerNe
  have hOuterNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_inter) elimC1)
          unflatC2 ≠ Term.Stuck := by
    cases hC2 : unflatC2 <;>
      simp [hC2, __eo_mk_apply] at hUnflatC2Ne ⊢
  have hOuterEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_inter) elimC1)
          unflatC2 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_inter) elimC1) unflatC2 :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.re_inter) elimC1) unflatC2
      hOuterNe
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) elimC1) unflatC2)) =
        SmtValue.RegLan (native_re_inter elimRv1 flatRv2) :=
    eval_re_inter_reglan_consume_local M elimC1 unflatC2 elimRv1
      flatRv2 (by simpa [elimC1] using hElimEval)
      (by simpa [unflatC2] using hUnflatC2Eval)
  have hFullTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) elimC1) unflatC2)) =
        SmtType.RegLan :=
    smt_typeof_re_inter_of_reglan_consume_local elimC1 unflatC2
      hElimTy (by simpa [unflatC2] using hUnflatC2Ty)
  have hFullRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan (native_re_inter elimRv1 flatRv2))
        (SmtValue.RegLan (native_re_inter rv1 rv2)) :=
    smt_value_rel_re_inter_consume_local hElimRelC1 hUnflatC2Rel
  refine ⟨native_re_inter elimRv1 flatRv2, ?_, ?_, hFullRel⟩
  · simpa [__re_unflatten, unflatC1, elimC1, unflatC2,
      eo_ite_false, hInnerEq, hOuterEq] using hFullEval
  · simpa [__re_unflatten, unflatC1, elimC1, unflatC2,
      eo_ite_false, hInnerEq, hOuterEq] using hFullTy

theorem re_unflatten_false_re_union_eval_rel_step_local
    (M : SmtModel) (hM : model_wf M)
    (c1 c2 : Term) (rv1 rv2 flatRv1 flatRv2 : SmtRegLan)
    (hC1Eval :
      __smtx_model_eval M (__eo_to_smt c1) =
        SmtValue.RegLan rv1)
    (hC2Eval :
      __smtx_model_eval M (__eo_to_smt c2) =
        SmtValue.RegLan rv2)
    (hUnflatC1Ty :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              c1)) =
        SmtType.RegLan)
    (hUnflatC1Eval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              c1)) =
        SmtValue.RegLan flatRv1)
    (hUnflatC1List :
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true) c1) =
        Term.Boolean true)
    (hUnflatC1Rel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRv1)
        (SmtValue.RegLan rv1))
    (hUnflatC2Ty :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              c2)) =
        SmtType.RegLan)
    (hUnflatC2Eval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              c2)) =
        SmtValue.RegLan flatRv2)
    (hUnflatC2Rel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRv2)
        (SmtValue.RegLan rv2)) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) c1) c2))) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) c1) c2))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan (native_re_union rv1 rv2)) := by
  let unflatC1 :=
    __re_unflatten (Term.Boolean true) c1
  let elimC1 :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat) unflatC1
  let unflatC2 :=
    __re_unflatten (Term.Boolean false) c2
  have hElimTy :
      __smtx_typeof (__eo_to_smt elimC1) = SmtType.RegLan := by
    simpa [elimC1, unflatC1] using
      RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type
        unflatC1 (by simpa [unflatC1] using hUnflatC1List)
        (by simpa [unflatC1] using hUnflatC1Ty)
  rcases reConcat_singleton_elim_eval_rel_consume_local M unflatC1
      flatRv1 (by simpa [unflatC1] using hUnflatC1List)
      (by simpa [unflatC1] using hUnflatC1Eval) with
    ⟨elimRv1, hElimEval, hElimRel⟩
  have hElimRelC1 :
      RuleProofs.smt_value_rel (SmtValue.RegLan elimRv1)
        (SmtValue.RegLan rv1) :=
    RuleProofs.smt_value_rel_trans _ _ _ hElimRel hUnflatC1Rel
  have hElimNe : elimC1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation elimC1 (by
      unfold RuleProofs.eo_has_smt_translation
      rw [hElimTy]
      simp)
  have hUnflatC2Ne : unflatC2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation unflatC2 (by
      unfold RuleProofs.eo_has_smt_translation
      rw [show __smtx_typeof (__eo_to_smt unflatC2) = SmtType.RegLan by
        simpa [unflatC2] using hUnflatC2Ty]
      simp)
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.re_union) elimC1 ≠ Term.Stuck := by
    cases hElim : elimC1 <;>
      simp [hElim, __eo_mk_apply] at hElimNe ⊢
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.re_union) elimC1 =
        Term.Apply (Term.UOp UserOp.re_union) elimC1 :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.re_union)
      elimC1 hInnerNe
  have hOuterNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_union) elimC1)
          unflatC2 ≠ Term.Stuck := by
    cases hC2 : unflatC2 <;>
      simp [hC2, __eo_mk_apply] at hUnflatC2Ne ⊢
  have hOuterEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_union) elimC1)
          unflatC2 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_union) elimC1) unflatC2 :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.re_union) elimC1) unflatC2
      hOuterNe
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) elimC1) unflatC2)) =
        SmtValue.RegLan (native_re_union elimRv1 flatRv2) :=
    eval_re_union_reglan_consume_local M elimC1 unflatC2 elimRv1
      flatRv2 (by simpa [elimC1] using hElimEval)
      (by simpa [unflatC2] using hUnflatC2Eval)
  have hFullTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) elimC1) unflatC2)) =
        SmtType.RegLan :=
    smt_typeof_re_union_of_reglan_consume_local elimC1 unflatC2
      hElimTy (by simpa [unflatC2] using hUnflatC2Ty)
  have hFullRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan (native_re_union elimRv1 flatRv2))
        (SmtValue.RegLan (native_re_union rv1 rv2)) :=
    smt_value_rel_re_union_consume_local hElimRelC1 hUnflatC2Rel
  refine ⟨native_re_union elimRv1 flatRv2, ?_, ?_, hFullRel⟩
  · simpa [__re_unflatten, unflatC1, elimC1, unflatC2,
      eo_ite_false, hInnerEq, hOuterEq] using hFullEval
  · simpa [__re_unflatten, unflatC1, elimC1, unflatC2,
      eo_ite_false, hInnerEq, hOuterEq] using hFullTy

theorem re_unflatten_str_false_str_to_re_eval_rel_step_local
    (M : SmtModel)
    (acc s b : Term) (accSs ss newSs : SmtSeq)
    (rb recRv : SmtRegLan)
    (hAccNe : acc ≠ Term.Stuck)
    (hNewAccEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) acc
              (__str_nary_intro s))) =
        SmtValue.Seq newSs)
    (hNewAccTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) acc
              (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char)
    (hNewAccList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_concat (Term.UOp UserOp.str_concat) acc
            (__str_nary_intro s)) =
        Term.Boolean true)
    (hNewAccStrRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string newSs)))
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs))
            (native_str_to_re (native_unpack_string ss)))))
    (hRecEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten_str
              (__eo_list_concat (Term.UOp UserOp.str_concat) acc
                (__str_nary_intro s)) b)) =
        SmtValue.RegLan recRv)
    (hRecTy :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten_str
              (__eo_list_concat (Term.UOp UserOp.str_concat) acc
                (__str_nary_intro s)) b)) =
        SmtType.RegLan)
    (hRecRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan recRv)
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string newSs)) rb))) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten_str acc
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s)) b))) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten_str acc
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s)) b))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs))
            (native_re_concat
              (native_str_to_re (native_unpack_string ss)) rb))) := by
  have hTailCongr :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string newSs)) rb))
        (SmtValue.RegLan
          (native_re_concat
            (native_re_concat
              (native_str_to_re (native_unpack_string accSs))
              (native_str_to_re (native_unpack_string ss))) rb)) :=
    smt_value_rel_re_concat_consume_local hNewAccStrRel
      (RuleProofs.smt_value_rel_refl (SmtValue.RegLan rb))
  have hAssoc :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_re_concat
            (native_re_concat
              (native_str_to_re (native_unpack_string accSs))
              (native_str_to_re (native_unpack_string ss))) rb))
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs))
            (native_re_concat
              (native_str_to_re (native_unpack_string ss)) rb))) :=
    smt_value_rel_re_concat_assoc_consume_local
      (native_str_to_re (native_unpack_string accSs))
      (native_str_to_re (native_unpack_string ss)) rb
  have hRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan recRv)
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs))
            (native_re_concat
              (native_str_to_re (native_unpack_string ss)) rb))) :=
    RuleProofs.smt_value_rel_trans _ _ _
      (RuleProofs.smt_value_rel_trans _ _ _ hRecRel hTailCongr)
      hAssoc
  have hUnfold :
      __re_unflatten_str acc
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) b) =
        __re_unflatten_str
          (__eo_list_concat (Term.UOp UserOp.str_concat) acc
            (__str_nary_intro s)) b := by
    simpa [__str_nary_intro] using
      __re_unflatten_str.eq_3 acc s b hAccNe
  exact ⟨recRv,
    by
      rw [hUnfold]
      exact hRecEval,
    by
      rw [hUnfold]
      exact hRecTy,
    hRel⟩

theorem re_unflatten_str_false_default_eval_rel_step_local
    (M : SmtModel) (hM : model_wf M)
    (acc b : Term) (accSs : SmtSeq) (rb rb' : SmtRegLan)
    (hAccNe : acc ≠ Term.Stuck)
    (hBNe : b ≠ Term.Stuck)
    (hNotStrPrefix :
      ∀ (s tail : Term),
        b =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc =
        Term.Boolean true)
    (hAccTy :
      __smtx_typeof (__eo_to_smt acc) =
        SmtType.Seq SmtType.Char)
    (hAccEval :
      __smtx_model_eval M (__eo_to_smt acc) =
        SmtValue.Seq accSs)
    (hUnflatBTy :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              b)) =
        SmtType.RegLan)
    (hUnflatBEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              b)) =
        SmtValue.RegLan rb')
    (hUnflatBRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rb')
        (SmtValue.RegLan rb))
    (hCollect : __str_collect acc ≠ Term.Stuck) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten_str acc b)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten_str acc b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs)) rb)) := by
  let collectedString :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
      (__str_collect acc)
  let headRe := Term.Apply (Term.UOp UserOp.str_to_re) collectedString
  let unflatB :=
    __re_unflatten (Term.Boolean true) b
  have hCollectedTy :
      __smtx_typeof (__eo_to_smt collectedString) =
        SmtType.Seq SmtType.Char := by
    simpa [collectedString] using
      str_collect_singleton_elim_type_local acc SmtType.Char hAccList
        hAccTy hCollect
  have hCollectedNe : collectedString ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation collectedString (by
      unfold RuleProofs.eo_has_smt_translation
      rw [hCollectedTy]
      simp)
  have hHeadMkNe :
      __eo_mk_apply (Term.UOp UserOp.str_to_re) collectedString ≠
        Term.Stuck := by
    cases hCollected : collectedString <;>
      simp [hCollected, __eo_mk_apply] at hCollectedNe ⊢
  have hHeadMkEq :
      __eo_mk_apply (Term.UOp UserOp.str_to_re) collectedString =
        headRe :=
    by
      simpa [headRe] using
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.UOp UserOp.str_to_re) collectedString hHeadMkNe
  have hHeadTy :
      __smtx_typeof (__eo_to_smt headRe) = SmtType.RegLan := by
    simpa [headRe] using
      smt_typeof_str_to_re_of_seq_consume_local collectedString
        hCollectedTy
  have hHeadNe : headRe ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation headRe (by
      unfold RuleProofs.eo_has_smt_translation
      rw [hHeadTy]
      simp)
  have hInnerMkNe :
      __eo_mk_apply (Term.UOp UserOp.re_concat) headRe ≠ Term.Stuck := by
    cases hHead : headRe <;>
      simp [hHead, __eo_mk_apply] at hHeadNe ⊢
  have hInnerMkEq :
      __eo_mk_apply (Term.UOp UserOp.re_concat) headRe =
        Term.Apply (Term.UOp UserOp.re_concat) headRe :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.re_concat)
      headRe hInnerMkNe
  have hUnflatBNe : unflatB ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation unflatB (by
      unfold RuleProofs.eo_has_smt_translation
      rw [show __smtx_typeof (__eo_to_smt unflatB) = SmtType.RegLan by
        simpa [unflatB] using hUnflatBTy]
      simp)
  have hOuterMkNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_concat) headRe)
          unflatB ≠ Term.Stuck := by
    cases hUnflat : unflatB <;>
      simp [hUnflat, __eo_mk_apply] at hUnflatBNe ⊢
  have hOuterMkEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_concat) headRe)
          unflatB =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) headRe)
          unflatB :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.re_concat) headRe) unflatB
      hOuterMkNe
  have hUnfold :
      __re_unflatten_str acc b =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) headRe)
          unflatB := by
    simpa [collectedString, headRe, unflatB, eo_ite_false, hHeadMkEq,
      hInnerMkEq, hOuterMkEq] using
      __re_unflatten_str.eq_4 acc b hAccNe hBNe hNotStrPrefix
  rcases re_unflatten_str_finish_eval_rel_local M hM acc unflatB accSs
      rb rb' hAccList hAccTy hAccEval
      (by simpa [unflatB] using hUnflatBTy)
      (by simpa [unflatB] using hUnflatBEval)
      hUnflatBRel hCollect with
    ⟨outRv, hFinishEval, hFinishTy, hFinishRel⟩
  exact ⟨outRv,
    by
      rw [hUnfold]
      simpa [headRe, collectedString, unflatB] using hFinishEval,
    by
      rw [hUnfold]
      simpa [headRe, collectedString, unflatB] using hFinishTy,
    hFinishRel⟩

theorem re_unflatten_false_true_re_concat_eval_rel_step_local
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) (ra rb flatRa flatRb : SmtRegLan)
    (hANotStrToRe :
      ∀ s : Term,
        a = Term.Apply (Term.UOp UserOp.str_to_re) s -> False)
    (hUnflatATy :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              a)) =
        SmtType.RegLan)
    (hUnflatAEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false)
              a)) =
        SmtValue.RegLan flatRa)
    (hUnflatARel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRa)
        (SmtValue.RegLan ra))
    (hUnflatBTy :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              b)) =
        SmtType.RegLan)
    (hUnflatBEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              b)) =
        SmtValue.RegLan flatRb)
    (hUnflatBRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRb)
        (SmtValue.RegLan rb)) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat) a) b))) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat) a) b))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan (native_re_concat ra rb)) := by
  let unflatA :=
    __re_unflatten (Term.Boolean false) a
  let unflatB :=
    __re_unflatten (Term.Boolean true) b
  have hUnflatANe : unflatA ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation unflatA (by
      unfold RuleProofs.eo_has_smt_translation
      rw [show __smtx_typeof (__eo_to_smt unflatA) = SmtType.RegLan by
        simpa [unflatA] using hUnflatATy]
      simp)
  have hUnflatBNe : unflatB ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation unflatB (by
      unfold RuleProofs.eo_has_smt_translation
      rw [show __smtx_typeof (__eo_to_smt unflatB) = SmtType.RegLan by
        simpa [unflatB] using hUnflatBTy]
      simp)
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.re_concat) unflatA ≠
        Term.Stuck := by
    cases hA : unflatA <;>
      simp [hA, __eo_mk_apply] at hUnflatANe ⊢
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.re_concat) unflatA =
        Term.Apply (Term.UOp UserOp.re_concat) unflatA :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.re_concat)
      unflatA hInnerNe
  have hOuterNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_concat) unflatA)
          unflatB ≠ Term.Stuck := by
    cases hB : unflatB <;>
      simp [hB, __eo_mk_apply] at hUnflatBNe ⊢
  have hOuterEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_concat) unflatA)
          unflatB =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) unflatA)
          unflatB :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.re_concat) unflatA) unflatB
      hOuterNe
  have hUnfold :
      __re_unflatten (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) =
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) unflatA)
          unflatB := by
    simpa [unflatA, unflatB, hInnerEq, hOuterEq] using
      __re_unflatten.eq_3 a b hANotStrToRe
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) unflatA)
              unflatB)) =
        SmtValue.RegLan (native_re_concat flatRa flatRb) :=
    eval_re_concat_reglan_consume_local M unflatA unflatB flatRa
      flatRb (by simpa [unflatA] using hUnflatAEval)
      (by simpa [unflatB] using hUnflatBEval)
  have hFullTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) unflatA)
              unflatB)) =
        SmtType.RegLan :=
    smt_typeof_re_concat_of_reglan_consume_local unflatA unflatB
      (by simpa [unflatA] using hUnflatATy)
      (by simpa [unflatB] using hUnflatBTy)
  have hFullRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan (native_re_concat flatRa flatRb))
        (SmtValue.RegLan (native_re_concat ra rb)) :=
    smt_value_rel_re_concat_consume_local hUnflatARel hUnflatBRel
  exact ⟨native_re_concat flatRa flatRb,
    by
      rw [hUnfold]
      exact hFullEval,
    by
      rw [hUnfold]
      exact hFullTy,
    hFullRel⟩

theorem re_unflatten_false_true_str_to_re_eval_rel_step_local
    (M : SmtModel)
    (s b : Term) (ss introSs : SmtSeq) (rb outRv : SmtRegLan)
    (hIntroStrRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string introSs)))
        (SmtValue.RegLan
          (native_str_to_re (native_unpack_string ss))))
    (hStrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten_str
              (__str_nary_intro s) b)) =
        SmtValue.RegLan outRv)
    (hStrTy :
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten_str
              (__str_nary_intro s) b)) =
        SmtType.RegLan)
    (hStrRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string introSs)) rb))) :
    ∃ outRv',
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s)) b))) =
        SmtValue.RegLan outRv' ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s)) b))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv')
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string ss)) rb)) := by
  have hUnfold :
      __re_unflatten (Term.Boolean true)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) b) =
        __re_unflatten_str (__str_nary_intro s) b := by
    simpa [__str_nary_intro] using
      __re_unflatten.eq_2 s b
  have hTailRel :
      RuleProofs.smt_value_rel
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string introSs)) rb))
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string ss)) rb)) :=
    smt_value_rel_re_concat_consume_local hIntroStrRel
      (RuleProofs.smt_value_rel_refl (SmtValue.RegLan rb))
  exact ⟨outRv,
    by rw [hUnfold]; exact hStrEval,
    by rw [hUnfold]; exact hStrTy,
    RuleProofs.smt_value_rel_trans _ _ _ hStrRel hTailRel⟩

theorem re_unflatten_false_true_default_eval_rel_step_local
    (M : SmtModel) (r : Term) (rv : SmtRegLan)
    (hRNe : r ≠ Term.Stuck)
    (hNotStrPrefix :
      ∀ (s tail : Term),
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False)
    (hNotConcat :
      ∀ (a b : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
        False)
    (hRTy :
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval :
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true) r)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true) r)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan rv) := by
  have hUnfold :
      __re_unflatten (Term.Boolean true) r = r :=
    __re_unflatten.eq_4 r hRNe
      hNotStrPrefix hNotConcat
  exact ⟨rv, by rw [hUnfold]; exact hREval,
    by rw [hUnfold]; exact hRTy,
    RuleProofs.smt_value_rel_refl _⟩

theorem re_unflatten_false_false_default_eval_rel_step_local
    (M : SmtModel) (r : Term) (rv : SmtRegLan)
    (hRNe : r ≠ Term.Stuck)
    (hNotMult :
      ∀ body : Term,
        r = Term.Apply (Term.UOp UserOp.re_mult) body -> False)
    (hNotInter :
      ∀ (c1 c2 : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
        False)
    (hNotUnion :
      ∀ (c1 c2 : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
        False)
    (hRTy :
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval :
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false) r)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false) r)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan rv) := by
  have hUnfold :
      __re_unflatten (Term.Boolean false) r = r :=
    __re_unflatten.eq_8 r hRNe
      hNotMult hNotInter hNotUnion
  exact ⟨rv, by rw [hUnfold]; exact hREval,
    by rw [hUnfold]; exact hRTy,
    RuleProofs.smt_value_rel_refl _⟩

theorem re_unflatten_false_re_mult_child_list_of_ne_stuck_local
    (body : Term)
    (hNe :
      __re_unflatten (Term.Boolean false)
          (Term.Apply (Term.UOp UserOp.re_mult) body) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true) body) =
      Term.Boolean true := by
  have hEq :=
    __re_unflatten.eq_5 body
  rw [hEq] at hNe
  have hArgNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true) body) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hNe
  exact
    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_list_of_ne_stuck
      (__re_unflatten (Term.Boolean true) body)
      hArgNe

theorem re_unflatten_false_re_inter_child_list_of_ne_stuck_local
    (c1 c2 : Term)
    (hNe :
      __re_unflatten (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true) c1) =
      Term.Boolean true := by
  have hEq :=
    __re_unflatten.eq_6 c1 c2
  rw [hEq] at hNe
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.re_inter)
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true) c1)) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hNe
  have hArgNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true) c1) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
  exact
    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_list_of_ne_stuck
      (__re_unflatten (Term.Boolean true) c1)
      hArgNe

theorem re_unflatten_false_re_inter_right_ne_stuck_of_ne_stuck_local
    (c1 c2 : Term)
    (hNe :
      __re_unflatten (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) ≠
        Term.Stuck) :
    __re_unflatten (Term.Boolean false) c2 ≠
      Term.Stuck := by
  have hEq :=
    __re_unflatten.eq_6 c1 c2
  rw [hEq] at hNe
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hNe

theorem re_unflatten_false_re_union_child_list_of_ne_stuck_local
    (c1 c2 : Term)
    (hNe :
      __re_unflatten (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true) c1) =
      Term.Boolean true := by
  have hEq :=
    __re_unflatten.eq_7 c1 c2
  rw [hEq] at hNe
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.re_union)
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true) c1)) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hNe
  have hArgNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true) c1) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
  exact
    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_list_of_ne_stuck
      (__re_unflatten (Term.Boolean true) c1)
      hArgNe

theorem re_unflatten_false_re_union_right_ne_stuck_of_ne_stuck_local
    (c1 c2 : Term)
    (hNe :
      __re_unflatten (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) ≠
        Term.Stuck) :
    __re_unflatten (Term.Boolean false) c2 ≠
      Term.Stuck := by
  have hEq :=
    __re_unflatten.eq_7 c1 c2
  rw [hEq] at hNe
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hNe

theorem re_unflatten_false_true_str_to_re_child_ne_stuck_local
    (s b : Term)
    (hNe :
      __re_unflatten (Term.Boolean true)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) b) ≠
        Term.Stuck) :
    __re_unflatten_str (__str_nary_intro s) b ≠
      Term.Stuck := by
  have hEq :=
    __re_unflatten.eq_2 s b
  rw [hEq] at hNe
  simpa [__str_nary_intro] using hNe

theorem re_unflatten_false_true_re_concat_children_ne_stuck_local
    (a b : Term)
    (hANotStrToRe :
      ∀ s : Term,
        a = Term.Apply (Term.UOp UserOp.str_to_re) s -> False)
    (hNe :
      __re_unflatten (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) ≠
        Term.Stuck) :
    __re_unflatten (Term.Boolean false) a ≠
        Term.Stuck ∧
      __re_unflatten (Term.Boolean true) b ≠
        Term.Stuck := by
  have hEq :=
    __re_unflatten.eq_3 a b hANotStrToRe
  rw [hEq] at hNe
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean false) a) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hNe
  exact ⟨
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe,
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hNe⟩

theorem re_unflatten_str_false_str_to_re_tail_ne_stuck_local
    (acc s b : Term)
    (hAccNe : acc ≠ Term.Stuck)
    (hNe :
      __re_unflatten_str acc
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) b) ≠
        Term.Stuck) :
    __re_unflatten_str
        (__eo_list_concat (Term.UOp UserOp.str_concat) acc
          (__str_nary_intro s)) b ≠
      Term.Stuck := by
  have hEq :=
    __re_unflatten_str.eq_3 acc s b hAccNe
  rw [hEq] at hNe
  simpa [__str_nary_intro] using hNe

theorem re_unflatten_str_false_default_children_ne_stuck_local
    (acc b : Term)
    (hAccNe : acc ≠ Term.Stuck)
    (hBNe : b ≠ Term.Stuck)
    (hNotStrPrefix :
      ∀ (s tail : Term),
        b =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False)
    (hNe :
      __re_unflatten_str acc b ≠ Term.Stuck) :
    __str_collect acc ≠ Term.Stuck ∧
      __re_unflatten (Term.Boolean true) b ≠
        Term.Stuck := by
  have hEq :=
    __re_unflatten_str.eq_4 acc b hAccNe hBNe hNotStrPrefix
  rw [hEq] at hNe
  let collected :=
    __str_collect acc
  let singleton :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat) collected
  let head :=
    __eo_mk_apply (Term.UOp UserOp.str_to_re) singleton
  let unflatB :=
    __re_unflatten (Term.Boolean true) b
  have hInnerConcatNe :
      __eo_mk_apply (Term.UOp UserOp.re_concat) head ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ (by
      simpa [collected, singleton, head, unflatB] using hNe)
  have hHeadNe : head ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerConcatNe
  have hSingletonNe : singleton ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hHeadNe
  have hUnflatBNe : unflatB ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ (by
      simpa [collected, singleton, head, unflatB] using hNe)
  have hReqNe :
      __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) collected)
          (Term.Boolean true) (__eo_list_singleton_elim_2 collected) ≠
        Term.Stuck := by
    simpa [singleton, __eo_list_singleton_elim] using hSingletonNe
  have hElim2Ne :
      __eo_list_singleton_elim_2 collected ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.str_concat) collected)
      (Term.Boolean true) (__eo_list_singleton_elim_2 collected)
      hReqNe
  have hCollectedNe : collected ≠ Term.Stuck := by
    cases hCollected : collected <;>
      simp [collected, hCollected, __eo_list_singleton_elim_2] at hElim2Ne ⊢
  exact ⟨by simpa [collected] using hCollectedNe,
    by simpa [unflatB] using hUnflatBNe⟩

theorem re_unflatten_str_false_default_eval_rel_from_true_local
    (M : SmtModel) (hM : model_wf M)
    (acc b : Term) (accSs : SmtSeq) (rb : SmtRegLan)
    (hTrue :
      ∀ rb',
        __smtx_typeof (__eo_to_smt b) = SmtType.RegLan ->
        __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb' ->
        __re_unflatten (Term.Boolean true) b ≠
          Term.Stuck ->
        ∃ outRv,
          __smtx_model_eval M
              (__eo_to_smt
                (__re_unflatten (Term.Boolean true)
                  b)) =
            SmtValue.RegLan outRv ∧
          __smtx_typeof
              (__eo_to_smt
                (__re_unflatten (Term.Boolean true)
                  b)) =
            SmtType.RegLan ∧
          RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
            (SmtValue.RegLan rb'))
    (hAccNe : acc ≠ Term.Stuck)
    (hBNe : b ≠ Term.Stuck)
    (hNotStrPrefix :
      ∀ (s tail : Term),
        b =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc =
        Term.Boolean true)
    (hAccTy :
      __smtx_typeof (__eo_to_smt acc) =
        SmtType.Seq SmtType.Char)
    (hAccEval :
      __smtx_model_eval M (__eo_to_smt acc) =
        SmtValue.Seq accSs)
    (hBTy :
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan)
    (hBEval :
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb)
    (hNe :
      __re_unflatten_str acc b ≠ Term.Stuck) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten_str acc b)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten_str acc b)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs)) rb)) := by
  rcases re_unflatten_str_false_default_children_ne_stuck_local acc b
      hAccNe hBNe hNotStrPrefix hNe with
    ⟨hCollect, hUnflatBNe⟩
  rcases hTrue rb hBTy hBEval hUnflatBNe with
    ⟨rb', hUnflatBEval, hUnflatBTy, hUnflatBRel⟩
  exact re_unflatten_str_false_default_eval_rel_step_local M hM acc b
    accSs rb rb' hAccNe hBNe hNotStrPrefix hAccList hAccTy
    hAccEval hUnflatBTy hUnflatBEval hUnflatBRel hCollect

theorem smt_eval_reglan_of_smt_type_reglan_consume_local
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.RegLan) :
    ∃ r, __smtx_model_eval M t = SmtValue.RegLan r := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) =
        SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact reglan_value_canonical hValTy

theorem smt_eval_seq_char_of_smt_type_seq_char_consume_local
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Seq SmtType.Char) :
    ∃ ss, __smtx_model_eval M t = SmtValue.Seq ss := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) =
        SmtType.Seq SmtType.Char := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact seq_value_canonical hValTy

theorem eval_re_concat_parts_consume_local
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) (rv : SmtRegLan)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
        SmtType.RegLan)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
        SmtValue.RegLan rv) :
    ∃ ra rb,
      __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan ∧
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb ∧
      rv = native_re_concat ra rb := by
  have hNN : term_has_non_none_type
      (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) ≠
      SmtType.None
    rw [hTy]
    simp
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.RegLan :=
    reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt a) hArgs.1 with ⟨ra, hAEval⟩
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt b) hArgs.2 with ⟨rb, hBEval⟩
  have hNative :
      SmtValue.RegLan (native_re_concat ra rb) = SmtValue.RegLan rv := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.RegLan rv at hEval
    simpa [__smtx_model_eval, __smtx_model_eval_re_concat, hAEval,
      hBEval] using hEval
  cases hNative
  exact ⟨ra, rb, hArgs.1, hArgs.2, hAEval, hBEval, rfl⟩

theorem eval_re_union_parts_consume_local
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) (rv : SmtRegLan)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
        SmtType.RegLan)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
        SmtValue.RegLan rv) :
    ∃ ra rb,
      __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan ∧
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb ∧
      rv = native_re_union ra rb := by
  have hNN : term_has_non_none_type
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) ≠
      SmtType.None
    rw [hTy]
    simp
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.RegLan :=
    reglan_binop_args_of_non_none (op := SmtTerm.re_union)
      (typeof_re_union_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt a) hArgs.1 with ⟨ra, hAEval⟩
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt b) hArgs.2 with ⟨rb, hBEval⟩
  have hNative :
      SmtValue.RegLan (native_re_union ra rb) = SmtValue.RegLan rv := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.RegLan rv at hEval
    simpa [__smtx_model_eval, __smtx_model_eval_re_union, hAEval,
      hBEval] using hEval
  cases hNative
  exact ⟨ra, rb, hArgs.1, hArgs.2, hAEval, hBEval, rfl⟩

theorem eval_re_inter_parts_consume_local
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) (rv : SmtRegLan)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
        SmtType.RegLan)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
        SmtValue.RegLan rv) :
    ∃ ra rb,
      __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan ∧
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb ∧
      rv = native_re_inter ra rb := by
  have hNN : term_has_non_none_type
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) ≠
      SmtType.None
    rw [hTy]
    simp
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.RegLan :=
    reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
      (typeof_re_inter_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt a) hArgs.1 with ⟨ra, hAEval⟩
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt b) hArgs.2 with ⟨rb, hBEval⟩
  have hNative :
      SmtValue.RegLan (native_re_inter ra rb) = SmtValue.RegLan rv := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.RegLan rv at hEval
    simpa [__smtx_model_eval, __smtx_model_eval_re_inter, hAEval,
      hBEval] using hEval
  cases hNative
  exact ⟨ra, rb, hArgs.1, hArgs.2, hAEval, hBEval, rfl⟩

theorem str_in_re_re_concat_false_rel_of_no_split_consume_local
    (M : SmtModel) (hM : model_wf M)
    (s r1 r2 side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1)
                r2)))
          side))
    (hNoSplit :
      ∀ ss rv1,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r1) = SmtValue.RegLan rv1 ->
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              native_str_in_re pre rv1 = false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1)
              r2))))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean false))) := by
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2
  rcases str_re_consume_translation_facts s rConcat side (by
      simpa [rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hConcatTy, _hEqBool⟩
  rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
      (__eo_to_smt s) hSTy with
    ⟨ss, hSEval⟩
  have hSsTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt rConcat) hConcatTy with
    ⟨rv, hRConcatEval⟩
  rcases eval_re_concat_parts_consume_local M hM r1 r2 rv
      (by simpa [rConcat] using hConcatTy)
      (by simpa [rConcat] using hRConcatEval) with
    ⟨rv1, rv2, _hR1Ty, _hR2Ty, hR1Eval, _hR2Eval, hRv⟩
  subst rv
  have hNativeFalse :
      native_str_in_re (native_unpack_string ss)
          (native_re_concat rv1 rv2) =
        false :=
    native_str_in_re_re_concat_false_of_no_split_local
      (native_unpack_string ss) rv1 rv2
      (hNoSplit ss rv1 hSEval hR1Eval)
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt rConcat)))
    (__smtx_model_eval M (SmtTerm.Boolean false))
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
    hRConcatEval, hNativeFalse,
    model_str_in_re_unpack_eq_string_of_value_type ss
      (native_re_concat rv1 rv2) hSsTy]
  exact RuleProofs.smt_value_rel_refl _

theorem str_in_re_re_mult_concat_rel_of_no_nonempty_prefix_consume_local
    (M : SmtModel) (hM : model_wf M)
    (s r3 r2 side right : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.re_mult) r3))
                r2)))
          side))
    (hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r2)))
        (__smtx_model_eval M (__eo_to_smt right)))
    (hNoNonemptyPrefix :
      ∀ ss rv3,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r3) = SmtValue.RegLan rv3 ->
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              pre ≠ [] ->
                native_str_in_re pre rv3 = false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult) r3))
              r2))))
      (__smtx_model_eval M (__eo_to_smt right)) := by
  let rStar := Term.Apply (Term.UOp UserOp.re_mult) r3
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) rStar) r2
  rcases str_re_consume_translation_facts s rConcat side (by
      simpa [rStar, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hConcatTy, _hEqBool⟩
  rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
      (__eo_to_smt s) hSTy with
    ⟨ss, hSEval⟩
  have hSsTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt rConcat) hConcatTy with
    ⟨rv, hRConcatEval⟩
  rcases eval_re_concat_parts_consume_local M hM rStar r2 rv
      (by simpa [rStar, rConcat] using hConcatTy)
      (by simpa [rStar, rConcat] using hRConcatEval) with
    ⟨starRv, rv2, hStarTy, _hR2Ty, hStarEval, hR2Eval, hRv⟩
  subst rv
  have hR3Ty :
      __smtx_typeof (__eo_to_smt r3) = SmtType.RegLan :=
    RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan r3
      (by simpa [rStar] using hStarTy)
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt r3) hR3Ty with
    ⟨rv3, hR3Eval⟩
  have hStarNative :
      SmtValue.RegLan (native_re_mult rv3) =
        SmtValue.RegLan starRv := by
    change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt r3)) =
      SmtValue.RegLan starRv at hStarEval
    simpa [__smtx_model_eval, __smtx_model_eval_re_mult, hR3Eval]
      using hStarEval
  cases hStarNative
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_concat (native_re_mult rv3) rv2) =
        native_str_in_re (native_unpack_string ss) rv2 :=
    native_str_in_re_re_mult_concat_eq_tail_of_no_prefix_local
      (native_unpack_string ss) rv3 rv2
      (hNoNonemptyPrefix ss rv3 hSEval hR3Eval)
  have hOrigRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              rConcat)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              r2))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt rConcat)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hRConcatEval, hR2Eval, hNativeEq,
      model_str_in_re_unpack_eq_string_of_value_type ss
        (native_re_concat (native_re_mult rv3) rv2) hSsTy,
      model_str_in_re_unpack_eq_string_of_value_type ss rv2 hSsTy]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigRightRel hRightRel

theorem str_in_re_residual_rel_of_native_eq_consume_local
    (M : SmtModel) (hM : model_wf M)
    (s r side s' r' residual : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hS'Ty :
      __smtx_typeof (__eo_to_smt s') = SmtType.Seq SmtType.Char)
    (hR'Ty :
      __smtx_typeof (__eo_to_smt r') = SmtType.RegLan)
    (hResidualRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r')))
        (__smtx_model_eval M (__eo_to_smt residual)))
    (hNativeEq :
      ∀ ss rv ss' rv',
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt s') = SmtValue.Seq ss' ->
        __smtx_model_eval M (__eo_to_smt r') = SmtValue.RegLan rv' ->
          native_str_in_re (native_unpack_string ss) rv =
            native_str_in_re (native_unpack_string ss') rv') :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt residual)) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hRTy, _hEqBool⟩
  rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
      (__eo_to_smt s) hSTy with
    ⟨ss, hSEval⟩
  have hSsTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt r) hRTy with
    ⟨rv, hREval⟩
  rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
      (__eo_to_smt s') hS'Ty with
    ⟨ss', hS'Eval⟩
  have hSs'Ty :
      __smtx_typeof_value (SmtValue.Seq ss') =
        SmtType.Seq SmtType.Char := by
    rw [← hS'Eval]
    simpa [hS'Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s') (by
        unfold term_has_non_none_type
        rw [hS'Ty]
        simp)
  rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
      (__eo_to_smt r') hR'Ty with
    ⟨rv', hR'Eval⟩
  have hNative :
      native_str_in_re (native_unpack_string ss) rv =
        native_str_in_re (native_unpack_string ss') rv' :=
    hNativeEq ss rv ss' rv' hSEval hREval hS'Eval hR'Eval
  have hOrigResidualTermRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s') r'))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s') (__eo_to_smt r')))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hREval, hS'Eval, hR'Eval, hNative,
      model_str_in_re_unpack_eq_string_of_value_type ss rv hSsTy,
      model_str_in_re_unpack_eq_string_of_value_type ss' rv' hSs'Ty]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigResidualTermRel
    hResidualRel

theorem term_ne_stuck_of_smt_type_reglan_consume_local
    (r : Term)
    (hTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    r ≠ Term.Stuck := by
  exact RuleProofs.term_ne_stuck_of_has_smt_translation r (by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTy]
    simp)

def StrInReConsumeInternal.re_unflatten_true_rel_local
    (M : SmtModel) (r : Term) : Prop :=
  ∀ rv,
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
    __re_unflatten (Term.Boolean true) r ≠
      Term.Stuck ->
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true) r)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true) r)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan rv)

def StrInReConsumeInternal.re_unflatten_false_rel_local
    (M : SmtModel) (r : Term) : Prop :=
  ∀ rv,
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
    __re_unflatten (Term.Boolean false) r ≠
      Term.Stuck ->
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false) r)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean false) r)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan rv)

def StrInReConsumeInternal.re_unflatten_str_rel_local
    (M : SmtModel) (r : Term) : Prop :=
  ∀ acc accSs rb,
    __eo_is_list (Term.UOp UserOp.str_concat) acc = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt acc) = SmtType.Seq SmtType.Char ->
    __smtx_model_eval M (__eo_to_smt acc) = SmtValue.Seq accSs ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rb ->
    __re_unflatten_str acc r ≠ Term.Stuck ->
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten_str acc r)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten_str acc r)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan
          (native_re_concat
            (native_str_to_re (native_unpack_string accSs)) rb))

theorem StrInReConsumeInternal.re_unflatten_default_rels_local
    (M : SmtModel) (hM : model_wf M) (r : Term)
    (hNotStrPrefix :
      ∀ (s tail : Term),
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False)
    (hNotConcat :
      ∀ (a b : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
        False)
    (hNotMult :
      ∀ body : Term,
        r = Term.Apply (Term.UOp UserOp.re_mult) body -> False)
    (hNotInter :
      ∀ (c1 c2 : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
        False)
    (hNotUnion :
      ∀ (c1 c2 : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
        False) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M r ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M r ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M r := by
  constructor
  · intro rv hRTy hREval hNe
    exact re_unflatten_false_true_default_eval_rel_step_local M r rv
      (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy)
      hNotStrPrefix hNotConcat hRTy hREval
  constructor
  · intro rv hRTy hREval hNe
    exact re_unflatten_false_false_default_eval_rel_step_local M r rv
      (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy)
      hNotMult hNotInter hNotUnion hRTy hREval
  · intro acc accSs rb hAccList hAccTy hAccEval hRTy hREval hNe
    have hTrue :
        ∀ rb',
          __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
          __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rb' ->
          __re_unflatten (Term.Boolean true) r ≠
            Term.Stuck ->
          ∃ outRv,
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_unflatten (Term.Boolean true)
                    r)) =
              SmtValue.RegLan outRv ∧
            __smtx_typeof
                (__eo_to_smt
                  (__re_unflatten (Term.Boolean true)
                    r)) =
              SmtType.RegLan ∧
            RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
              (SmtValue.RegLan rb') := by
      intro rb' hRTy' hREval' hNe'
      exact re_unflatten_false_true_default_eval_rel_step_local M r rb'
        (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy')
        hNotStrPrefix hNotConcat hRTy' hREval'
    exact re_unflatten_str_false_default_eval_rel_from_true_local M hM
      acc r accSs rb hTrue
      (RuleProofs.term_ne_stuck_of_has_smt_translation acc (by
        unfold RuleProofs.eo_has_smt_translation
        rw [hAccTy]
        simp))
      (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy)
      hNotStrPrefix hAccList hAccTy hAccEval hRTy hREval hNe

theorem StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local
    (M : SmtModel) (hM : model_wf M) (r : Term)
    (hNotApply :
      ∀ f x : Term, r = Term.Apply f x -> False) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M r ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M r ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M r := by
  exact StrInReConsumeInternal.re_unflatten_default_rels_local M hM r
    (by
      intro s tail h
      exact hNotApply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail h)
    (by
      intro a b h
      exact hNotApply (Term.Apply (Term.UOp UserOp.re_concat) a) b h)
    (by
      intro body h
      exact hNotApply (Term.UOp UserOp.re_mult) body h)
    (by
      intro c1 c2 h
      exact hNotApply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 h)
    (by
      intro c1 c2 h
      exact hNotApply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 h)

theorem StrInReConsumeInternal.re_unflatten_apply_uop_default_rels_local
    (M : SmtModel) (hM : model_wf M)
    (op : UserOp) (x : Term)
    (hNotMultOp : op ≠ UserOp.re_mult) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M (Term.Apply (Term.UOp op) x) ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M (Term.Apply (Term.UOp op) x) ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M (Term.Apply (Term.UOp op) x) := by
  exact StrInReConsumeInternal.re_unflatten_default_rels_local M hM
    (Term.Apply (Term.UOp op) x)
    (by
      intro s tail h
      cases h)
    (by
      intro a b h
      cases h)
    (by
      intro body h
      cases h
      exact hNotMultOp rfl)
    (by
      intro c1 c2 h
      cases h)
    (by
      intro c1 c2 h
      cases h)

theorem StrInReConsumeInternal.re_unflatten_apply_apply_default_rels_local
    (M : SmtModel) (hM : model_wf M)
    (g y x : Term)
    (hNotConcatG : g ≠ Term.UOp UserOp.re_concat)
    (hNotInterG : g ≠ Term.UOp UserOp.re_inter)
    (hNotUnionG : g ≠ Term.UOp UserOp.re_union) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M (Term.Apply (Term.Apply g y) x) ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M
        (Term.Apply (Term.Apply g y) x) ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M
        (Term.Apply (Term.Apply g y) x) := by
  exact StrInReConsumeInternal.re_unflatten_default_rels_local M hM
    (Term.Apply (Term.Apply g y) x)
    (by
      intro s tail h
      cases h
      exact hNotConcatG rfl)
    (by
      intro a b h
      cases h
      exact hNotConcatG rfl)
    (by
      intro body h
      cases h)
    (by
      intro c1 c2 h
      cases h
      exact hNotInterG rfl)
    (by
      intro c1 c2 h
      cases h
      exact hNotUnionG rfl)

theorem StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local
    (M : SmtModel) (hM : model_wf M)
    (f x : Term)
    (hNotUOp : ∀ op : UserOp, f = Term.UOp op -> False)
    (hNotApply : ∀ g y : Term, f = Term.Apply g y -> False) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M (Term.Apply f x) ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M (Term.Apply f x) ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M (Term.Apply f x) := by
  exact StrInReConsumeInternal.re_unflatten_default_rels_local M hM (Term.Apply f x)
    (by
      intro s tail h
      cases h
      exact hNotApply
        (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.str_to_re) s) rfl)
    (by
      intro a b h
      cases h
      exact hNotApply (Term.UOp UserOp.re_concat) a rfl)
    (by
      intro body h
      cases h
      exact hNotUOp UserOp.re_mult rfl)
    (by
      intro c1 c2 h
      cases h
      exact hNotApply (Term.UOp UserOp.re_inter) c1 rfl)
    (by
      intro c1 c2 h
      cases h
      exact hNotApply (Term.UOp UserOp.re_union) c1 rfl)

theorem StrInReConsumeInternal.term_ne_stuck_of_eo_is_list_true_local
    (op x : Term)
    (hList : __eo_is_list op x = Term.Boolean true) :
    x ≠ Term.Stuck := by
  intro h
  subst x
  cases op <;> simp [__eo_is_list] at hList

theorem StrInReConsumeInternal.re_unflatten_str_default_from_true_rel_local
    (M : SmtModel) (hM : model_wf M) (r : Term)
    (hTrue : StrInReConsumeInternal.re_unflatten_true_rel_local M r)
    (hNotStrPrefix :
      ∀ (s tail : Term),
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False) :
    StrInReConsumeInternal.re_unflatten_str_rel_local M r := by
  intro acc accSs rb hAccList hAccTy hAccEval hRTy hREval hNe
  exact re_unflatten_str_false_default_eval_rel_from_true_local M hM
    acc r accSs rb hTrue
    (RuleProofs.term_ne_stuck_of_has_smt_translation acc (by
      unfold RuleProofs.eo_has_smt_translation
      rw [hAccTy]
      simp))
    (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy)
    hNotStrPrefix hAccList hAccTy hAccEval hRTy hREval hNe

theorem StrInReConsumeInternal.re_unflatten_re_mult_rels_local
    (M : SmtModel) (hM : model_wf M)
    (body : Term)
    (hBodyRels :
      StrInReConsumeInternal.re_unflatten_true_rel_local M body ∧
        StrInReConsumeInternal.re_unflatten_false_rel_local M body ∧
        StrInReConsumeInternal.re_unflatten_str_rel_local M body) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M
        (Term.Apply (Term.UOp UserOp.re_mult) body) ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M
        (Term.Apply (Term.UOp UserOp.re_mult) body) ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M
        (Term.Apply (Term.UOp UserOp.re_mult) body) := by
  let r := Term.Apply (Term.UOp UserOp.re_mult) body
  have hNotStrPrefix :
      ∀ (s tail : Term),
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False := by
    intro s tail h
    have h' :
        Term.Apply (Term.UOp UserOp.re_mult) body =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail := by
      simpa [r] using h
    cases h'
  have hNotConcat :
      ∀ (a b : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
        False := by
    intro a b h
    have h' :
        Term.Apply (Term.UOp UserOp.re_mult) body =
          Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b := by
      simpa [r] using h
    cases h'
  have hTrue : StrInReConsumeInternal.re_unflatten_true_rel_local M r := by
    intro rv hRTy hREval hNe
    exact re_unflatten_false_true_default_eval_rel_step_local M r rv
      (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy)
      hNotStrPrefix hNotConcat hRTy hREval
  have hFalse : StrInReConsumeInternal.re_unflatten_false_rel_local M r := by
    intro rv hRTy hREval hNe
    rcases hBodyRels with ⟨hBodyTrue, _hBodyFalse, _hBodyStr⟩
    have hParentNN :
        term_has_non_none_type (SmtTerm.re_mult (__eo_to_smt body)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt r) ≠ SmtType.None
      rw [hRTy]
      simp
    have hBodyTy :
        __smtx_typeof (__eo_to_smt body) = SmtType.RegLan :=
      reglan_arg_of_non_none
        (op := SmtTerm.re_mult) (t := __eo_to_smt body)
        (typeof_re_mult_eq (__eo_to_smt body)) hParentNN
    rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
        (__eo_to_smt body) hBodyTy with
      ⟨bodyRv, hBodyEval⟩
    have hParentEvalNative :
        SmtValue.RegLan (native_re_mult bodyRv) =
          SmtValue.RegLan rv := by
      change __smtx_model_eval M
          (SmtTerm.re_mult (__eo_to_smt body)) =
        SmtValue.RegLan rv at hREval
      simpa [__smtx_model_eval, __smtx_model_eval_re_mult,
        hBodyEval] using hREval
    cases hParentEvalNative
    have hChildList :
        __eo_is_list (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              body) =
          Term.Boolean true :=
      re_unflatten_false_re_mult_child_list_of_ne_stuck_local body
        (by simpa [r] using hNe)
    have hChildNe :
        __re_unflatten (Term.Boolean true) body ≠
          Term.Stuck :=
      StrInReConsumeInternal.term_ne_stuck_of_eo_is_list_true_local
        (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true) body)
        hChildList
    rcases hBodyTrue bodyRv hBodyTy hBodyEval hChildNe with
      ⟨flatRv, hFlatEval, hFlatTy, hFlatRel⟩
    exact re_unflatten_false_re_mult_eval_rel_step_local M hM body
      bodyRv flatRv hBodyEval hFlatTy hFlatEval hChildList hFlatRel
  have hStr : StrInReConsumeInternal.re_unflatten_str_rel_local M r :=
    StrInReConsumeInternal.re_unflatten_str_default_from_true_rel_local M hM r hTrue
      hNotStrPrefix
  simpa [r] using And.intro hTrue (And.intro hFalse hStr)

theorem StrInReConsumeInternal.re_unflatten_re_inter_rels_local
    (M : SmtModel) (hM : model_wf M)
    (c1 c2 : Term)
    (hC1Rels :
      StrInReConsumeInternal.re_unflatten_true_rel_local M c1 ∧
        StrInReConsumeInternal.re_unflatten_false_rel_local M c1 ∧
        StrInReConsumeInternal.re_unflatten_str_rel_local M c1)
    (hC2Rels :
      StrInReConsumeInternal.re_unflatten_true_rel_local M c2 ∧
        StrInReConsumeInternal.re_unflatten_false_rel_local M c2 ∧
        StrInReConsumeInternal.re_unflatten_str_rel_local M c2) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
  let r := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2
  have hNotStrPrefix :
      ∀ (s tail : Term),
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False := by
    intro s tail h
    have h' :
        Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail := by
      simpa [r] using h
    cases h'
  have hNotConcat :
      ∀ (a b : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
        False := by
    intro a b h
    have h' :
        Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 =
          Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b := by
      simpa [r] using h
    cases h'
  have hTrue : StrInReConsumeInternal.re_unflatten_true_rel_local M r := by
    intro rv hRTy hREval hNe
    exact re_unflatten_false_true_default_eval_rel_step_local M r rv
      (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy)
      hNotStrPrefix hNotConcat hRTy hREval
  have hFalse : StrInReConsumeInternal.re_unflatten_false_rel_local M r := by
    intro rv hRTy hREval hNe
    rcases hC1Rels with ⟨hC1True, _hC1False, _hC1Str⟩
    rcases hC2Rels with ⟨_hC2True, hC2False, _hC2Str⟩
    have hParentNN :
        term_has_non_none_type
          (SmtTerm.re_inter (__eo_to_smt c1) (__eo_to_smt c2)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt r) ≠ SmtType.None
      rw [hRTy]
      simp
    have hArgsTy :
        __smtx_typeof (__eo_to_smt c1) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt c2) = SmtType.RegLan :=
      reglan_binop_args_of_non_none
        (op := SmtTerm.re_inter) (t1 := __eo_to_smt c1)
        (t2 := __eo_to_smt c2)
        (typeof_re_inter_eq (__eo_to_smt c1) (__eo_to_smt c2))
        hParentNN
    rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
        (__eo_to_smt c1) hArgsTy.1 with
      ⟨rv1, hC1Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
        (__eo_to_smt c2) hArgsTy.2 with
      ⟨rv2, hC2Eval⟩
    have hParentEvalNative :
        SmtValue.RegLan (native_re_inter rv1 rv2) =
          SmtValue.RegLan rv := by
      change __smtx_model_eval M
          (SmtTerm.re_inter (__eo_to_smt c1) (__eo_to_smt c2)) =
        SmtValue.RegLan rv at hREval
      simpa [__smtx_model_eval, __smtx_model_eval_re_inter,
        hC1Eval, hC2Eval] using hREval
    cases hParentEvalNative
    have hChildList :
        __eo_is_list (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              c1) =
          Term.Boolean true :=
      re_unflatten_false_re_inter_child_list_of_ne_stuck_local c1 c2
        (by simpa [r] using hNe)
    have hC1ChildNe :
        __re_unflatten (Term.Boolean true) c1 ≠
          Term.Stuck :=
      StrInReConsumeInternal.term_ne_stuck_of_eo_is_list_true_local
        (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true) c1)
        hChildList
    have hC2ChildNe :
        __re_unflatten (Term.Boolean false) c2 ≠
          Term.Stuck :=
      re_unflatten_false_re_inter_right_ne_stuck_of_ne_stuck_local c1 c2
        (by simpa [r] using hNe)
    rcases hC1True rv1 hArgsTy.1 hC1Eval hC1ChildNe with
      ⟨flatRv1, hFlatEval1, hFlatTy1, hFlatRel1⟩
    rcases hC2False rv2 hArgsTy.2 hC2Eval hC2ChildNe with
      ⟨flatRv2, hFlatEval2, hFlatTy2, hFlatRel2⟩
    exact re_unflatten_false_re_inter_eval_rel_step_local M hM c1 c2
      rv1 rv2 flatRv1 flatRv2 hC1Eval hC2Eval hFlatTy1
      hFlatEval1 hChildList hFlatRel1 hFlatTy2 hFlatEval2 hFlatRel2
  have hStr : StrInReConsumeInternal.re_unflatten_str_rel_local M r :=
    StrInReConsumeInternal.re_unflatten_str_default_from_true_rel_local M hM r hTrue
      hNotStrPrefix
  simpa [r] using And.intro hTrue (And.intro hFalse hStr)

theorem StrInReConsumeInternal.re_unflatten_re_union_rels_local
    (M : SmtModel) (hM : model_wf M)
    (c1 c2 : Term)
    (hC1Rels :
      StrInReConsumeInternal.re_unflatten_true_rel_local M c1 ∧
        StrInReConsumeInternal.re_unflatten_false_rel_local M c1 ∧
        StrInReConsumeInternal.re_unflatten_str_rel_local M c1)
    (hC2Rels :
      StrInReConsumeInternal.re_unflatten_true_rel_local M c2 ∧
        StrInReConsumeInternal.re_unflatten_false_rel_local M c2 ∧
        StrInReConsumeInternal.re_unflatten_str_rel_local M c2) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
  let r := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2
  have hNotStrPrefix :
      ∀ (s tail : Term),
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
        False := by
    intro s tail h
    have h' :
        Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail := by
      simpa [r] using h
    cases h'
  have hNotConcat :
      ∀ (a b : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
        False := by
    intro a b h
    have h' :
        Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 =
          Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b := by
      simpa [r] using h
    cases h'
  have hTrue : StrInReConsumeInternal.re_unflatten_true_rel_local M r := by
    intro rv hRTy hREval hNe
    exact re_unflatten_false_true_default_eval_rel_step_local M r rv
      (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy)
      hNotStrPrefix hNotConcat hRTy hREval
  have hFalse : StrInReConsumeInternal.re_unflatten_false_rel_local M r := by
    intro rv hRTy hREval hNe
    rcases hC1Rels with ⟨hC1True, _hC1False, _hC1Str⟩
    rcases hC2Rels with ⟨_hC2True, hC2False, _hC2Str⟩
    have hParentNN :
        term_has_non_none_type
          (SmtTerm.re_union (__eo_to_smt c1) (__eo_to_smt c2)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt r) ≠ SmtType.None
      rw [hRTy]
      simp
    have hArgsTy :
        __smtx_typeof (__eo_to_smt c1) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt c2) = SmtType.RegLan :=
      reglan_binop_args_of_non_none
        (op := SmtTerm.re_union) (t1 := __eo_to_smt c1)
        (t2 := __eo_to_smt c2)
        (typeof_re_union_eq (__eo_to_smt c1) (__eo_to_smt c2))
        hParentNN
    rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
        (__eo_to_smt c1) hArgsTy.1 with
      ⟨rv1, hC1Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
        (__eo_to_smt c2) hArgsTy.2 with
      ⟨rv2, hC2Eval⟩
    have hParentEvalNative :
        SmtValue.RegLan (native_re_union rv1 rv2) =
          SmtValue.RegLan rv := by
      change __smtx_model_eval M
          (SmtTerm.re_union (__eo_to_smt c1) (__eo_to_smt c2)) =
        SmtValue.RegLan rv at hREval
      simpa [__smtx_model_eval, __smtx_model_eval_re_union,
        hC1Eval, hC2Eval] using hREval
    cases hParentEvalNative
    have hChildList :
        __eo_is_list (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              c1) =
          Term.Boolean true :=
      re_unflatten_false_re_union_child_list_of_ne_stuck_local c1 c2
        (by simpa [r] using hNe)
    have hC1ChildNe :
        __re_unflatten (Term.Boolean true) c1 ≠
          Term.Stuck :=
      StrInReConsumeInternal.term_ne_stuck_of_eo_is_list_true_local
        (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true) c1)
        hChildList
    have hC2ChildNe :
        __re_unflatten (Term.Boolean false) c2 ≠
          Term.Stuck :=
      re_unflatten_false_re_union_right_ne_stuck_of_ne_stuck_local c1 c2
        (by simpa [r] using hNe)
    rcases hC1True rv1 hArgsTy.1 hC1Eval hC1ChildNe with
      ⟨flatRv1, hFlatEval1, hFlatTy1, hFlatRel1⟩
    rcases hC2False rv2 hArgsTy.2 hC2Eval hC2ChildNe with
      ⟨flatRv2, hFlatEval2, hFlatTy2, hFlatRel2⟩
    exact re_unflatten_false_re_union_eval_rel_step_local M hM c1 c2
      rv1 rv2 flatRv1 flatRv2 hC1Eval hC2Eval hFlatTy1
      hFlatEval1 hChildList hFlatRel1 hFlatTy2 hFlatEval2 hFlatRel2
  have hStr : StrInReConsumeInternal.re_unflatten_str_rel_local M r :=
    StrInReConsumeInternal.re_unflatten_str_default_from_true_rel_local M hM r hTrue
      hNotStrPrefix
  simpa [r] using And.intro hTrue (And.intro hFalse hStr)

theorem StrInReConsumeInternal.re_unflatten_re_concat_rels_local
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hARels :
      StrInReConsumeInternal.re_unflatten_true_rel_local M a ∧
        StrInReConsumeInternal.re_unflatten_false_rel_local M a ∧
        StrInReConsumeInternal.re_unflatten_str_rel_local M a)
    (hBRels :
      StrInReConsumeInternal.re_unflatten_true_rel_local M b ∧
        StrInReConsumeInternal.re_unflatten_false_rel_local M b ∧
        StrInReConsumeInternal.re_unflatten_str_rel_local M b) :
    StrInReConsumeInternal.re_unflatten_true_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) ∧
      StrInReConsumeInternal.re_unflatten_false_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) ∧
      StrInReConsumeInternal.re_unflatten_str_rel_local M
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) := by
  classical
  let r := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b
  have hNotMult :
      ∀ body : Term,
        r = Term.Apply (Term.UOp UserOp.re_mult) body -> False := by
    intro body h
    have h' :
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b =
          Term.Apply (Term.UOp UserOp.re_mult) body := by
      simpa [r] using h
    cases h'
  have hNotInter :
      ∀ (c1 c2 : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
        False := by
    intro c1 c2 h
    have h' :
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b =
          Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 := by
      simpa [r] using h
    cases h'
  have hNotUnion :
      ∀ (c1 c2 : Term),
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
        False := by
    intro c1 c2 h
    have h' :
        Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b =
          Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 := by
      simpa [r] using h
    cases h'
  have hTrue : StrInReConsumeInternal.re_unflatten_true_rel_local M r := by
    intro rv hRTy hREval hNe
    have hParentNN :
        term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt r) ≠ SmtType.None
      rw [hRTy]
      simp
    have hArgsTy :
        __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt b) = SmtType.RegLan :=
      reglan_binop_args_of_non_none
        (op := SmtTerm.re_concat) (t1 := __eo_to_smt a)
        (t2 := __eo_to_smt b)
        (typeof_re_concat_eq (__eo_to_smt a) (__eo_to_smt b))
        hParentNN
    rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
        (__eo_to_smt b) hArgsTy.2 with
      ⟨rb, hBEval⟩
    by_cases hANotStrToRe :
        ∀ s : Term,
          a = Term.Apply (Term.UOp UserOp.str_to_re) s -> False
    · rcases hARels with ⟨_hATrue, hAFalse, _hAStr⟩
      rcases hBRels with ⟨hBTrue, _hBFalse, _hBStr⟩
      rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
          (__eo_to_smt a) hArgsTy.1 with
        ⟨ra, hAEval⟩
      have hParentEvalNative :
          SmtValue.RegLan (native_re_concat ra rb) =
            SmtValue.RegLan rv := by
        change __smtx_model_eval M
            (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
          SmtValue.RegLan rv at hREval
        simpa [__smtx_model_eval, __smtx_model_eval_re_concat,
          hAEval, hBEval] using hREval
      cases hParentEvalNative
      rcases re_unflatten_false_true_re_concat_children_ne_stuck_local
          a b hANotStrToRe (by simpa [r] using hNe) with
        ⟨hAChildNe, hBChildNe⟩
      rcases hAFalse ra hArgsTy.1 hAEval hAChildNe with
        ⟨flatRa, hFlatEvalA, hFlatTyA, hFlatRelA⟩
      rcases hBTrue rb hArgsTy.2 hBEval hBChildNe with
        ⟨flatRb, hFlatEvalB, hFlatTyB, hFlatRelB⟩
      exact re_unflatten_false_true_re_concat_eval_rel_step_local M hM
        a b ra rb flatRa flatRb hANotStrToRe hFlatTyA hFlatEvalA
        hFlatRelA hFlatTyB hFlatEvalB hFlatRelB
    · have hExists :
          ∃ s : Term, a = Term.Apply (Term.UOp UserOp.str_to_re) s := by
        by_cases hExists :
            ∃ s : Term, a = Term.Apply (Term.UOp UserOp.str_to_re) s
        · exact hExists
        · exfalso
          exact hANotStrToRe (by
            intro s hs
            exact hExists ⟨s, hs⟩)
      rcases hExists with ⟨s, hAeq⟩
      subst a
      rcases hBRels with ⟨_hBTrue, _hBFalse, hBStr⟩
      have hSTy :
          __smtx_typeof (__eo_to_smt s) =
            SmtType.Seq SmtType.Char :=
        str_to_re_arg_type_of_reglan_consume_local s hArgsTy.1
      rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
          (__eo_to_smt s) hSTy with
        ⟨ss, hSEval⟩
      have hSsTy :
          __smtx_typeof_value (SmtValue.Seq ss) =
            SmtType.Seq SmtType.Char := by
        rw [← hSEval]
        simpa [hSTy] using
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
            unfold term_has_non_none_type
            rw [hSTy]
            simp)
      have hSsSeqTy :
          __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
        have hsimpa := hSsTy
        try simp at hsimpa ⊢
        exact hsimpa
      have hHeadEval :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
            SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) :=
        eval_str_to_re_reglan_consume_local M s ss hSEval hSsSeqTy
      have hParentEvalNative :
          SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string ss)) rb) =
            SmtValue.RegLan rv := by
        change __smtx_model_eval M
            (SmtTerm.re_concat
              (SmtTerm.str_to_re (__eo_to_smt s)) (__eo_to_smt b)) =
          SmtValue.RegLan rv at hREval
        simpa [__smtx_model_eval, __smtx_model_eval_re_concat,
          __smtx_model_eval_str_to_re, hSEval, hBEval,
          native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsSeqTy]
          using hREval
      cases hParentEvalNative
      have hIntroNe : __str_nary_intro s ≠ Term.Stuck :=
        str_nary_intro_ne_stuck_of_seq_type_local s SmtType.Char hSTy
      rcases str_nary_intro_str_to_re_rel_local M hM s ss hSTy
          hSEval hIntroNe with
        ⟨introSs, hIntroEval, hIntroTy, hIntroList, hIntroRel⟩
      have hChildNe :
          __re_unflatten_str (__str_nary_intro s) b ≠
            Term.Stuck :=
        re_unflatten_false_true_str_to_re_child_ne_stuck_local s b
          (by simpa [r] using hNe)
      rcases hBStr (__str_nary_intro s) introSs rb hIntroList
          hIntroTy hIntroEval hArgsTy.2 hBEval hChildNe with
        ⟨outRv, hStrEval, hStrTy, hStrRel⟩
      exact re_unflatten_false_true_str_to_re_eval_rel_step_local M
        s b ss introSs rb outRv hIntroRel hStrEval hStrTy hStrRel
  have hFalse : StrInReConsumeInternal.re_unflatten_false_rel_local M r := by
    intro rv hRTy hREval hNe
    exact re_unflatten_false_false_default_eval_rel_step_local M r rv
      (term_ne_stuck_of_smt_type_reglan_consume_local r hRTy)
      hNotMult hNotInter hNotUnion hRTy hREval
  have hStr : StrInReConsumeInternal.re_unflatten_str_rel_local M r := by
    intro acc accSs rv hAccList hAccTy hAccEval hRTy hREval hNe
    have hParentNN :
        term_has_non_none_type
          (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt r) ≠ SmtType.None
      rw [hRTy]
      simp
    have hArgsTy :
        __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt b) = SmtType.RegLan :=
      reglan_binop_args_of_non_none
        (op := SmtTerm.re_concat) (t1 := __eo_to_smt a)
        (t2 := __eo_to_smt b)
        (typeof_re_concat_eq (__eo_to_smt a) (__eo_to_smt b))
        hParentNN
    rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
        (__eo_to_smt b) hArgsTy.2 with
      ⟨rb, hBEval⟩
    by_cases hANotStrToRe :
        ∀ s : Term,
          a = Term.Apply (Term.UOp UserOp.str_to_re) s -> False
    · have hNotStrPrefix :
          ∀ (s tail : Term),
            r =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail ->
            False := by
        intro s tail h
        have h' :
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s)) tail := by
          simpa [r] using h
        cases h'
        exact hANotStrToRe s rfl
      exact StrInReConsumeInternal.re_unflatten_str_default_from_true_rel_local M hM r hTrue
        hNotStrPrefix acc accSs rv hAccList hAccTy hAccEval hRTy hREval hNe
    · have hExists :
          ∃ s : Term, a = Term.Apply (Term.UOp UserOp.str_to_re) s := by
        by_cases hExists :
            ∃ s : Term, a = Term.Apply (Term.UOp UserOp.str_to_re) s
        · exact hExists
        · exfalso
          exact hANotStrToRe (by
            intro s hs
            exact hExists ⟨s, hs⟩)
      rcases hExists with ⟨s, hAeq⟩
      subst a
      rcases hBRels with ⟨_hBTrue, _hBFalse, hBStr⟩
      have hSTy :
          __smtx_typeof (__eo_to_smt s) =
            SmtType.Seq SmtType.Char :=
        str_to_re_arg_type_of_reglan_consume_local s hArgsTy.1
      rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
          (__eo_to_smt s) hSTy with
        ⟨ss, hSEval⟩
      have hSsTy :
          __smtx_typeof_value (SmtValue.Seq ss) =
            SmtType.Seq SmtType.Char := by
        rw [← hSEval]
        simpa [hSTy] using
          smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
            unfold term_has_non_none_type
            rw [hSTy]
            simp)
      have hSsSeqTy :
          __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
        have hsimpa := hSsTy
        try simp at hsimpa ⊢
        exact hsimpa
      have hHeadEval :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
            SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) :=
        eval_str_to_re_reglan_consume_local M s ss hSEval hSsSeqTy
      have hParentEvalNative :
          SmtValue.RegLan
              (native_re_concat
                (native_str_to_re (native_unpack_string ss)) rb) =
            SmtValue.RegLan rv := by
        change __smtx_model_eval M
            (SmtTerm.re_concat
              (SmtTerm.str_to_re (__eo_to_smt s)) (__eo_to_smt b)) =
          SmtValue.RegLan rv at hREval
        simpa [__smtx_model_eval, __smtx_model_eval_re_concat,
          __smtx_model_eval_str_to_re, hSEval, hBEval,
          native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsSeqTy]
          using hREval
      cases hParentEvalNative
      have hAccNe : acc ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation acc (by
          unfold RuleProofs.eo_has_smt_translation
          rw [hAccTy]
          simp)
      have hIntroNe : __str_nary_intro s ≠ Term.Stuck :=
        str_nary_intro_ne_stuck_of_seq_type_local s SmtType.Char hSTy
      rcases str_list_concat_singleton_intro_str_to_re_rel_local M hM
          acc s accSs ss hAccList hAccTy hAccEval hSTy hSEval
          hIntroNe with
        ⟨newSs, hNewEval, hNewTy, hNewList, hNewStrRel⟩
      have hTailNe :
          __re_unflatten_str
              (__eo_list_concat (Term.UOp UserOp.str_concat) acc
                (__str_nary_intro s)) b ≠
            Term.Stuck :=
        re_unflatten_str_false_str_to_re_tail_ne_stuck_local acc s b
          hAccNe (by simpa [r] using hNe)
      rcases hBStr
          (__eo_list_concat (Term.UOp UserOp.str_concat) acc
            (__str_nary_intro s)) newSs rb hNewList hNewTy hNewEval
          hArgsTy.2 hBEval hTailNe with
        ⟨recRv, hRecEval, hRecTy, hRecRel⟩
      exact re_unflatten_str_false_str_to_re_eval_rel_step_local M
        acc s b accSs ss newSs rb recRv hAccNe hNewEval hNewTy
        hNewList hNewStrRel hRecEval hRecTy hRecRel
  simpa [r] using And.intro hTrue (And.intro hFalse hStr)

theorem StrInReConsumeInternal.re_unflatten_consume_rels_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ r : Term,
      StrInReConsumeInternal.re_unflatten_true_rel_local M r ∧
        StrInReConsumeInternal.re_unflatten_false_rel_local M r ∧
        StrInReConsumeInternal.re_unflatten_str_rel_local M r
  | Term.Apply (Term.UOp op) x => by
      by_cases hOp : op = UserOp.re_mult
      · subst op
        exact StrInReConsumeInternal.re_unflatten_re_mult_rels_local M hM x
          (StrInReConsumeInternal.re_unflatten_consume_rels_local M hM x)
      · exact StrInReConsumeInternal.re_unflatten_apply_uop_default_rels_local M hM op x hOp
  | Term.Apply (Term.Apply g y) x => by
      by_cases hConcat : g = Term.UOp UserOp.re_concat
      · subst g
        exact StrInReConsumeInternal.re_unflatten_re_concat_rels_local M hM y x
          (StrInReConsumeInternal.re_unflatten_consume_rels_local M hM y)
          (StrInReConsumeInternal.re_unflatten_consume_rels_local M hM x)
      · by_cases hInter : g = Term.UOp UserOp.re_inter
        · subst g
          exact StrInReConsumeInternal.re_unflatten_re_inter_rels_local M hM y x
            (StrInReConsumeInternal.re_unflatten_consume_rels_local M hM y)
            (StrInReConsumeInternal.re_unflatten_consume_rels_local M hM x)
        · by_cases hUnion : g = Term.UOp UserOp.re_union
          · subst g
            exact StrInReConsumeInternal.re_unflatten_re_union_rels_local M hM y x
              (StrInReConsumeInternal.re_unflatten_consume_rels_local M hM y)
              (StrInReConsumeInternal.re_unflatten_consume_rels_local M hM x)
          · exact StrInReConsumeInternal.re_unflatten_apply_apply_default_rels_local M hM
              g y x hConcat hInter hUnion
  | Term.Apply (Term.UOp1 op t) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.UOp1 op t) x
        (by intro op' h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.UOp2 op t u) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.UOp2 op t u) x
        (by intro op' h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.UOp3 op t u v) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.UOp3 op t u v) x
        (by intro op' h; cases h)
        (by intro g y h; cases h)
  | Term.Apply Term.__eo_List x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        Term.__eo_List x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply Term.__eo_List_nil x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        Term.__eo_List_nil x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply Term.__eo_List_cons x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        Term.__eo_List_cons x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply Term.Bool x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        Term.Bool x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.Boolean b) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.Boolean b) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.Numeral n) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.Numeral n) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.Rational q) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.Rational q) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.String s) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.String s) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.Binary w n) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.Binary w n) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply Term.Type x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        Term.Type x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply Term.Stuck x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        Term.Stuck x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply Term.FunType x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        Term.FunType x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.Var n t) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.Var n t) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.DatatypeType s d) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.DatatypeType s d) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.DatatypeTypeRef s) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.DatatypeTypeRef s) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.DtcAppType t u) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.DtcAppType t u) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.DtCons s d i) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.DtCons s d i) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.DtSel s d i j) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.DtSel s d i j) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.USort u) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.USort u) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.Apply (Term.UConst u t) x => by
      exact StrInReConsumeInternal.re_unflatten_apply_fun_ne_special_default_rels_local M hM
        (Term.UConst u t) x
        (by intro op h; cases h)
        (by intro g y h; cases h)
  | Term.UOp op => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM (Term.UOp op)
        (by intro f x h; cases h)
  | Term.UOp1 op t => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.UOp1 op t) (by intro f x h; cases h)
  | Term.UOp2 op t u => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.UOp2 op t u) (by intro f x h; cases h)
  | Term.UOp3 op t u v => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.UOp3 op t u v) (by intro f x h; cases h)
  | Term.__eo_List => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        Term.__eo_List (by intro f x h; cases h)
  | Term.__eo_List_nil => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        Term.__eo_List_nil (by intro f x h; cases h)
  | Term.__eo_List_cons => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        Term.__eo_List_cons (by intro f x h; cases h)
  | Term.Bool => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        Term.Bool (by intro f x h; cases h)
  | Term.Boolean b => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.Boolean b) (by intro f x h; cases h)
  | Term.Numeral n => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.Numeral n) (by intro f x h; cases h)
  | Term.Rational q => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.Rational q) (by intro f x h; cases h)
  | Term.String s => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.String s) (by intro f x h; cases h)
  | Term.Binary w n => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.Binary w n) (by intro f x h; cases h)
  | Term.Type => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        Term.Type (by intro f x h; cases h)
  | Term.Stuck => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        Term.Stuck (by intro f x h; cases h)
  | Term.FunType => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        Term.FunType (by intro f x h; cases h)
  | Term.Var n t => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.Var n t) (by intro f x h; cases h)
  | Term.DatatypeType s d => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.DatatypeType s d) (by intro f x h; cases h)
  | Term.DatatypeTypeRef s => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.DatatypeTypeRef s) (by intro f x h; cases h)
  | Term.DtcAppType t u => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.DtcAppType t u) (by intro f x h; cases h)
  | Term.DtCons s d i => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.DtCons s d i) (by intro f x h; cases h)
  | Term.DtSel s d i j => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.DtSel s d i j) (by intro f x h; cases h)
  | Term.USort u => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.USort u) (by intro f x h; cases h)
  | Term.UConst u t => by
      exact StrInReConsumeInternal.re_unflatten_non_apply_default_rels_local M hM
        (Term.UConst u t) (by intro f x h; cases h)
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem re_unflatten_false_true_eval_rel_consume_local
    (M : SmtModel) (hM : model_wf M)
    (r : Term) (rv : SmtRegLan)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval :
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hNe :
      __re_unflatten (Term.Boolean true) r ≠
        Term.Stuck) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true) r)) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_unflatten (Term.Boolean true) r)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan rv) := by
  exact (StrInReConsumeInternal.re_unflatten_consume_rels_local M hM r).1 rv hRTy hREval hNe

theorem re_unflatten_singleton_elim_eval_rel_consume_local
    (M : SmtModel) (hM : model_wf M)
    (r : Term) (rv : SmtRegLan)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval :
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hElimNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true) r) ≠
        Term.Stuck) :
    ∃ outRv,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__re_unflatten (Term.Boolean true) r))) =
        SmtValue.RegLan outRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__re_unflatten (Term.Boolean true) r))) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan outRv)
        (SmtValue.RegLan rv) := by
  let unflat := __re_unflatten (Term.Boolean true) r
  have hUnflatList :
      __eo_is_list (Term.UOp UserOp.re_concat) unflat =
        Term.Boolean true :=
    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_list_of_ne_stuck
      unflat (by simpa [unflat] using hElimNe)
  have hUnflatNe : unflat ≠ Term.Stuck :=
    StrInReConsumeInternal.term_ne_stuck_of_eo_is_list_true_local
      (Term.UOp UserOp.re_concat) unflat hUnflatList
  rcases re_unflatten_false_true_eval_rel_consume_local M hM r rv
      hRTy hREval (by simpa [unflat] using hUnflatNe) with
    ⟨flatRv, hFlatEval, hFlatTy, hFlatRel⟩
  have hElimTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              unflat)) =
        SmtType.RegLan := by
    simpa [unflat] using
      RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type
        unflat hUnflatList hFlatTy
  rcases reConcat_singleton_elim_eval_rel_consume_local M unflat flatRv
      hUnflatList (by simpa [unflat] using hFlatEval) with
    ⟨elimRv, hElimEval, hElimRel⟩
  exact ⟨elimRv, by simpa [unflat] using hElimEval, hElimTy,
    RuleProofs.smt_value_rel_trans _ _ _ hElimRel hFlatRel⟩

theorem StrInReConsumeInternal.str_re_consume_final_args_type_of_side_local
    (side s' r' : Term)
    (hSideTy : __smtx_typeof (__eo_to_smt side) = SmtType.Bool)
    (hSide :
      side =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r')
    (hSideNe : side ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt s') = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r') = SmtType.RegLan := by
  let final :=
    __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r'
  have hFinalNe : final ≠ Term.Stuck := by
    simpa [final, hSide] using hSideNe
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s' ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hFinalNe
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s' =
        Term.Apply (Term.UOp UserOp.str_in_re) s' :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re) s'
      hInnerNe
  have hFinalEq :
      final =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r' := by
    have hOuterEqRaw :
        final =
          Term.Apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' hFinalNe
    rw [hOuterEqRaw, hInnerEq]
  have hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re) s') r') := by
    unfold RuleProofs.eo_has_bool_type
    simpa [final, hSide, hFinalEq] using hSideTy
  simpa [RuleProofs.ReUnfoldNegSupport.mkStrInRe] using
    RuleProofs.ReUnfoldNegSupport.str_in_re_args_of_bool_type s' r'
      hBool

theorem str_re_consume_model_rel_of_final_parts_local
    (M : SmtModel) (hM : model_wf M)
    (s r side parts rePart : Term)
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
              (__str_collect parts)))
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              rePart)))
    (hSideNe : side ≠ Term.Stuck)
    (hPartsList :
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true)
    (hPartsTy :
      __smtx_typeof (__eo_to_smt parts) =
        SmtType.Seq SmtType.Char)
    (hPartsEvalRel :
      ∀ ss,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          ∃ partsSs,
            __smtx_model_eval M (__eo_to_smt parts) =
              SmtValue.Seq partsSs ∧
            RuleProofs.smt_value_rel (SmtValue.Seq partsSs)
              (SmtValue.Seq ss))
    (hCollectNe : __str_collect parts ≠ Term.Stuck)
    (hRePartTy :
      __smtx_typeof (__eo_to_smt rePart) = SmtType.RegLan)
    (hRePartEvalRel :
      ∀ rv,
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∃ reRv,
            __smtx_model_eval M (__eo_to_smt rePart) =
              SmtValue.RegLan reRv ∧
            RuleProofs.smt_value_rel (SmtValue.RegLan reRv)
              (SmtValue.RegLan rv))
    (hUnflatElimNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            rePart) ≠
        Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let s' :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
      (__str_collect parts)
  let r' :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
      (__re_unflatten (Term.Boolean true) rePart)
  have hMkSideNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' ≠
        Term.Stuck := by
    simpa [s', r', hSide] using hSideNe
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s' ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkSideNe
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s' =
        Term.Apply (Term.UOp UserOp.str_in_re) s' :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re) s'
      hInnerNe
  have hOuterEq :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r' := by
    have hOuterEqRaw :
        __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' =
          Term.Apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' hMkSideNe
    rw [hOuterEqRaw, hInnerEq]
  apply str_re_consume_model_rel_of_side_str_in_re_rel M hM s r side s'
    r' hEqTrans
  · rw [hSide]
    simpa [s', r'] using hOuterEq
  · intro ss rv hSEval hREval
    rcases hPartsEvalRel ss hSEval with
      ⟨partsSs, hPartsEval, hPartsRel⟩
    rcases str_collect_singleton_elim_eval_rel_local M hM parts
        partsSs SmtType.Char hPartsList hPartsTy hPartsEval hCollectNe with
      ⟨outSs, hOutEval, hOutRelParts⟩
    rcases hRePartEvalRel rv hREval with
      ⟨reRv, hRePartEval, hRePartRel⟩
    rcases re_unflatten_singleton_elim_eval_rel_consume_local M hM
        rePart reRv hRePartTy hRePartEval hUnflatElimNe with
      ⟨outRv, hOutReEval, _hOutReTy, hOutReRelPart⟩
    exact ⟨outSs, outRv,
      by simpa [s'] using hOutEval,
      by simpa [r'] using hOutReEval,
      RuleProofs.smt_value_rel_trans _ _ _ hOutRelParts hPartsRel,
      RuleProofs.smt_value_rel_trans _ _ _ hOutReRelPart hRePartRel⟩

theorem StrInReConsumeInternal.str_re_consume_model_rel_of_final_parts_native_eq_local
    (M : SmtModel) (hM : model_wf M)
    (s r side parts rePart : Term)
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
              (__str_collect parts)))
          (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
            (__re_unflatten (Term.Boolean true)
              rePart)))
    (hSideNe : side ≠ Term.Stuck)
    (hPartsList :
      __eo_is_list (Term.UOp UserOp.str_concat) parts =
        Term.Boolean true)
    (hPartsTy :
      __smtx_typeof (__eo_to_smt parts) =
        SmtType.Seq SmtType.Char)
    (hCollectNe : __str_collect parts ≠ Term.Stuck)
    (hRePartTy :
      __smtx_typeof (__eo_to_smt rePart) = SmtType.RegLan)
    (hUnflatElimNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            rePart) ≠
        Term.Stuck)
    (hNativeEq :
      ∀ ss rv partsSs reRv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt parts) =
          SmtValue.Seq partsSs ->
        __smtx_model_eval M (__eo_to_smt rePart) =
          SmtValue.RegLan reRv ->
          native_str_in_re (native_unpack_string ss) rv =
            native_str_in_re (native_unpack_string partsSs) reRv) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let s' :=
    __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
      (__str_collect parts)
  let r' :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
      (__re_unflatten (Term.Boolean true) rePart)
  have hMkSideNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' ≠
        Term.Stuck := by
    simpa [s', r', hSide] using hSideNe
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s' ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkSideNe
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s' =
        Term.Apply (Term.UOp UserOp.str_in_re) s' :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re) s'
      hInnerNe
  have hOuterEq :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r' := by
    have hOuterEqRaw :
        __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' =
          Term.Apply (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.str_in_re) s') r' hMkSideNe
    rw [hOuterEqRaw, hInnerEq]
  have hSideApply :
      side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r' := by
    rw [hSide]
    simpa [s', r'] using hOuterEq
  exact str_re_consume_model_rel_of_side_native_eval M hM s r side
    hEqTrans (by
      intro ss rv hSEval hREval
      rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local
          M hM (__eo_to_smt parts) hPartsTy with
        ⟨partsSs, hPartsEval⟩
      rcases smt_model_eval_reglan_of_type M hM rePart hRePartTy with
        ⟨reRv, hRePartEval⟩
      rcases str_collect_singleton_elim_eval_rel_local M hM parts
          partsSs SmtType.Char hPartsList hPartsTy hPartsEval
          hCollectNe with
        ⟨outSs, hOutEval, hOutRelParts⟩
      rcases re_unflatten_singleton_elim_eval_rel_consume_local M hM
          rePart reRv hRePartTy hRePartEval hUnflatElimNe with
        ⟨outRv, hOutReEval, _hOutReTy, hOutReRelPart⟩
      have hPartsSeqTy :
          __smtx_typeof_value (SmtValue.Seq partsSs) =
            SmtType.Seq SmtType.Char := by
        rw [← hPartsEval]
        simpa [hPartsTy] using
          smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt parts) (by
              unfold term_has_non_none_type
              rw [hPartsTy]
              simp)
      have hOutSeqTy :
          __smtx_typeof_value (SmtValue.Seq outSs) =
            SmtType.Seq SmtType.Char := by
        have hSeq : RuleProofs.smt_seq_rel outSs partsSs := by
          simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using
            hOutRelParts
        have hEq : outSs = partsSs :=
          (RuleProofs.smt_seq_rel_iff_eq outSs partsSs).1 hSeq
        rw [hEq]
        exact hPartsSeqTy
      have hOutNative :
          native_str_in_re (native_unpack_string outSs) outRv =
            native_str_in_re (native_unpack_string partsSs) reRv :=
        native_str_in_re_eq_of_seq_reglan_rel hPartsSeqTy hOutRelParts
          hOutReRelPart
      have hOrigNative :
          native_str_in_re (native_unpack_string ss) rv =
            native_str_in_re (native_unpack_string partsSs) reRv :=
        hNativeEq ss rv partsSs reRv hSEval hREval hPartsEval
          hRePartEval
      rw [hSideApply]
      change __smtx_model_eval M
          (SmtTerm.str_in_re (__eo_to_smt s') (__eo_to_smt r')) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv)
      simp [s', r', __smtx_model_eval, __smtx_model_eval_str_in_re,
        hOutEval, hOutReEval,
        model_str_in_re_unpack_eq_string_of_value_type outSs outRv hOutSeqTy]
      rw [hOutNative, ← hOrigNative])

theorem str_re_consume_model_rel_of_re_concat_empty_left
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
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
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hConcatArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hConcatArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hEpsEval :
      __smtx_model_eval M (__eo_to_smt eps) =
        SmtValue.RegLan (native_str_to_re []) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [])) =
      SmtValue.RegLan (native_str_to_re [])
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
     ]
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt concat) =
        SmtValue.RegLan (native_re_concat (native_str_to_re []) rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt eps) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat (native_str_to_re []) rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hEpsEval,
      hREval]
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              concat)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt concat)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hConcatEval, hREval, native_re_concat_left_empty_local]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_concat_empty_right
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat) r)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let concat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r) eps
  rcases str_re_consume_translation_facts s concat side (by
      simpa [eps, concat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hConcatTy, _hEqBool⟩
  have hConcatArgs :
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt eps)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt concat) ≠ SmtType.None
      rw [hConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt r) (__eo_to_smt eps)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hConcatArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hConcatArgs.1]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hEpsEval :
      __smtx_model_eval M (__eo_to_smt eps) =
        SmtValue.RegLan (native_str_to_re []) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [])) =
      SmtValue.RegLan (native_str_to_re [])
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
     ]
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt concat) =
        SmtValue.RegLan (native_re_concat rv (native_str_to_re [])) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt eps)) =
      SmtValue.RegLan (native_re_concat rv (native_str_to_re []))
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hEpsEval,
      hREval]
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              concat)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt concat)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hConcatEval, hREval, native_re_concat_right_empty_local]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_rec_str_concat_re_concat_empty_left_eq
    (s1 s2 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
          r)
        fuel =
      __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        r fuel := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel ⊢

theorem str_re_consume_rec_non_str_concat_re_concat_empty_left_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotConcat :
      ∀ s1 s2 : Term,
        s ≠ Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2) :
    __str_re_consume_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
          r)
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec] at hS hFuel hNotConcat ⊢

theorem str_re_consume_rec_re_concat_empty_left_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
          r)
        fuel =
      __str_re_consume_rec s r fuel := by
  by_cases hConcat :
      ∃ s1 s2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  · rcases hConcat with ⟨s1, s2, hEq⟩
    subst s
    exact str_re_consume_rec_str_concat_re_concat_empty_left_eq s1 s2 r
      fuel hFuel
  · exact str_re_consume_rec_non_str_concat_re_concat_empty_left_eq s r fuel
      hS hFuel (by
        intro s1 s2 hEq
        exact hConcat ⟨s1, s2, hEq⟩)

theorem str_re_consume_rec_re_concat_empty_left_model_rel
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
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_rec_re_concat_empty_left_eq s r fuel hS
      hFuel]
  apply str_re_consume_model_rel_of_re_concat_empty_left M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_str_concat_str_to_re_eq_true_eq
    (s1 s2 s3 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEq : __eo_eq s1 s3 = Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) s3))
          r)
        fuel =
      __str_re_consume_rec s2 r fuel := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hS3Ne hEq ⊢
  all_goals simp [hEq, eo_ite_true]

theorem str_re_consume_rec_str_concat_str_to_re_len_mismatch_eq
    (s1 s2 s3 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEqFalse : __eo_eq s1 s3 = Term.Boolean false)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) =
        Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) s3))
          r)
        fuel =
      Term.Boolean false := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hS3Ne hEqFalse hLen ⊢
  all_goals simp [hEqFalse, hLen, eo_ite_false, eo_ite_true]

theorem str_re_consume_rec_str_concat_str_to_re_no_match_eq
    (s1 s2 s3 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEqFalse : __eo_eq s1 s3 = Term.Boolean false)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) =
        Term.Boolean false) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) s3))
          r)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) s3))
          r) := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hS3Ne hEqFalse hLen ⊢
  all_goals simp [hEqFalse, hLen, eo_ite_false]

theorem str_re_consume_rec_str_concat_re_allchar_len_one_eq
    (s1 s2 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen : __eo_is_eq (__eo_len s1) (Term.Numeral 1) =
      Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.UOp UserOp.re_allchar))
          r)
        fuel =
      __str_re_consume_rec s2 r fuel := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hLen ⊢
  all_goals simp [hLen, eo_ite_true]

theorem str_re_consume_rec_str_concat_re_allchar_len_mismatch_eq
    (s1 s2 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen : __eo_is_eq (__eo_len s1) (Term.Numeral 1) =
      Term.Boolean false) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.UOp UserOp.re_allchar))
          r)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.UOp UserOp.re_allchar))
          r) := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hLen ⊢
  all_goals simp [hLen, eo_ite_false]

theorem str_re_consume_rec_str_concat_re_range_match_eq
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
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
          r)
        fuel =
      __str_re_consume_rec s2 r fuel := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hLen hMatch ⊢
  all_goals simp [hLen, hMatch, eo_ite_true]

theorem str_re_consume_rec_str_concat_re_range_mismatch_eq
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
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        Term.Boolean false) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
          r)
        fuel =
      Term.Boolean false := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hLen hMatch ⊢
  all_goals simp [hLen, hMatch, eo_ite_true, eo_ite_false]

theorem str_re_consume_rec_str_concat_re_range_len_mismatch_eq
    (s1 s2 s3 s5 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
          (__eo_is_eq (__eo_len s5) (Term.Numeral 1))) =
        Term.Boolean false) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
          r)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
          r) := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hLen ⊢
  all_goals simp [hLen, eo_ite_false]

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_mem_not_epsilon_eq
    (s1 s2 r3 r2 fc fr : Term)
    (hLeftNotFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemNotEps :
      __eo_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr)))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean false) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2) := by
  rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr]
  simp [hLeftNotFalse, hMemNotEps, eo_ite_false]

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_right_not_false_eq
    (s1 s2 r3 r2 fc fr : Term)
    (hLeftNotFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr)))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightNotFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r2
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2) := by
  rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr]
  simp [hLeftNotFalse, hMemEps, hRightNotFalse, eo_ite_false,
    eo_ite_true]

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_same_residual_eq
    (s1 s2 r3 r2 fc fr : Term)
    (hLeftNotFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr)))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r2
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean true)
    (hSame :
      __eo_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (__str_membership_str
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr))) =
        Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2) := by
  rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr]
  simp [hLeftNotFalse, hMemEps, hRightFalse, hSame, eo_ite_false,
    eo_ite_true]

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_residual_eq
    (s1 s2 r3 r2 fc fr : Term)
    (hLeftNotFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr)))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r2
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean true)
    (hDifferent :
      __eo_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (__str_membership_str
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr))) =
        Term.Boolean false) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr) =
      __str_re_consume_rec
        (__str_membership_str
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr)))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2)
        fr := by
  rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr]
  simp [hLeftNotFalse, hMemEps, hRightFalse, hDifferent, eo_ite_false,
    eo_ite_true]

theorem str_re_consume_rec_str_concat_re_mult_non_concat_fuel_eq
    (s1 s2 r3 r2 fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotFuelConcat :
      ∀ fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        False) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2) := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hNotFuelConcat ⊢

theorem str_re_consume_rec_str_concat_re_concat_left_false_eq
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
    (hR1Mult :
      ∀ r3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.re_mult) r3)
    (hFuelMult :
      ∀ r3 fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        r1 = Term.Apply (Term.UOp UserOp.re_mult) r3 ->
        False)
    (hLeftFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r1 fuel)
          (Term.Boolean false) =
        Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
        fuel =
      Term.Boolean false := by
  rw [__str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
    hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult]
  simp [hLeftFalse, eo_ite_true]

theorem str_re_consume_rec_str_concat_re_concat_mem_epsilon_eq
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
    (hR1Mult :
      ∀ r3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.re_mult) r3)
    (hFuelMult :
      ∀ r3 fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        r1 = Term.Apply (Term.UOp UserOp.re_mult) r3 ->
        False)
    (hLeftNotFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_is_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
        fuel =
      __str_re_consume_rec
        (__str_membership_str
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r1 fuel))
        r2 fuel := by
  rw [__str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
    hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult]
  simp [hLeftNotFalse, hMemEps, eo_ite_false, eo_ite_true]

theorem str_re_consume_rec_str_concat_re_concat_fallback_eq
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
    (hR1Mult :
      ∀ r3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.re_mult) r3)
    (hFuelMult :
      ∀ r3 fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        r1 = Term.Apply (Term.UOp UserOp.re_mult) r3 ->
        False)
    (hLeftNotFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemNotEps :
      __eo_is_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean false) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2) := by
  rw [__str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
    hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult]
  simp [hLeftNotFalse, hMemNotEps, eo_ite_false]

theorem str_re_consume_string_singleton_of_seq_type_len_one
    (s : Term)
    (hTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hLen : __eo_is_eq (__eo_len s) (Term.Numeral 1) = Term.Boolean true) :
    ∃ c : native_Char, s = Term.String [c] := by
  cases s <;>
    simp [__eo_len, __eo_is_eq, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] at hLen ⊢
  case String str =>
    have hNatLen : str.length = 1 := by
      have hInt : (str.length : Int) = 1 := by
        simpa [native_str_len] using hLen.symm
      exact_mod_cast hInt
    cases str with
    | nil =>
        simp at hNatLen
    | cons c cs =>
        cases cs with
        | nil =>
            exact ⟨c, rfl⟩
        | cons d rest =>
            exfalso
            simp at hNatLen
  case Binary w n =>
    exfalso
    change __smtx_typeof (SmtTerm.Binary w n) =
      SmtType.Seq SmtType.Char at hTy
    rw [__smtx_typeof.eq_5] at hTy
    cases hCond :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hCond] at hTy

theorem str_re_consume_allchar_concat_no_prefix_of_tail_no_prefix_evals_local
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r : Term)
    (hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq SmtType.Char)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hLen : __eo_is_eq (__eo_len s1) (Term.Numeral 1) =
      Term.Boolean true)
    (hTailNoPrefix :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s2) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              native_str_in_re pre rv = false) :
    ∀ ss rv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) =
        SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              r)) =
        SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false := by
  rcases str_re_consume_string_singleton_of_seq_type_len_one s1 hS1Ty
      hLen with ⟨c, hS1Eq⟩
  subst s1
  intro ss rv hSEval hREval pre suf hAppend
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              r)) =
        SmtValue.RegLan (native_re_concat native_re_allchar rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat SmtTerm.re_allchar (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat native_re_allchar rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hRTailEval]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  have hAppend' :
      pre ++ suf = c :: native_unpack_string ss2 := by
    rw [native_unpack_string_pack_seq_concat_local] at hAppend
    simpa [native_unpack_string_pack_string] using hAppend
  exact
    native_str_in_re_re_allchar_concat_singleton_prefix_false_of_tail_no_prefix_local
      c (native_unpack_string ss2) rvTail
      (hTailNoPrefix ss2 rvTail hS2Eval hRTailEval) pre suf hAppend'

theorem str_re_consume_allchar_concat_residual_of_tail_residual_evals_local
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r side : Term)
    (hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq SmtType.Char)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hLen : __eo_is_eq (__eo_len s1) (Term.Numeral 1) =
      Term.Boolean true)
    (hTailResidual :
      ∀ q ss rv ss' qv,
        __smtx_model_eval M (__eo_to_smt s2) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ss' ->
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (native_unpack_string ss)
              (native_re_concat rv qv) =
            native_str_in_re (native_unpack_string ss') qv) :
    ∀ q ss rv ss' qv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) =
        SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              r)) =
        SmtValue.RegLan rv ->
      __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
        SmtValue.Seq ss' ->
      __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
        native_str_in_re (native_unpack_string ss)
            (native_re_concat rv qv) =
          native_str_in_re (native_unpack_string ss') qv := by
  rcases str_re_consume_string_singleton_of_seq_type_len_one s1 hS1Ty
      hLen with
    ⟨c, hS1Eq⟩
  have hCValid : native_char_valid c = true := by
    have hStringTy :
        __smtx_typeof (__eo_to_smt (Term.String [c])) =
          SmtType.Seq SmtType.Char := by
      simpa [hS1Eq] using hS1Ty
    have hStrValid : native_string_valid [c] = true :=
      native_string_valid_of_smtx_typeof_eo_string [c] hStringTy
    simpa [native_string_valid] using hStrValid
  subst s1
  intro q ss rv ss' qv hSEval hREval hTailEval hQEval
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              r)) =
        SmtValue.RegLan (native_re_concat native_re_allchar rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat SmtTerm.re_allchar (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat native_re_allchar rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hRTailEval]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  rw [native_unpack_string_pack_seq_concat_local]
  simp [native_unpack_string_pack_string]
  rw [native_str_in_re_re_concat_assoc_consume_local]
  rw [native_str_in_re_re_allchar_concat_singleton_left_local c
    (native_unpack_string ss2) (native_re_concat rvTail qv) hCValid]
  exact hTailResidual q ss2 rvTail ss' qv hS2Eval hRTailEval
    hTailEval hQEval

theorem str_flatten_singleton_intro_string_singleton_local
    (c : native_Char) :
    __str_flatten
        (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
          (Term.String [c])) =
      substrWord [c] 0 1 := by
  simpa [__str_nary_intro] using (str_flatten_nary_intro_cons c [])

theorem str_re_consume_range_head_native_eq_of_match_local
    (M : SmtModel) (hM : model_wf M)
    (c lo hi : native_Char) (b : native_Bool)
    (hValid : native_string_valid [c] = true)
    (hRangeTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) (Term.String [lo]))
              (Term.String [hi]))) =
        SmtType.RegLan)
    (hMatch :
      __eo_requires (__eo_is_str (Term.String [c])) (Term.Boolean true)
          (__str_eval_str_in_re_rec
            (__str_flatten
              (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
                (Term.String [c])))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) (Term.String [lo]))
              (Term.String [hi]))) =
        Term.Boolean b) :
    native_str_in_re [c] (native_re_range [lo] [hi]) = b := by
  let range :=
    Term.Apply
      (Term.Apply (Term.UOp UserOp.re_range) (Term.String [lo]))
      (Term.String [hi])
  let evalHead :=
    __str_eval_str_in_re_rec
      (__str_flatten
        (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
          (Term.String [c])))
      range
  have hReqNe :
      __eo_requires (__eo_is_str (Term.String [c])) (Term.Boolean true)
          evalHead ≠ Term.Stuck := by
    rw [hMatch]
    simp
  have hEvalHeadEq : evalHead = Term.Boolean b := by
    rw [← eo_requires_result_eq_of_ne_stuck
      (__eo_is_str (Term.String [c])) (Term.Boolean true) evalHead hReqNe]
    exact hMatch
  have hEvalHeadNe : evalHead ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck
      (__eo_is_str (Term.String [c])) (Term.Boolean true) evalHead hReqNe
  have hRangeEval :
      __smtx_model_eval M (__eo_to_smt range) =
        SmtValue.RegLan (native_re_range [lo] [hi]) := by
    change __smtx_model_eval M
        (SmtTerm.re_range (SmtTerm.String [lo]) (SmtTerm.String [hi])) =
      SmtValue.RegLan (native_re_range [lo] [hi])
    simp [__smtx_model_eval, __smtx_model_eval_re_range,
     ]
  have hEvalNeSub :
      __str_eval_str_in_re_rec (substrWord [c] 0 1) range ≠
        Term.Stuck := by
    simpa [evalHead, range,
      str_flatten_singleton_intro_string_singleton_local c] using
      hEvalHeadNe
  have hEvalEq :
      __str_eval_str_in_re_rec (substrWord [c] 0 1) range =
        Term.Boolean (native_str_in_re [c] (native_re_range [lo] [hi])) :=
    by
      simpa [native_str_in_re_eq_model] using
        str_eval_str_in_re_rec_substrWord_eq M hM [c] range
          (native_re_range [lo] [hi]) hValid (by
            simpa [range] using hRangeTy) hRangeEval hEvalNeSub
  have hEvalHeadEqSub :
      __str_eval_str_in_re_rec (substrWord [c] 0 1) range =
        Term.Boolean b := by
    simpa [evalHead, range,
      str_flatten_singleton_intro_string_singleton_local c] using
      hEvalHeadEq
  rw [hEvalEq] at hEvalHeadEqSub
  cases hEvalHeadEqSub
  rfl

theorem str_re_consume_range_concat_no_prefix_of_tail_no_prefix_evals_local
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r : Term)
    (hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq SmtType.Char)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char)
    (hS3Ty : __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char)
    (hS5Ty : __smtx_typeof (__eo_to_smt s5) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hRangeTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        SmtType.RegLan)
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
    (hTailNoPrefix :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s2) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∀ pre suf : native_String,
            pre ++ suf = native_unpack_string ss ->
              native_str_in_re pre rv = false) :
    ∀ ss rv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) =
        SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
              r)) =
        SmtValue.RegLan rv ->
        ∀ pre suf : native_String,
          pre ++ suf = native_unpack_string ss ->
            native_str_in_re pre rv = false := by
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
      hS1Len with ⟨c, hS1Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s3 hS3Ty
      hS3Len with ⟨lo, hS3Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s5 hS5Ty
      hS5Len with ⟨hi, hS5Eq⟩
  have hCValidString : native_string_valid [c] = true := by
    have hStringTy :
        __smtx_typeof (__eo_to_smt (Term.String [c])) =
          SmtType.Seq SmtType.Char := by
      simpa [hS1Eq] using hS1Ty
    exact native_string_valid_of_smtx_typeof_eo_string [c] hStringTy
  subst s1
  subst s3
  subst s5
  intro ss rv hSEval hREval pre suf hAppend
  have hHeadTrue :
      native_str_in_re [c] (native_re_range [lo] [hi]) = true :=
    str_re_consume_range_head_native_eq_of_match_local M hM c lo hi true
      hCValidString (by simpa using hRangeTy) (by simpa using hMatch)
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range)
                    (Term.String [lo]))
                  (Term.String [hi])))
              r)) =
        SmtValue.RegLan (native_re_concat (native_re_range [lo] [hi])
          rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.re_range (SmtTerm.String [lo]) (SmtTerm.String [hi]))
          (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat (native_re_range [lo] [hi])
        rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_re_range, hRTailEval,
     ]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  have hAppend' :
      pre ++ suf = c :: native_unpack_string ss2 := by
    rw [native_unpack_string_pack_seq_concat_local] at hAppend
    simpa [native_unpack_string_pack_string] using hAppend
  exact
    native_str_in_re_re_range_concat_singleton_prefix_false_of_tail_no_prefix_local
      c lo hi (native_unpack_string ss2) rvTail
      (hTailNoPrefix ss2 rvTail hS2Eval hRTailEval) pre suf hAppend'

theorem str_re_consume_range_concat_residual_of_tail_residual_evals_local
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r side : Term)
    (hS1Ty : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq SmtType.Char)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char)
    (hS3Ty : __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char)
    (hS5Ty : __smtx_typeof (__eo_to_smt s5) = SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hRangeTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        SmtType.RegLan)
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
    (hTailResidual :
      ∀ q ss rv ss' qv,
        __smtx_model_eval M (__eo_to_smt s2) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ss' ->
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (native_unpack_string ss)
              (native_re_concat rv qv) =
            native_str_in_re (native_unpack_string ss') qv) :
    ∀ q ss rv ss' qv,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)) =
        SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
              r)) =
        SmtValue.RegLan rv ->
      __smtx_model_eval M (__eo_to_smt (__str_membership_str side)) =
        SmtValue.Seq ss' ->
      __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
        native_str_in_re (native_unpack_string ss)
            (native_re_concat rv qv) =
          native_str_in_re (native_unpack_string ss') qv := by
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
  rcases str_re_consume_string_singleton_of_seq_type_len_one s3 hS3Ty
      hS3Len with
    ⟨lo, hS3Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s5 hS5Ty
      hS5Len with
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
  have hHeadTrue :
      native_str_in_re [c] (native_re_range [lo] [hi]) = true :=
    str_re_consume_range_head_native_eq_of_match_local M hM c lo hi true
      hCValidString (by simpa using hRangeTy) (by simpa using hMatch)
  intro q ss rv ss' qv hSEval hREval hTailEval hQEval
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range)
                    (Term.String [lo]))
                  (Term.String [hi])))
              r)) =
        SmtValue.RegLan (native_re_concat (native_re_range [lo] [hi])
          rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.re_range (SmtTerm.String [lo]) (SmtTerm.String [hi]))
          (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat (native_re_range [lo] [hi])
        rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_re_range, hRTailEval,
     ]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  rw [native_unpack_string_pack_seq_concat_local]
  simp [native_unpack_string_pack_string]
  rw [native_str_in_re_re_concat_assoc_consume_local]
  rw [native_str_in_re_re_range_concat_singleton_left_true_local c lo hi
    (native_unpack_string ss2) (native_re_concat rvTail qv) hHeadTrue]
  exact hTailResidual q ss2 rvTail ss' qv hS2Eval hRTailEval
    hTailEval hQEval

theorem str_re_consume_model_rel_of_str_concat_str_to_re_prefix
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r side : Term)
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
                  (Term.Apply (Term.UOp UserOp.str_to_re) s1))
                r)))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s1))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let headRe := Term.Apply (Term.UOp UserOp.str_to_re) s1
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) headRe) r
  rcases str_re_consume_translation_facts sConcat rConcat side (by
      simpa [sConcat, headRe, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hConcatTy, hRConcatTy, _hEqBool⟩
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hConcatTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt headRe) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt headRe) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [hRConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt headRe) (__eo_to_smt r)) hNN
  have hS1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS1Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s1) (by
        unfold term_has_non_none_type
        rw [hS1Ty]
        simp)
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRConcatArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRConcatArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hS1EvalTy with
    ⟨ss1, hS1Eval, hSs1Ty⟩
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hSs1SeqTy :
      __smtx_typeof_seq_value ss1 = SmtType.Seq SmtType.Char := by
    have hsimpa := hSs1Ty
    try simp at hsimpa ⊢
    exact hsimpa
  have hSs2SeqTy :
      __smtx_typeof_seq_value ss2 = SmtType.Seq SmtType.Char := by
    have hsimpa := hSs2Ty
    try simp at hsimpa ⊢
    exact hsimpa
  have hSs1Unpack :
      native_unpack_seq ss1 =
        impl_native_string_to_values (native_unpack_string ss1) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSs1SeqTy
  have hSs2Unpack :
      native_unpack_seq ss2 =
        impl_native_string_to_values (native_unpack_string ss2) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSs2SeqTy
  have hS1Valid : native_string_valid (native_unpack_string ss1) = true :=
    native_unpack_string_valid_of_typeof_seq_char (by
      have hsimpa := hS1EvalTy; (try simp [hS1Eval] at hsimpa ⊢); exact hsimpa)
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt sConcat) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
            (native_seq_concat (native_unpack_seq ss1)
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
          (native_seq_concat (native_unpack_seq ss1)
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS1Eval,
      hS2Eval]
  have hHeadEval :
      __smtx_model_eval M (__eo_to_smt headRe) =
        SmtValue.RegLan (native_str_to_re (native_unpack_string ss1)) := by
    change __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt s1)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss1))
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hS1Eval,
      hSs1Unpack]
  have hRConcatEval :
      __smtx_model_eval M (__eo_to_smt rConcat) =
        SmtValue.RegLan
          (native_re_concat (native_str_to_re (native_unpack_string ss1)) rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt headRe) (__eo_to_smt r)) =
      SmtValue.RegLan
        (native_re_concat (native_str_to_re (native_unpack_string ss1)) rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hHeadEval,
      hREval]
  have hNativeEq :
      native_str_in_re
          (native_unpack_string
            (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
              (native_seq_concat (native_unpack_seq ss1)
                (native_unpack_seq ss2))))
          (native_re_concat (native_str_to_re (native_unpack_string ss1)) rv) =
        native_str_in_re (native_unpack_string ss2) rv := by
    rw [native_unpack_string_pack_seq_concat_local]
    exact native_str_in_re_str_to_re_concat_left_local
      (native_unpack_string ss1) (native_unpack_string ss2) rv hS1Valid
  have hModelNativeEq :
      Smtm.native_str_in_re
          (native_unpack_seq
            (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
              (native_seq_concat (native_unpack_seq ss1)
                (native_unpack_seq ss2))))
          (native_re_concat (native_str_to_re
            (native_unpack_string ss1)) rv) =
        Smtm.native_str_in_re (native_unpack_seq ss2) rv := by
    calc
      _ = Smtm.native_str_in_re
          (impl_native_string_to_values
            (native_unpack_string ss1 ++ native_unpack_string ss2))
          (native_re_concat (native_str_to_re
            (native_unpack_string ss1)) rv) := by
          simp [native_unpack_seq_pack_seq, hSs1Unpack, hSs2Unpack,
            native_seq_concat, impl_native_string_to_values, List.map_append]
      _ = native_str_in_re
          (native_unpack_string ss1 ++ native_unpack_string ss2)
          (native_re_concat (native_str_to_re
            (native_unpack_string ss1)) rv) :=
        (native_str_in_re_eq_model _ _).symm
      _ = native_str_in_re (native_unpack_string ss2) rv := by
        simpa [native_unpack_string_pack_seq_concat_local] using hNativeEq
      _ = Smtm.native_str_in_re (native_unpack_seq ss2) rv := by
        rw [hSs2Unpack]
        exact native_str_in_re_eq_model _ _
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) sConcat)
              rConcat)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt sConcat) (__eo_to_smt rConcat)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s2) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hConcatEval,
      hRConcatEval, hS2Eval, hREval, hModelNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_str_concat_re_allchar_prefix
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r side : Term)
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
                r)))
          side))
    (hLen : __eo_is_eq (__eo_len s1) (Term.Numeral 1) =
      Term.Boolean true)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let allchar := Term.UOp UserOp.re_allchar
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) allchar) r
  rcases str_re_consume_translation_facts sConcat rConcat side (by
      simpa [sConcat, allchar, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hConcatTy, hRConcatTy, _hEqBool⟩
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hConcatTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt allchar) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt allchar) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [hRConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt allchar) (__eo_to_smt r)) hNN
  rcases str_re_consume_string_singleton_of_seq_type_len_one s1 hS1Ty
      hLen with ⟨c, hS1Eq⟩
  have hCValid : native_char_valid c = true := by
    have hStringTy :
        __smtx_typeof (__eo_to_smt (Term.String [c])) =
          SmtType.Seq SmtType.Char := by
      simpa [hS1Eq] using hS1Ty
    have hStrValid : native_string_valid [c] = true :=
      native_string_valid_of_smtx_typeof_eo_string [c] hStringTy
    simpa [native_string_valid] using hStrValid
  subst s1
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    simpa [allchar] using hRConcatArgs.2
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hSs2SeqTy :
      __smtx_typeof_seq_value ss2 = SmtType.Seq SmtType.Char := by
    have hsimpa := hSs2Ty
    try simp at hsimpa ⊢
    exact hsimpa
  have hSs2Unpack :
      native_unpack_seq ss2 =
        impl_native_string_to_values (native_unpack_string ss2) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSs2SeqTy
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hAllcharEval :
      __smtx_model_eval M (__eo_to_smt allchar) =
        SmtValue.RegLan native_re_allchar := by
    change __smtx_model_eval M SmtTerm.re_allchar =
      SmtValue.RegLan native_re_allchar
    rw [__smtx_model_eval.eq_104]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              r)) =
        SmtValue.RegLan (native_re_concat native_re_allchar rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat SmtTerm.re_allchar (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat native_re_allchar rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hREval]
  have hNativeEq :
      native_str_in_re
          (native_unpack_string
            (native_pack_seq
              (__smtx_elem_typeof_seq_value (native_pack_string [c]))
              (native_seq_concat
                (native_unpack_seq (native_pack_string [c]))
                (native_unpack_seq ss2))))
          (native_re_concat native_re_allchar rv) =
        native_str_in_re (native_unpack_string ss2) rv := by
    rw [native_unpack_string_pack_seq_concat_local]
    simp [native_unpack_string_pack_string]
    exact native_str_in_re_re_allchar_concat_singleton_left_local c
      (native_unpack_string ss2) rv hCValid
  have hModelNativeEq :
      Smtm.native_str_in_re
          (native_unpack_seq
            (native_pack_seq
              (__smtx_elem_typeof_seq_value (native_pack_string [c]))
              (native_seq_concat
                [SmtValue.Char c]
                (native_unpack_seq ss2))))
          (native_re_concat native_re_allchar rv) =
        Smtm.native_str_in_re (native_unpack_seq ss2) rv := by
    calc
      _ = Smtm.native_str_in_re
          (impl_native_string_to_values ([c] ++ native_unpack_string ss2))
          (native_re_concat native_re_allchar rv) := by
          simp [native_unpack_seq_pack_seq, hSs2Unpack,
            native_seq_concat, impl_native_string_to_values]
      _ = native_str_in_re ([c] ++ native_unpack_string ss2)
          (native_re_concat native_re_allchar rv) :=
        (native_str_in_re_eq_model _ _).symm
      _ = native_str_in_re (native_unpack_string ss2) rv := by
        exact native_str_in_re_re_allchar_concat_singleton_left_local c
          (native_unpack_string ss2) rv hCValid
      _ = Smtm.native_str_in_re (native_unpack_seq ss2) rv := by
        rw [hSs2Unpack]
        exact native_str_in_re_eq_model _ _
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat)
                    (Term.String [c])) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.UOp UserOp.re_allchar))
                r))))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2))
          (SmtTerm.re_concat SmtTerm.re_allchar (__eo_to_smt r))))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s2) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
      __smtx_model_eval_str_concat, __smtx_model_eval_re_concat, hS2Eval,
      hREval, hModelNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_str_concat_re_range_prefix
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r side : Term)
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
                r)))
          side))
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
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        Term.Boolean true)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let range := Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) range) r
  rcases str_re_consume_translation_facts sConcat rConcat side (by
      simpa [sConcat, range, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hConcatTy, hRConcatTy, _hEqBool⟩
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hConcatTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt range) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt range) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [hRConcatTy]
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
      hS1Len with ⟨c, hS1Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s3
      hRangeArgs.1 hS3Len with ⟨lo, hS3Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s5
      hRangeArgs.2 hS5Len with ⟨hi, hS5Eq⟩
  have hCValidString : native_string_valid [c] = true := by
    have hStringTy :
        __smtx_typeof (__eo_to_smt (Term.String [c])) =
          SmtType.Seq SmtType.Char := by
      simpa [hS1Eq] using hS1Ty
    exact native_string_valid_of_smtx_typeof_eo_string [c] hStringTy
  subst s1
  subst s3
  subst s5
  have hRangeTySingleton :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) (Term.String [lo]))
              (Term.String [hi]))) =
        SmtType.RegLan := by
    simpa [range] using hRConcatArgs.1
  have hHeadTrue :
      native_str_in_re [c] (native_re_range [lo] [hi]) = true :=
    str_re_consume_range_head_native_eq_of_match_local M hM c lo hi true
      hCValidString hRangeTySingleton (by simpa using hMatch)
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    simpa [range] using hRConcatArgs.2
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hSs2SeqTy :
      __smtx_typeof_seq_value ss2 = SmtType.Seq SmtType.Char := by
    have hsimpa := hSs2Ty
    try simp at hsimpa ⊢
    exact hsimpa
  have hSs2Unpack :
      native_unpack_seq ss2 =
        impl_native_string_to_values (native_unpack_string ss2) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSs2SeqTy
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hRangeEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) (Term.String [lo]))
              (Term.String [hi]))) =
        SmtValue.RegLan (native_re_range [lo] [hi]) := by
    change __smtx_model_eval M
        (SmtTerm.re_range (SmtTerm.String [lo]) (SmtTerm.String [hi])) =
      SmtValue.RegLan (native_re_range [lo] [hi])
    simp [__smtx_model_eval, __smtx_model_eval_re_range,
     ]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range)
                    (Term.String [lo]))
                  (Term.String [hi])))
              r)) =
        SmtValue.RegLan (native_re_concat (native_re_range [lo] [hi]) rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.re_range (SmtTerm.String [lo]) (SmtTerm.String [hi]))
          (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat (native_re_range [lo] [hi]) rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_re_range, hREval]
  have hNativeEq :
      native_str_in_re
          (native_unpack_string
            (native_pack_seq
              (__smtx_elem_typeof_seq_value (native_pack_string [c]))
              (native_seq_concat
                (native_unpack_seq (native_pack_string [c]))
                (native_unpack_seq ss2))))
          (native_re_concat (native_re_range [lo] [hi]) rv) =
        native_str_in_re (native_unpack_string ss2) rv := by
    rw [native_unpack_string_pack_seq_concat_local]
    simp [native_unpack_string_pack_string]
    exact native_str_in_re_re_range_concat_singleton_left_true_local c lo
      hi (native_unpack_string ss2) rv hHeadTrue
  have hModelNativeEq :
      Smtm.native_str_in_re
          (native_unpack_seq
            (native_pack_seq
              (__smtx_elem_typeof_seq_value (native_pack_string [c]))
              (native_seq_concat
                [SmtValue.Char c]
                (native_unpack_seq ss2))))
          (native_re_concat (native_re_range [lo] [hi]) rv) =
        Smtm.native_str_in_re (native_unpack_seq ss2) rv := by
    calc
      _ = Smtm.native_str_in_re
          (impl_native_string_to_values ([c] ++ native_unpack_string ss2))
          (native_re_concat (native_re_range [lo] [hi]) rv) := by
          simp [native_unpack_seq_pack_seq, hSs2Unpack,
            native_seq_concat, impl_native_string_to_values]
      _ = native_str_in_re ([c] ++ native_unpack_string ss2)
          (native_re_concat (native_re_range [lo] [hi]) rv) :=
        (native_str_in_re_eq_model _ _).symm
      _ = native_str_in_re (native_unpack_string ss2) rv := by
        exact native_str_in_re_re_range_concat_singleton_left_true_local c lo
          hi (native_unpack_string ss2) rv hHeadTrue
      _ = Smtm.native_str_in_re (native_unpack_seq ss2) rv := by
        rw [hSs2Unpack]
        exact native_str_in_re_eq_model _ _
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat)
                    (Term.String [c])) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_range)
                      (Term.String [lo]))
                    (Term.String [hi])))
                r))))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2))
          (SmtTerm.re_concat
            (SmtTerm.re_range (SmtTerm.String [lo]) (SmtTerm.String [hi]))
            (__eo_to_smt r))))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s2) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
      __smtx_model_eval_str_concat, __smtx_model_eval_re_concat,
      __smtx_model_eval_re_range, hS2Eval, hREval,
      hModelNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_rec_str_concat_str_to_re_eq_true_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 r fuel side : Term)
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
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s3))
            r)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEq : __eo_eq s1 s3 = Term.Boolean true)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s2 r fuel)))) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hS3Eq : s3 = s1 := eq_of_eo_eq_true s1 s3 hEq
  subst s3
  have hSideRec : side = __str_re_consume_rec s2 r fuel := by
    rw [hSide,
      str_re_consume_rec_str_concat_str_to_re_eq_true_eq s1 s2 s1 r fuel
        hFuel hS3Ne hEq]
  apply str_re_consume_model_rel_of_str_concat_str_to_re_prefix M hM s1
    s2 r side hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_str_concat_re_allchar_len_one_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r fuel side : Term)
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
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.UOp UserOp.re_allchar))
            r)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen : __eo_is_eq (__eo_len s1) (Term.Numeral 1) =
      Term.Boolean true)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s2 r fuel)))) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec : side = __str_re_consume_rec s2 r fuel := by
    rw [hSide,
      str_re_consume_rec_str_concat_re_allchar_len_one_eq s1 s2 r fuel
        hFuel hLen]
  apply str_re_consume_model_rel_of_str_concat_re_allchar_prefix M hM s1
    s2 r side hEqTrans hLen
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_str_concat_re_range_match_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r fuel side : Term)
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
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
            r)
          fuel)
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
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        Term.Boolean true)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s2 r fuel)))) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec : side = __str_re_consume_rec s2 r fuel := by
    rw [hSide,
      str_re_consume_rec_str_concat_re_range_match_eq s1 s2 s3 s5 r
        fuel hFuel hLen hMatch]
  apply str_re_consume_model_rel_of_str_concat_re_range_prefix M hM s1
    s2 s3 s5 r side hEqTrans hLen hMatch
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_str_concat_str_to_re_no_match_model_rel
    (M : SmtModel)
    (s1 s2 s3 r fuel side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s3))
            r)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEqFalse : __eo_eq s1 s3 = Term.Boolean false)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) =
        Term.Boolean false) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.str_to_re) s3))
      r)
    side
  rw [hSide,
    str_re_consume_rec_str_concat_str_to_re_no_match_eq s1 s2 s3 r fuel
      hFuel hS3Ne hEqFalse hLen]

theorem str_re_consume_rec_str_concat_re_allchar_len_mismatch_model_rel
    (M : SmtModel)
    (s1 s2 r fuel side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.UOp UserOp.re_allchar))
            r)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen : __eo_is_eq (__eo_len s1) (Term.Numeral 1) =
      Term.Boolean false) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.UOp UserOp.re_allchar))
      r)
    side
  rw [hSide,
    str_re_consume_rec_str_concat_re_allchar_len_mismatch_eq s1 s2 r fuel
      hFuel hLen]

theorem str_re_consume_rec_str_concat_re_range_len_mismatch_model_rel
    (M : SmtModel)
    (s1 s2 s3 s5 r fuel side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
            r)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
          (__eo_is_eq (__eo_len s5) (Term.Numeral 1))) =
        Term.Boolean false) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
      r)
    side
  rw [hSide,
    str_re_consume_rec_str_concat_re_range_len_mismatch_eq s1 s2 s3 s5 r
      fuel hFuel hLen]

theorem str_re_consume_rec_str_concat_re_mult_non_concat_fuel_model_rel
    (M : SmtModel)
    (s1 s2 r3 r2 fuel side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3))
            r2)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotFuelConcat :
      ∀ fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        False) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult) r3))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.re_mult) r3))
      r2)
    side
  rw [hSide,
    str_re_consume_rec_str_concat_re_mult_non_concat_fuel_eq s1 s2 r3 r2
      fuel hFuel hNotFuelConcat]

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_mem_not_epsilon_model_rel
    (M : SmtModel)
    (s1 s2 r3 r2 fc fr side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3))
            r2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
    (hLeftNotFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemNotEps :
      __eo_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr)))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult) r3))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.re_mult) r3))
      r2)
    side
  rw [hSide,
    str_re_consume_rec_str_concat_re_mult_concat_fuel_mem_not_epsilon_eq
      s1 s2 r3 r2 fc fr hLeftNotFalse hMemNotEps]

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_left_false_model_rel_of_right_rel
    (M : SmtModel)
    (s1 s2 r3 r2 fc fr side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3))
            r2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
    (hLeftFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean true)
    (hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.re_mult) r3))
                r2))))
        (__smtx_model_eval M
          (__eo_to_smt
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r2
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr))))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult) r3))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRight :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          r2
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr) := by
    rw [hSide, __str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr]
    simp [hLeftFalse, eo_ite_true]
  simpa [hSideRight] using hRightRel

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_right_not_false_model_rel
    (M : SmtModel)
    (s1 s2 r3 r2 fc fr side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3))
            r2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
    (hLeftNotFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr)))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightNotFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r2
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult) r3))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.re_mult) r3))
      r2)
    side
  rw [hSide,
    str_re_consume_rec_str_concat_re_mult_concat_fuel_right_not_false_eq
      s1 s2 r3 r2 fc fr hLeftNotFalse hMemEps hRightNotFalse]

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_same_residual_model_rel
    (M : SmtModel)
    (s1 s2 r3 r2 fc fr side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3))
            r2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
    (hLeftNotFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr)))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r2
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean true)
    (hSame :
      __eo_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (__str_membership_str
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr))) =
        Term.Boolean true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult) r3))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.re_mult) r3))
      r2)
    side
  rw [hSide,
    str_re_consume_rec_str_concat_re_mult_concat_fuel_same_residual_eq
      s1 s2 r3 r2 fc fr hLeftNotFalse hMemEps hRightFalse hSame]

theorem str_re_consume_rec_str_concat_re_mult_concat_fuel_residual_model_rel_of_residual_rel
    (M : SmtModel)
    (s1 s2 r3 r2 fc fr side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3))
            r2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
    (hLeftNotFalse :
      __eo_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r3
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr)))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r2
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr))
          (Term.Boolean false) =
        Term.Boolean true)
    (hDifferent :
      __eo_eq
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (__str_membership_str
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr))) =
        Term.Boolean false)
    (hResidualRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.re_mult) r3))
                r2))))
        (__smtx_model_eval M
          (__eo_to_smt
            (__str_re_consume_rec
              (__str_membership_str
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r3
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) fc) fr)))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.re_mult) r3))
                r2)
              fr)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult) r3))
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideFallback :
      side =
        __str_re_consume_rec
          (__str_membership_str
            (__str_re_consume_rec
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r3
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) fc) fr)))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3))
            r2)
          fr := by
    rw [hSide,
      str_re_consume_rec_str_concat_re_mult_concat_fuel_residual_eq
        s1 s2 r3 r2 fc fr hLeftNotFalse hMemEps hRightFalse
        hDifferent]
  simpa [hSideFallback] using hResidualRel

theorem str_re_consume_rec_str_concat_re_concat_fallback_model_rel
    (M : SmtModel)
    (s1 s2 r1 r2 fuel side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hR1Empty :
      r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    (hR1StrToRe :
      ∀ s3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) s3)
    (hR1Range :
      ∀ s3 s5 : Term,
        r1 ≠ Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
    (hR1Allchar : r1 ≠ Term.UOp UserOp.re_allchar)
    (hR1Mult :
      ∀ r3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.re_mult) r3)
    (hFuelMult :
      ∀ r3 fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        r1 = Term.Apply (Term.UOp UserOp.re_mult) r3 ->
        False)
    (hLeftNotFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemNotEps :
      __eo_is_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1)
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
    (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
    side
  rw [hSide,
    str_re_consume_rec_str_concat_re_concat_fallback_eq s1 s2 r1 r2
      fuel hFuel hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult
      hFuelMult hLeftNotFalse hMemNotEps]

theorem str_re_consume_rec_str_concat_re_concat_left_false_model_rel_of_false_rel
    (M : SmtModel)
    (s1 s2 r1 r2 fuel side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hR1Empty :
      r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    (hR1StrToRe :
      ∀ s3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) s3)
    (hR1Range :
      ∀ s3 s5 : Term,
        r1 ≠ Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
    (hR1Allchar : r1 ≠ Term.UOp UserOp.re_allchar)
    (hR1Mult :
      ∀ r3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.re_mult) r3)
    (hFuelMult :
      ∀ r3 fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        r1 = Term.Apply (Term.UOp UserOp.re_mult) r3 ->
        False)
    (hLeftFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r1 fuel)
          (Term.Boolean false) =
        Term.Boolean true)
    (hFalseRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1)
                r2))))
        (__smtx_model_eval M (__eo_to_smt (Term.Boolean false)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1)
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideFallback :
      side = Term.Boolean false := by
    rw [hSide,
      str_re_consume_rec_str_concat_re_concat_left_false_eq s1 s2 r1 r2
        fuel hFuel hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult
        hFuelMult hLeftFalse]
  simpa [hSideFallback] using hFalseRel

theorem str_re_consume_rec_str_concat_re_concat_mem_epsilon_model_rel_of_residual_rel
    (M : SmtModel)
    (s1 s2 r1 r2 fuel side : Term)
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hR1Empty :
      r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    (hR1StrToRe :
      ∀ s3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) s3)
    (hR1Range :
      ∀ s3 s5 : Term,
        r1 ≠ Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
    (hR1Allchar : r1 ≠ Term.UOp UserOp.re_allchar)
    (hR1Mult :
      ∀ r3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.re_mult) r3)
    (hFuelMult :
      ∀ r3 fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        r1 = Term.Apply (Term.UOp UserOp.re_mult) r3 ->
        False)
    (hLeftNotFalse :
      __eo_is_eq
          (__str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            r1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_is_eq
          (__str_membership_re
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hResidualRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1)
                r2))))
        (__smtx_model_eval M
          (__eo_to_smt
            (__str_re_consume_rec
              (__str_membership_str
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r1 fuel))
              r2 fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1)
              r2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideFallback :
      side =
        __str_re_consume_rec
          (__str_membership_str
            (__str_re_consume_rec
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              r1 fuel))
          r2 fuel := by
    rw [hSide,
      str_re_consume_rec_str_concat_re_concat_mem_epsilon_eq s1 s2 r1 r2
        fuel hFuel hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult
        hFuelMult hLeftNotFalse hMemEps]
  simpa [hSideFallback] using hResidualRel

theorem str_re_consume_rec_str_concat_re_range_mismatch_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 s5 r fuel side : Term)
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
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
            r)
          fuel)
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
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) =
        Term.Boolean false) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let range := Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) range) r
  rcases str_re_consume_translation_facts sConcat rConcat side (by
      simpa [sConcat, range, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hConcatTy, hRConcatTy, _hEqBool⟩
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hConcatTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt range) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt range) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [hRConcatTy]
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
      hS1Len with ⟨c, hS1Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s3
      hRangeArgs.1 hS3Len with ⟨lo, hS3Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s5
      hRangeArgs.2 hS5Len with ⟨hi, hS5Eq⟩
  have hCValidString : native_string_valid [c] = true := by
    have hStringTy :
        __smtx_typeof (__eo_to_smt (Term.String [c])) =
          SmtType.Seq SmtType.Char := by
      simpa [hS1Eq] using hS1Ty
    exact native_string_valid_of_smtx_typeof_eo_string [c] hStringTy
  subst s1
  subst s3
  subst s5
  have hRangeTySingleton :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_range) (Term.String [lo]))
              (Term.String [hi]))) =
        SmtType.RegLan := by
    simpa [range] using hRConcatArgs.1
  have hHeadFalse :
      native_str_in_re [c] (native_re_range [lo] [hi]) = false :=
    str_re_consume_range_head_native_eq_of_match_local M hM c lo hi false
      hCValidString hRangeTySingleton (by simpa using hMatch)
  have hSideFalse : side = Term.Boolean false := by
    rw [hSide,
      str_re_consume_rec_str_concat_re_range_mismatch_eq
        (Term.String [c]) s2 (Term.String [lo]) (Term.String [hi]) r
        fuel hFuel hLen hMatch]
  apply str_re_consume_model_rel_of_side_false M hM
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
      (Term.String [c])) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_range) (Term.String [lo]))
          (Term.String [hi])))
      r)
    side hEqTrans hSideFalse
  intro ss rv hSEval hREval
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    simpa [range] using hRConcatArgs.2
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range)
                    (Term.String [lo]))
                  (Term.String [hi])))
              r)) =
        SmtValue.RegLan
          (native_re_concat (native_re_range [lo] [hi]) rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.re_range (SmtTerm.String [lo]) (SmtTerm.String [hi]))
          (__eo_to_smt r)) =
      SmtValue.RegLan
        (native_re_concat (native_re_range [lo] [hi]) rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_re_range, hRTailEval,
     ]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  rw [native_unpack_string_pack_seq_concat_local]
  simp [native_unpack_string_pack_string]
  exact native_str_in_re_re_range_concat_singleton_left_false_local c lo hi
    (native_unpack_string ss2) rvTail hHeadFalse

theorem str_re_consume_rec_str_concat_str_to_re_len_mismatch_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 s3 r fuel side : Term)
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
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s3))
            r)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEqFalse : __eo_eq s1 s3 = Term.Boolean false)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) =
        Term.Boolean true) :
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
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let headRe := Term.Apply (Term.UOp UserOp.str_to_re) s3
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) headRe) r
  rcases str_re_consume_translation_facts sConcat rConcat side (by
      simpa [sConcat, headRe, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hConcatTy, hRConcatTy, _hEqBool⟩
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hConcatTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt headRe) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt headRe) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [hRConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt headRe) (__eo_to_smt r)) hNN
  have hS3Ty :
      __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char := by
    have hNN : term_has_non_none_type
        (SmtTerm.str_to_re (__eo_to_smt s3)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt headRe) ≠ SmtType.None
      rw [hRConcatArgs.1]
      simp
    exact seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
      (typeof_str_to_re_eq (__eo_to_smt s3)) hNN
  rcases eo_and_eq_true_local
      (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
      (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) hLen with
    ⟨hS1Len, hS3Len⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s1 hS1Ty
      hS1Len with ⟨c, hS1Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s3 hS3Ty
      hS3Len with ⟨d, hS3Eq⟩
  subst s1
  subst s3
  have hCharNe : c ≠ d := by
    intro hcd
    subst d
    simp [__eo_eq, native_teq] at hEqFalse
  have hSideFalse : side = Term.Boolean false := by
    rw [hSide,
      str_re_consume_rec_str_concat_str_to_re_len_mismatch_eq
        (Term.String [c]) s2 (Term.String [d]) r fuel hFuel hS3Ne
        hEqFalse hLen]
  apply str_re_consume_model_rel_of_side_false M hM
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
      (Term.String [c])) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [d])))
      r)
    side hEqTrans hSideFalse
  intro ss rv hSEval hREval
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    simpa [headRe] using hRConcatArgs.2
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hS2EvalTy with
    ⟨ss2, hS2Eval, hSs2Ty⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hHeadEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [d]))) =
        SmtValue.RegLan (native_str_to_re [d]) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [d])) =
      SmtValue.RegLan (native_str_to_re [d])
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
     ]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [d])))
              r)) =
        SmtValue.RegLan (native_re_concat (native_str_to_re [d]) rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.str_to_re (SmtTerm.String [d])) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat (native_str_to_re [d]) rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re, hRTailEval,
     ]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  rw [native_unpack_string_pack_seq_concat_local]
  simp [native_unpack_string_pack_string]
  exact native_str_in_re_str_to_re_concat_singleton_false_local c d
    (native_unpack_string ss2) rvTail hCharNe

theorem str_re_consume_model_rel_of_re_inter_all_right
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) r)
                (Term.UOp UserOp.re_all))))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hInterArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hInterArgs.1]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hAllEval :
      __smtx_model_eval M (__eo_to_smt all) =
        SmtValue.RegLan native_re_all := by
    change __smtx_model_eval M SmtTerm.re_all =
      SmtValue.RegLan native_re_all
    rw [__smtx_model_eval.eq_106]
  have hInterEval :
      __smtx_model_eval M (__eo_to_smt inter) =
        SmtValue.RegLan (native_re_inter rv native_re_all) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt r) (__eo_to_smt all)) =
      SmtValue.RegLan (native_re_inter rv native_re_all)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hAllEval,
      hREval]
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char (by
      have hsimpa := hSEvalTy; (try simp [hSEval] at hsimpa ⊢); exact hsimpa)
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_inter rv native_re_all) =
        native_str_in_re (native_unpack_string ss) rv := by
    rw [native_str_in_re_re_inter, native_str_in_re_re_all _ hValid]
    simp
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              inter)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt inter)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hInterEval, hREval,
      model_str_in_re_unpack_eq_string_of_value_type ss
        (native_re_inter rv native_re_all) hSsTy,
      model_str_in_re_unpack_eq_string_of_value_type ss rv hSsTy,
      hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_inter_all_left
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter)
                  (Term.UOp UserOp.re_all))
                r)))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter)
                (Term.UOp UserOp.re_all))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let all := Term.UOp UserOp.re_all
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) all) r
  rcases str_re_consume_translation_facts s inter side (by
      simpa [all, inter] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hInterTy, _hEqBool⟩
  have hInterArgs :
      __smtx_typeof (__eo_to_smt all) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_inter (__eo_to_smt all) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt inter) ≠ SmtType.None
      rw [hInterTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
      (typeof_re_inter_eq (__eo_to_smt all) (__eo_to_smt r)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hInterArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hInterArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hAllEval :
      __smtx_model_eval M (__eo_to_smt all) =
        SmtValue.RegLan native_re_all := by
    change __smtx_model_eval M SmtTerm.re_all =
      SmtValue.RegLan native_re_all
    rw [__smtx_model_eval.eq_106]
  have hInterEval :
      __smtx_model_eval M (__eo_to_smt inter) =
        SmtValue.RegLan (native_re_inter native_re_all rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt all) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_inter native_re_all rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hAllEval,
      hREval]
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char (by
      have hsimpa := hSEvalTy; (try simp [hSEval] at hsimpa ⊢); exact hsimpa)
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_inter native_re_all rv) =
        native_str_in_re (native_unpack_string ss) rv := by
    rw [native_str_in_re_re_inter, native_str_in_re_re_all _ hValid]
    simp
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              inter)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt inter)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hInterEval, hREval,
      model_str_in_re_unpack_eq_string_of_value_type ss
        (native_re_inter native_re_all rv) hSsTy,
      model_str_in_re_unpack_eq_string_of_value_type ss rv hSsTy,
      hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_union_none_right
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) r)
                (Term.UOp UserOp.re_none))))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.1]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hNoneEval :
      __smtx_model_eval M (__eo_to_smt none) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_105]
  have hUnionEval :
      __smtx_model_eval M (__eo_to_smt union) =
        SmtValue.RegLan (native_re_union rv native_re_none) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt r) (__eo_to_smt none)) =
      SmtValue.RegLan (native_re_union rv native_re_none)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hNoneEval,
      hREval]
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_union rv native_re_none) =
        native_str_in_re (native_unpack_string ss) rv := by
    rw [native_str_in_re_re_union, native_str_in_re_re_none]
    simp
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              union)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt union)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hUnionEval, hREval,
      model_str_in_re_unpack_eq_string_of_value_type ss
        (native_re_union rv native_re_none) hSsTy,
      model_str_in_re_unpack_eq_string_of_value_type ss rv hSsTy,
      hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_union_none_left
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union)
                  (Term.UOp UserOp.re_none))
                r)))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union)
                (Term.UOp UserOp.re_none))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let none := Term.UOp UserOp.re_none
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) none) r
  rcases str_re_consume_translation_facts s union side (by
      simpa [none, union] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hUnionTy, _hEqBool⟩
  have hUnionArgs :
      __smtx_typeof (__eo_to_smt none) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_union (__eo_to_smt none) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt union) ≠ SmtType.None
      rw [hUnionTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
      (typeof_re_union_eq (__eo_to_smt none) (__eo_to_smt r)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hNoneEval :
      __smtx_model_eval M (__eo_to_smt none) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_105]
  have hUnionEval :
      __smtx_model_eval M (__eo_to_smt union) =
        SmtValue.RegLan (native_re_union native_re_none rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt none) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_union native_re_none rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hNoneEval,
      hREval]
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_union native_re_none rv) =
        native_str_in_re (native_unpack_string ss) rv := by
    rw [native_str_in_re_re_union, native_str_in_re_re_none]
    simp
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              union)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt union)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hUnionEval, hREval,
      model_str_in_re_unpack_eq_string_of_value_type ss
        (native_re_union native_re_none rv) hSsTy,
      model_str_in_re_unpack_eq_string_of_value_type ss rv hSsTy,
      hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_union_left_false
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 left side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) c1) c2)))
          side))
    (hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
        (__smtx_model_eval M (__eo_to_smt left)))
    (hLeftEval :
      __smtx_model_eval M (__eo_to_smt left) = SmtValue.Boolean false)
    (hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) c1) c2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hC1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c1)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c1) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.1]
        simp)
  have hC2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c2)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c2) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hC1EvalTy with ⟨rv1, hC1Eval⟩
  rcases reglan_value_canonical hC2EvalTy with ⟨rv2, hC2Eval⟩
  have hC1StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv1) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c1)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv1)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC1Eval, hSsTy]
  have hC2StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv2) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c2)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv2)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC2Eval, hSsTy]
  have hLeftNativeFalse :
      native_str_in_re (native_unpack_string ss) rv1 = false :=
    smt_value_rel_boolean_eq_consume_local (by
      simpa [hC1StrEval, hLeftEval] using hLeftRel)
  have hUnionEval :
      __smtx_model_eval M (__eo_to_smt union) =
        SmtValue.RegLan (native_re_union rv1 rv2) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt c1) (__eo_to_smt c2)) =
      SmtValue.RegLan (native_re_union rv1 rv2)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hC1Eval,
      hC2Eval]
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              union)) =
        SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_union rv1 rv2)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt union)) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ss)
          (native_re_union rv1 rv2))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hUnionEval, hSsTy]
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_union rv1 rv2) =
        native_str_in_re (native_unpack_string ss) rv2 := by
    rw [native_str_in_re_re_union, hLeftNativeFalse]
    simp
  rw [hOrigEval, hNativeEq]
  simpa [hC2StrEval] using hRightRel

theorem str_re_consume_model_rel_of_re_union_right_false
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 right side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) c1) c2)))
          side))
    (hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
        (__smtx_model_eval M (__eo_to_smt side)))
    (hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
        (__smtx_model_eval M (__eo_to_smt right)))
    (hRightEval :
      __smtx_model_eval M (__eo_to_smt right) = SmtValue.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) c1) c2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hC1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c1)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c1) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.1]
        simp)
  have hC2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c2)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c2) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hC1EvalTy with ⟨rv1, hC1Eval⟩
  rcases reglan_value_canonical hC2EvalTy with ⟨rv2, hC2Eval⟩
  have hC1StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv1) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c1)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv1)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC1Eval, hSsTy]
  have hC2StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv2) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c2)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv2)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC2Eval, hSsTy]
  have hRightNativeFalse :
      native_str_in_re (native_unpack_string ss) rv2 = false :=
    smt_value_rel_boolean_eq_consume_local (by
      simpa [hC2StrEval, hRightEval] using hRightRel)
  have hUnionEval :
      __smtx_model_eval M (__eo_to_smt union) =
        SmtValue.RegLan (native_re_union rv1 rv2) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt c1) (__eo_to_smt c2)) =
      SmtValue.RegLan (native_re_union rv1 rv2)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hC1Eval,
      hC2Eval]
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              union)) =
        SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_union rv1 rv2)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt union)) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ss)
          (native_re_union rv1 rv2))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hUnionEval, hSsTy]
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_union rv1 rv2) =
        native_str_in_re (native_unpack_string ss) rv1 := by
    rw [native_str_in_re_re_union, hRightNativeFalse]
    simp
  rw [hOrigEval, hNativeEq]
  simpa [hC1StrEval] using hLeftRel

theorem str_re_consume_model_rel_of_re_union_same_branches
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 left right side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) c1) c2)))
          side))
    (hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
        (__smtx_model_eval M (__eo_to_smt left)))
    (hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
        (__smtx_model_eval M (__eo_to_smt right)))
    (hSideEq : side = left)
    (hSame : left = right) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) c1) c2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hC1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c1)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c1) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.1]
        simp)
  have hC2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c2)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c2) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hC1EvalTy with ⟨rv1, hC1Eval⟩
  rcases reglan_value_canonical hC2EvalTy with ⟨rv2, hC2Eval⟩
  let b1 := native_str_in_re (native_unpack_string ss) rv1
  let b2 := native_str_in_re (native_unpack_string ss) rv2
  have hC1StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)) =
        SmtValue.Boolean b1 := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c1)) =
      SmtValue.Boolean b1
    simp [b1, __smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC1Eval, hSsTy]
  have hC2StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)) =
        SmtValue.Boolean b2 := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c2)) =
      SmtValue.Boolean b2
    simp [b2, __smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC2Eval, hSsTy]
  have hBranchesSameBool : b1 = b2 := by
    apply smt_value_rel_boolean_eq_consume_local
    have hLeftRel' :
        RuleProofs.smt_value_rel (SmtValue.Boolean b1)
          (__smtx_model_eval M (__eo_to_smt left)) := by
      simpa [hC1StrEval] using hLeftRel
    have hRightRel' :
        RuleProofs.smt_value_rel (SmtValue.Boolean b2)
          (__smtx_model_eval M (__eo_to_smt left)) := by
      simpa [hC2StrEval, hSame] using hRightRel
    exact RuleProofs.smt_value_rel_trans _ _ _
      hLeftRel'
      (RuleProofs.smt_value_rel_symm _ _ hRightRel')
  have hUnionEval :
      __smtx_model_eval M (__eo_to_smt union) =
        SmtValue.RegLan (native_re_union rv1 rv2) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt c1) (__eo_to_smt c2)) =
      SmtValue.RegLan (native_re_union rv1 rv2)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hC1Eval,
      hC2Eval]
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              union)) =
        SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_union rv1 rv2)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt union)) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ss)
          (native_re_union rv1 rv2))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hUnionEval, hSsTy]
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_union rv1 rv2) = b1 := by
    rw [native_str_in_re_re_union]
    subst b1
    subst b2
    rw [hBranchesSameBool]
    cases native_str_in_re (native_unpack_string ss) rv2 <;> simp
  rw [hOrigEval, hNativeEq, hSideEq]
  simpa [hC1StrEval] using hLeftRel

theorem str_re_consume_model_rel_of_re_inter_left_false
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 left side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)))
          side))
    (hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
        (__smtx_model_eval M (__eo_to_smt left)))
    (hLeftEval :
      __smtx_model_eval M (__eo_to_smt left) = SmtValue.Boolean false)
    (hSideFalse : side = Term.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) c1) c2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hC1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c1)) =
        SmtType.RegLan := by
    simpa [hInterArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c1) (by
        unfold term_has_non_none_type
        rw [hInterArgs.1]
        simp)
  have hC2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c2)) =
        SmtType.RegLan := by
    simpa [hInterArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c2) (by
        unfold term_has_non_none_type
        rw [hInterArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hC1EvalTy with ⟨rv1, hC1Eval⟩
  rcases reglan_value_canonical hC2EvalTy with ⟨rv2, hC2Eval⟩
  have hC1StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv1) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c1)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv1)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC1Eval, hSsTy]
  have hLeftNativeFalse :
      native_str_in_re (native_unpack_string ss) rv1 = false :=
    smt_value_rel_boolean_eq_consume_local (by
      simpa [hC1StrEval, hLeftEval] using hLeftRel)
  have hInterEval :
      __smtx_model_eval M (__eo_to_smt inter) =
        SmtValue.RegLan (native_re_inter rv1 rv2) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt c1) (__eo_to_smt c2)) =
      SmtValue.RegLan (native_re_inter rv1 rv2)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hC1Eval,
      hC2Eval]
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              inter)) =
        SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_inter rv1 rv2)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt inter)) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ss)
          (native_re_inter rv1 rv2))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hInterEval, hSsTy]
  have hNativeFalse :
      native_str_in_re (native_unpack_string ss)
          (native_re_inter rv1 rv2) = false := by
    rw [native_str_in_re_re_inter, hLeftNativeFalse]
    simp
  rw [hOrigEval, hNativeFalse, hSideFalse]
  change RuleProofs.smt_value_rel (SmtValue.Boolean false)
    (__smtx_model_eval M (SmtTerm.Boolean false))
  rw [__smtx_model_eval.eq_1]
  exact RuleProofs.smt_value_rel_refl _

theorem str_re_consume_model_rel_of_re_inter_right_false
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 right side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)))
          side))
    (hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
        (__smtx_model_eval M (__eo_to_smt right)))
    (hRightEval :
      __smtx_model_eval M (__eo_to_smt right) = SmtValue.Boolean false)
    (hSideFalse : side = Term.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) c1) c2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hC1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c1)) =
        SmtType.RegLan := by
    simpa [hInterArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c1) (by
        unfold term_has_non_none_type
        rw [hInterArgs.1]
        simp)
  have hC2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c2)) =
        SmtType.RegLan := by
    simpa [hInterArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c2) (by
        unfold term_has_non_none_type
        rw [hInterArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hC1EvalTy with ⟨rv1, hC1Eval⟩
  rcases reglan_value_canonical hC2EvalTy with ⟨rv2, hC2Eval⟩
  have hC2StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv2) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c2)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv2)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC2Eval, hSsTy]
  have hRightNativeFalse :
      native_str_in_re (native_unpack_string ss) rv2 = false :=
    smt_value_rel_boolean_eq_consume_local (by
      simpa [hC2StrEval, hRightEval] using hRightRel)
  have hInterEval :
      __smtx_model_eval M (__eo_to_smt inter) =
        SmtValue.RegLan (native_re_inter rv1 rv2) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt c1) (__eo_to_smt c2)) =
      SmtValue.RegLan (native_re_inter rv1 rv2)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hC1Eval,
      hC2Eval]
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              inter)) =
        SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_inter rv1 rv2)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt inter)) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ss)
          (native_re_inter rv1 rv2))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hInterEval, hSsTy]
  have hNativeFalse :
      native_str_in_re (native_unpack_string ss)
          (native_re_inter rv1 rv2) = false := by
    rw [native_str_in_re_re_inter, hRightNativeFalse]
    cases native_str_in_re (native_unpack_string ss) rv1 <;> simp
  rw [hOrigEval, hNativeFalse, hSideFalse]
  change RuleProofs.smt_value_rel (SmtValue.Boolean false)
    (__smtx_model_eval M (SmtTerm.Boolean false))
  rw [__smtx_model_eval.eq_1]
  exact RuleProofs.smt_value_rel_refl _

theorem str_re_consume_model_rel_of_re_inter_same_branches
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 left right side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)))
          side))
    (hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)))
        (__smtx_model_eval M (__eo_to_smt left)))
    (hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)))
        (__smtx_model_eval M (__eo_to_smt right)))
    (hSideEq : side = left)
    (hSame : left = right) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) c1) c2))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2
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
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hC1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c1)) =
        SmtType.RegLan := by
    simpa [hInterArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c1) (by
        unfold term_has_non_none_type
        rw [hInterArgs.1]
        simp)
  have hC2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c2)) =
        SmtType.RegLan := by
    simpa [hInterArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c2) (by
        unfold term_has_non_none_type
        rw [hInterArgs.2]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hC1EvalTy with ⟨rv1, hC1Eval⟩
  rcases reglan_value_canonical hC2EvalTy with ⟨rv2, hC2Eval⟩
  let b1 := native_str_in_re (native_unpack_string ss) rv1
  let b2 := native_str_in_re (native_unpack_string ss) rv2
  have hC1StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c1)) =
        SmtValue.Boolean b1 := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c1)) =
      SmtValue.Boolean b1
    simp [b1, __smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC1Eval, hSsTy]
  have hC2StrEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) c2)) =
        SmtValue.Boolean b2 := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt c2)) =
      SmtValue.Boolean b2
    simp [b2, __smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hC2Eval, hSsTy]
  have hBranchesSameBool : b1 = b2 := by
    apply smt_value_rel_boolean_eq_consume_local
    have hLeftRel' :
        RuleProofs.smt_value_rel (SmtValue.Boolean b1)
          (__smtx_model_eval M (__eo_to_smt left)) := by
      simpa [hC1StrEval] using hLeftRel
    have hRightRel' :
        RuleProofs.smt_value_rel (SmtValue.Boolean b2)
          (__smtx_model_eval M (__eo_to_smt left)) := by
      simpa [hC2StrEval, hSame] using hRightRel
    exact RuleProofs.smt_value_rel_trans _ _ _
      hLeftRel'
      (RuleProofs.smt_value_rel_symm _ _ hRightRel')
  have hInterEval :
      __smtx_model_eval M (__eo_to_smt inter) =
        SmtValue.RegLan (native_re_inter rv1 rv2) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt c1) (__eo_to_smt c2)) =
      SmtValue.RegLan (native_re_inter rv1 rv2)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hC1Eval,
      hC2Eval]
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              inter)) =
        SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_inter rv1 rv2)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt inter)) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ss)
          (native_re_inter rv1 rv2))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hInterEval, hSsTy]
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_inter rv1 rv2) = b1 := by
    rw [native_str_in_re_re_inter]
    subst b1
    subst b2
    rw [hBranchesSameBool]
    cases native_str_in_re (native_unpack_string ss) rv2 <;> simp
  rw [hOrigEval, hNativeEq, hSideEq]
  simpa [hC1StrEval] using hLeftRel

theorem str_re_consume_inter_re_all_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_inter s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_inter) r)
          (Term.UOp UserOp.re_all))
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_inter] at hS hFuel ⊢

theorem str_re_consume_inter_left_false_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_all)
    (hLeftFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean true) :
    __str_re_consume_inter s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
        fuel =
      Term.Boolean false := by
  rw [__str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftFalse, eo_ite_true]

theorem str_re_consume_inter_no_epsilon_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_all)
    (hLeftNotFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemNotEps :
      __eo_eq
          (__str_membership_re (__str_re_consume_rec s c1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean false)
    (hRightNotFalse :
      __eo_is_eq (__str_re_consume_inter s c2 fuel)
          (Term.Boolean false) =
        Term.Boolean false) :
    __str_re_consume_inter s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
  rw [__str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftNotFalse, hMemNotEps, hRightNotFalse, eo_ite_false]

theorem str_re_consume_inter_right_false_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_all)
    (hLeftNotFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re (__str_re_consume_rec s c1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightFalse :
      __eo_is_eq (__str_re_consume_inter s c2 fuel)
          (Term.Boolean false) =
        Term.Boolean true) :
    __str_re_consume_inter s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
        fuel =
      Term.Boolean false := by
  rw [__str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftNotFalse, hMemEps, hRightFalse, eo_ite_true, eo_ite_false]

theorem str_re_consume_inter_same_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_all)
    (hLeftNotFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re (__str_re_consume_rec s c1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightNotFalse :
      __eo_is_eq (__str_re_consume_inter s c2 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hSame :
      __eo_eq (__str_re_consume_rec s c1 fuel)
          (__str_re_consume_inter s c2 fuel) =
        Term.Boolean true) :
    __str_re_consume_inter s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
        fuel =
      __str_re_consume_rec s c1 fuel := by
  rw [__str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftNotFalse, hMemEps, hRightNotFalse, hSame, eo_ite_true,
    eo_ite_false]

theorem str_re_consume_inter_fallback_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_all)
    (hLeftNotFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re (__str_re_consume_rec s c1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightNotFalse :
      __eo_is_eq (__str_re_consume_inter s c2 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hNotSame :
      __eo_eq (__str_re_consume_rec s c1 fuel)
          (__str_re_consume_inter s c2 fuel) =
        Term.Boolean false) :
    __str_re_consume_inter s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
  rw [__str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftNotFalse, hMemEps, hRightNotFalse, hNotSame, eo_ite_true,
    eo_ite_false]

theorem str_re_consume_union_re_none_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_union s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_union) r)
          (Term.UOp UserOp.re_none))
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_union] at hS hFuel ⊢

theorem str_re_consume_union_left_false_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_none)
    (hLeftFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean true) :
    __str_re_consume_union s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
        fuel =
      __str_re_consume_union s c2 fuel := by
  rw [__str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftFalse, eo_ite_true]

theorem str_re_consume_union_no_epsilon_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_none)
    (hLeftNotFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemNotEps :
      __eo_eq
          (__str_membership_re (__str_re_consume_rec s c1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean false) :
    __str_re_consume_union s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
  rw [__str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftNotFalse, hMemNotEps, eo_ite_false]

theorem str_re_consume_union_right_false_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_none)
    (hLeftNotFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re (__str_re_consume_rec s c1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightFalse :
      __eo_is_eq (__str_re_consume_union s c2 fuel)
          (Term.Boolean false) =
        Term.Boolean true) :
    __str_re_consume_union s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
        fuel =
      __str_re_consume_rec s c1 fuel := by
  rw [__str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftNotFalse, hMemEps, hRightFalse, eo_ite_true, eo_ite_false]

theorem str_re_consume_union_same_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_none)
    (hLeftNotFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re (__str_re_consume_rec s c1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightNotFalse :
      __eo_is_eq (__str_re_consume_union s c2 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hSame :
      __eo_eq (__str_re_consume_rec s c1 fuel)
          (__str_re_consume_union s c2 fuel) =
        Term.Boolean true) :
    __str_re_consume_union s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
        fuel =
      __str_re_consume_rec s c1 fuel := by
  rw [__str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftNotFalse, hMemEps, hRightNotFalse, hSame, eo_ite_true,
    eo_ite_false]

theorem str_re_consume_union_fallback_eq
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_none)
    (hLeftNotFalse :
      __eo_is_eq (__str_re_consume_rec s c1 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hMemEps :
      __eo_eq
          (__str_membership_re (__str_re_consume_rec s c1 fuel))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Boolean true)
    (hRightNotFalse :
      __eo_is_eq (__str_re_consume_union s c2 fuel)
          (Term.Boolean false) =
        Term.Boolean false)
    (hNotSame :
      __eo_eq (__str_re_consume_rec s c1 fuel)
          (__str_re_consume_union s c2 fuel) =
        Term.Boolean false) :
    __str_re_consume_union s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
        fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
  rw [__str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
  simp [hLeftNotFalse, hMemEps, hRightNotFalse, hNotSame, eo_ite_true,
    eo_ite_false]

theorem str_re_consume_inter_re_all_model_rel
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
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) r)
              (Term.UOp UserOp.re_all)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_inter_re_all_eq s r fuel hS hFuel]
  apply str_re_consume_model_rel_of_re_inter_all_right M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_union_re_none_model_rel
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
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) r)
              (Term.UOp UserOp.re_none)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_union_re_none_eq s r fuel hS hFuel]
  apply str_re_consume_model_rel_of_re_union_none_right M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_inter_re_all_left_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter)
                  (Term.UOp UserOp.re_all))
                r)))
          side))
    (_hSide :
      side =
        __str_re_consume_inter s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter)
              (Term.UOp UserOp.re_all))
            r)
          fuel)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter)
                (Term.UOp UserOp.re_all))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  exact str_re_consume_model_rel_of_re_inter_all_left M hM s r side
    hEqTrans hReducedRel

theorem str_re_consume_union_re_none_left_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union)
                  (Term.UOp UserOp.re_none))
                r)))
          side))
    (_hSide :
      side =
        __str_re_consume_union s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union)
              (Term.UOp UserOp.re_none))
            r)
          fuel)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union)
                (Term.UOp UserOp.re_none))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  exact str_re_consume_model_rel_of_re_union_none_left M hM s r side
    hEqTrans hReducedRel

theorem str_re_consume_rec_re_inter_all_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_inter) r)
          (Term.UOp UserOp.re_all))
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec, __str_re_consume_inter] at hS hFuel ⊢

theorem str_re_consume_rec_re_inter_eq
    (s r1 r2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r1) r2)
        fuel =
      __str_re_consume_inter s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r1) r2)
        fuel := by
  exact __str_re_consume_rec.eq_12 s fuel r1 r2 hS hFuel

theorem str_re_consume_rec_re_union_none_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_union) r)
          (Term.UOp UserOp.re_none))
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec, __str_re_consume_union] at hS hFuel ⊢

theorem str_re_consume_rec_re_union_eq
    (s r1 r2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r1) r2)
        fuel =
      __str_re_consume_union s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r1) r2)
        fuel := by
  exact __str_re_consume_rec.eq_13 s fuel r1 r2 hS hFuel

theorem str_re_consume_rec_re_inter_all_model_rel
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
        __str_re_consume_rec s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter) r)
            (Term.UOp UserOp.re_all))
          fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) r)
              (Term.UOp UserOp.re_all)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_rec_re_inter_all_eq s r fuel hS hFuel]
  apply str_re_consume_model_rel_of_re_inter_all_right M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_re_union_none_model_rel
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
        __str_re_consume_rec s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union) r)
            (Term.UOp UserOp.re_none))
          fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) r)
              (Term.UOp UserOp.re_none)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_rec_re_union_none_eq s r fuel hS hFuel]
  apply str_re_consume_model_rel_of_re_union_none_right M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_default_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotRConcatEmpty :
      ∀ r2 : Term,
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
            r2 ->
        False)
    (hNotRInter :
      ∀ r1 r2 : Term,
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r1) r2 ->
        False)
    (hNotRUnion :
      ∀ r1 r2 : Term,
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r1) r2 ->
        False)
    (hNotStrConcatEmpty :
      ∀ s1 s2 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
            r2 ->
        False)
    (hNotStrConcatStrToRe :
      ∀ s1 s2 s3 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s3)) r2 ->
        False)
    (hNotStrConcatRange :
      ∀ s1 s2 s3 s5 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
            r2 ->
        False)
    (hNotStrConcatAllchar :
      ∀ s1 s2 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.UOp UserOp.re_allchar)) r2 ->
        False)
    (hNotStrConcatMult :
      ∀ s1 s2 r3 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3)) r2 ->
        False)
    (hNotStrConcatConcat :
      ∀ s1 s2 r1 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2 ->
        False)
    (hNotStrConcatMultFuel :
      ∀ s1 s2 r3 r2 fc fr : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3)) r2 ->
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        False) :
    __str_re_consume_rec s r fuel =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
  exact __str_re_consume_rec.eq_14 s r fuel hS hR hNotRConcatEmpty
    hNotRInter hNotRUnion hNotStrConcatEmpty hNotStrConcatStrToRe
    hNotStrConcatRange hNotStrConcatAllchar hNotStrConcatMult
    hNotStrConcatConcat hFuel hNotStrConcatMultFuel

theorem str_re_consume_rec_default_model_rel
    (M : SmtModel)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSide : side = __str_re_consume_rec s r fuel)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotRConcatEmpty :
      ∀ r2 : Term,
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
            r2 ->
        False)
    (hNotRInter :
      ∀ r1 r2 : Term,
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r1) r2 ->
        False)
    (hNotRUnion :
      ∀ r1 r2 : Term,
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r1) r2 ->
        False)
    (hNotStrConcatEmpty :
      ∀ s1 s2 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
            r2 ->
        False)
    (hNotStrConcatStrToRe :
      ∀ s1 s2 s3 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s3)) r2 ->
        False)
    (hNotStrConcatRange :
      ∀ s1 s2 s3 s5 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
            r2 ->
        False)
    (hNotStrConcatAllchar :
      ∀ s1 s2 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.UOp UserOp.re_allchar)) r2 ->
        False)
    (hNotStrConcatMult :
      ∀ s1 s2 r3 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3)) r2 ->
        False)
    (hNotStrConcatConcat :
      ∀ s1 s2 r1 r2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2 ->
        False)
    (hNotStrConcatMultFuel :
      ∀ s1 s2 r3 r2 fc fr : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2 ->
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3)) r2 ->
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        False) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M s r side
  rw [hSide]
  exact str_re_consume_rec_default_eq s r fuel hS hR hFuel
    hNotRConcatEmpty hNotRInter hNotRUnion hNotStrConcatEmpty
    hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
    hNotStrConcatMult hNotStrConcatConcat hNotStrConcatMultFuel

theorem str_re_consume_rec_stuck_left_absurd
    (r fuel side : Term)
    (hSide : side = __str_re_consume_rec Term.Stuck r fuel)
    (hSideNe : side ≠ Term.Stuck) :
    False := by
  apply hSideNe
  rw [hSide]
  cases r <;> cases fuel <;> simp [__str_re_consume_rec]

theorem str_re_consume_rec_stuck_right_absurd
    (s fuel side : Term)
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume_rec s Term.Stuck fuel)
    (hSideNe : side ≠ Term.Stuck) :
    False := by
  apply hSideNe
  rw [hSide]
  cases s <;> simp [__str_re_consume_rec] at hS ⊢

theorem str_re_consume_rec_stuck_fuel_absurd
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck)
    (hSide : side = __str_re_consume_rec s r Term.Stuck)
    (hSideNe : side ≠ Term.Stuck) :
    False := by
  apply hSideNe
  rw [hSide]
  cases s <;> cases r <;> simp [__str_re_consume_rec] at hS hR ⊢

theorem str_re_consume_union_stuck_left_absurd
    (r fuel side : Term)
    (hSide : side = __str_re_consume_union Term.Stuck r fuel)
    (hSideNe : side ≠ Term.Stuck) :
    False := by
  apply hSideNe
  rw [hSide]
  cases r <;> cases fuel <;> simp [__str_re_consume_union]

theorem str_re_consume_union_stuck_fuel_absurd
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume_union s r Term.Stuck)
    (hSideNe : side ≠ Term.Stuck) :
    False := by
  apply hSideNe
  rw [hSide]
  cases s <;> simp [__str_re_consume_union] at hS ⊢

theorem str_re_consume_inter_stuck_left_absurd
    (r fuel side : Term)
    (hSide : side = __str_re_consume_inter Term.Stuck r fuel)
    (hSideNe : side ≠ Term.Stuck) :
    False := by
  apply hSideNe
  rw [hSide]
  cases r <;> cases fuel <;> simp [__str_re_consume_inter]

theorem str_re_consume_inter_stuck_fuel_absurd
    (s r side : Term)
    (hS : s ≠ Term.Stuck)
    (hSide : side = __str_re_consume_inter s r Term.Stuck)
    (hSideNe : side ≠ Term.Stuck) :
    False := by
  apply hSideNe
  rw [hSide]
  cases s <;> simp [__str_re_consume_inter] at hS ⊢

theorem str_re_consume_union_default_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotUnionNone :
      ∀ c1 : Term,
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union) c1)
            (Term.UOp UserOp.re_none) ->
        False)
    (hNotUnion :
      ∀ c1 c2 : Term,
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
        False) :
    __str_re_consume_union s r fuel = Term.Stuck := by
  exact __str_re_consume_union.eq_5 s r fuel hS hNotUnionNone
    hNotUnion hFuel

theorem str_re_consume_inter_default_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotInterAll :
      ∀ c1 : Term,
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter) c1)
            (Term.UOp UserOp.re_all) ->
        False)
    (hNotInter :
      ∀ c1 c2 : Term,
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
        False) :
    __str_re_consume_inter s r fuel = Term.Stuck := by
  exact __str_re_consume_inter.eq_5 s r fuel hS hNotInterAll
    hNotInter hFuel

theorem str_re_consume_union_default_absurd
    (s r fuel side : Term)
    (hSide : side = __str_re_consume_union s r fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotUnionNone :
      ∀ c1 : Term,
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union) c1)
            (Term.UOp UserOp.re_none) ->
        False)
    (hNotUnion :
      ∀ c1 c2 : Term,
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
        False) :
    False := by
  apply hSideNe
  rw [hSide]
  exact str_re_consume_union_default_eq s r fuel hS hFuel
    hNotUnionNone hNotUnion

theorem str_re_consume_inter_default_absurd
    (s r fuel side : Term)
    (hSide : side = __str_re_consume_inter s r fuel)
    (hSideNe : side ≠ Term.Stuck)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotInterAll :
      ∀ c1 : Term,
        r =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter) c1)
            (Term.UOp UserOp.re_all) ->
        False)
    (hNotInter :
      ∀ c1 c2 : Term,
        r = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
        False) :
    False := by
  apply hSideNe
  rw [hSide]
  exact str_re_consume_inter_default_eq s r fuel hS hFuel
    hNotInterAll hNotInter

end RuleProofs
