module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport
public import Cpc.Proofs.RuleSupport.RegexValueSupport
import all Cpc.Proofs.RuleSupport.RegexValueSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReInterCstringProof

abbrev reInter (x ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) ys

abbrev lhs (x ys s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.re_inter)
      (Term.Apply (Term.UOp UserOp.str_to_re) s))
    (reInter x ys)

abbrev rhs (s : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) s

abbrev prem (s x ys : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (lhs x ys s)))
    (Term.Boolean true)

abbrev concl (x ys s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs x ys s)) (rhs s)

theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not,
        SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

theorem eo_eq_eq_true {t s : Term} (h : __eo_eq t s = Term.Boolean true) :
    s = t := by
  unfold __eo_eq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Term.Boolean.injEq, native_teq] at h
    exact of_decide_eq_true h

theorem eo_and_eq_true {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  unfold __eo_and at h
  split at h
  · rename_i b1 b2
    simp only [Term.Boolean.injEq, SmtEval.native_and, Bool.and_eq_true] at h
    exact ⟨by rw [h.1], by rw [h.2]⟩
  · rename_i w1 n1 w2 n2
    simp only [__eo_requires, native_ite] at h
    split at h
    · split at h <;> exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem eqs_of_eo_and4_eq_true
    (x1 y1 x2 y2 x3 y3 x4 y4 : Term)
    (h :
      __eo_and
          (__eo_and (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) =
        Term.Boolean true) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  rcases eo_and_eq_true h with ⟨h123, h4⟩
  rcases eo_and_eq_true h123 with ⟨h12, h3⟩
  rcases eo_and_eq_true h12 with ⟨h1, h2⟩
  exact ⟨eo_eq_eq_true h1, eo_eq_eq_true h2, eo_eq_eq_true h3,
    eo_eq_eq_true h4⟩

theorem eo_typeof_re_concat_ne_stuck_args_reglan (A B : Term)
    (h : __eo_typeof_re_concat A B ≠ Term.Stuck) :
    A = Term.UOp UserOp.RegLan ∧ B = Term.UOp UserOp.RegLan := by
  cases A with
  | UOp opA =>
      cases opA <;> cases B with
      | UOp opB => cases opB <;> simp [__eo_typeof_re_concat] at h ⊢
      | _ => simp [__eo_typeof_re_concat] at h
  | _ => cases B <;> simp [__eo_typeof_re_concat] at h

theorem eo_typeof_re_concat_eq_reglan_args_reglan (A B : Term)
    (h : __eo_typeof_re_concat A B = Term.UOp UserOp.RegLan) :
    A = Term.UOp UserOp.RegLan ∧ B = Term.UOp UserOp.RegLan := by
  exact eo_typeof_re_concat_ne_stuck_args_reglan A B (by rw [h]; simp)

theorem eo_typeof_str_to_re_eq_seq_char_of_reglan (T : Term)
    (h : __eo_typeof_str_to_re T = Term.UOp UserOp.RegLan) :
    T = Term.Apply Term.Seq Term.Char := by
  have hNe : __eo_typeof_str_to_re T ≠ Term.Stuck := by
    rw [h]
    simp
  cases T with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_to_re] at hNe ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_to_re] at hNe ⊢
            | _ => simp [__eo_typeof_str_to_re] at hNe
      | _ => simp [__eo_typeof_str_to_re] at hNe
  | _ => simp [__eo_typeof_str_to_re] at hNe

theorem prog_form (x ys s P : Term)
    (hNe : __eo_prog_re_inter_cstring x ys s (Proof.pf P) ≠ Term.Stuck) :
    P = prem s x ys ∧
      __eo_prog_re_inter_cstring x ys s (Proof.pf P) = concl x ys s := by
  unfold __eo_prog_re_inter_cstring at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i hPrem
    injection hPrem with hPremEq
    have hReqArg := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    rcases eqs_of_eo_and4_eq_true _ _ _ _ _ _ _ _ hReqArg with
      ⟨hs2, hs3, hx, hys⟩
    rw [hs2, hs3, hx, hys] at hPremEq
    exact ⟨hPremEq, hReqEq⟩
  · exact False.elim (hNe rfl)

private theorem smtx_typeof_str_to_re_of_seq_char
    (s : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (rhs s)) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) = SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hSTy, native_ite, native_Teq]

theorem typed_concl
    (x ys s : Term)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (concl x ys s) := by
  have hStrToReTy :
      __smtx_typeof (__eo_to_smt (rhs s)) = SmtType.RegLan :=
    smtx_typeof_str_to_re_of_seq_char s hSTy
  have hStrToReSmtTy :
      __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) = SmtType.RegLan := by
    have hsimpa := hStrToReTy
    try simp at hsimpa ⊢
    exact hsimpa
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (reInter x ys)) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys)) =
      SmtType.RegLan
    rw [typeof_re_inter_eq]
    simp [hXTy, hYsTy, native_ite, native_Teq]
  have hInnerSmtTy :
      __smtx_typeof (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys)) =
        SmtType.RegLan := by
    simpa using hInnerTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs x ys s)) = SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_inter
          (SmtTerm.str_to_re (__eo_to_smt s))
          (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys))) =
      SmtType.RegLan
    rw [typeof_re_inter_eq]
    simp [hStrToReSmtTy, hInnerSmtTy, native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs x ys s) (rhs s)
    (by rw [hLhsTy, hStrToReTy]) (by rw [hLhsTy]; simp)

private theorem rest_str_in_re_true_of_prem
    (M : SmtModel) (s x ys : Term) (ss : SmtSeq)
    (xv ysv : SmtRegLan)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hXEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan xv)
    (hYsEval : __smtx_model_eval M (__eo_to_smt ys) = SmtValue.RegLan ysv)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hPrem : eo_interprets M (prem s x ys) true) :
    native_str_in_re (native_unpack_string ss) (native_re_inter xv ysv) = true := by
  have hUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) (lhs x ys s))
      (Term.Boolean true) hPrem
  have hInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (lhs x ys s))) =
        SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_inter (native_str_to_re (native_unpack_string ss))
              (native_re_inter xv ysv))) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s)
          (SmtTerm.re_inter
            (SmtTerm.str_to_re (__eo_to_smt s))
            (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys)))) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ss)
          (native_re_inter (native_str_to_re (native_unpack_string ss))
            (native_re_inter xv ysv)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
      __smtx_model_eval_str_to_re, __smtx_model_eval_re_inter, hSEval,
      hXEval, hYsEval, hUnpack]
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hInEval, hTrueEval] at hPremRel
  have hValueEq :
      SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_inter (native_str_to_re (native_unpack_string ss))
              (native_re_inter xv ysv))) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  have hFull :
      native_str_in_re (native_unpack_string ss)
          (native_re_inter (native_str_to_re (native_unpack_string ss))
            (native_re_inter xv ysv)) =
        true := by
    injection hValueEq
  rw [RuleProofs.model_str_in_re_re_inter] at hFull
  cases hRest : native_str_in_re (native_unpack_string ss)
      (native_re_inter xv ysv)
  · cases hSg :
        native_str_in_re (native_unpack_string ss)
          (native_str_to_re (native_unpack_string ss)) <;>
      simp [hRest, hSg] at hFull
  · rfl

private theorem smt_value_rel_inter_cstring
    (pat : native_String) (xv ysv : SmtRegLan)
    (hPatValid : native_string_valid pat = true)
    (hRestMem :
      RuleProofs.native_str_in_re pat (native_re_inter xv ysv) = true) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter (native_str_to_re pat) (native_re_inter xv ysv)))
      (SmtValue.RegLan (native_str_to_re pat)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_inter (native_str_to_re pat) (native_re_inter xv ysv))
        (native_str_to_re pat)) =
    SmtValue.Boolean true
  congr
  simp
  intro str hValid
  simp only [← RuleProofs.native_str_in_re_eq_model]
  rw [RuleProofs.native_str_in_re_re_inter]
  cases hSg : RuleProofs.native_str_in_re str (native_str_to_re pat)
  · simp [hSg]
  · have hStrEq : str = pat :=
      RuleProofs.native_str_in_re_str_to_re_eq hValid hSg
    have hRest :
        RuleProofs.native_str_in_re str (native_re_inter xv ysv) = true := by
      simpa [hStrEq] using hRestMem
    simp [hSg, hRest]

theorem facts
    (M : SmtModel) (hM : model_wf M) (x ys s : Term)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hPrem : eo_interprets M (prem s x ys) true) :
    eo_interprets M (concl x ys s) true := by
  have hBool : RuleProofs.eo_has_bool_type (concl x ys s) :=
    typed_concl x ys s hXTy hYsTy hSTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.RegLan := by
    simpa [hXTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXTy]
        simp)
  have hYsEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt ys)) =
        SmtType.RegLan := by
    simpa [hYsTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt ys) (by
        unfold term_has_non_none_type
        rw [hYsTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases reglan_value_canonical hXEvalTy with ⟨xv, hXEval⟩
  rcases reglan_value_canonical hYsEvalTy with ⟨ysv, hYsEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hSEval, __smtx_typeof_value] using hSEvalTy
  have hPatValid : native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSsTy
  have hSUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  have hRestMem :
      RuleProofs.native_str_in_re (native_unpack_string ss)
          (native_re_inter xv ysv) = true := by
    rw [RuleProofs.native_str_in_re_eq_model]
    exact rest_str_in_re_true_of_prem M s x ys ss xv ysv hSEval hXEval hYsEval
      hSsTy hPrem
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs x ys s)) =
        SmtValue.RegLan
          (native_re_inter (native_str_to_re (native_unpack_string ss))
            (native_re_inter xv ysv)) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter
          (SmtTerm.str_to_re (__eo_to_smt s))
          (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys))) =
      SmtValue.RegLan
        (native_re_inter (native_str_to_re (native_unpack_string ss))
          (native_re_inter xv ysv))
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
      __smtx_model_eval_re_inter, hSEval, hXEval, hYsEval, hSUnpack]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (rhs s)) =
        SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) := by
    change __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt s)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss))
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hSEval, hSUnpack]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs x ys s) (rhs s) hBool <| by
    rw [hLhsEval, hRhsEval]
    exact smt_value_rel_inter_cstring
      (native_unpack_string ss) xv ysv hPatValid hRestMem

end ReInterCstringProof
