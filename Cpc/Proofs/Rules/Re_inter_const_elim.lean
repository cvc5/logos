module

public import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import all Cpc.Proofs.RuleSupport.RegexRewriteSupport

open Eo
open SmtEval
open Smtm

-- Keep string coercions on the model's explicit string-to-value embedding.
attribute [-instance] List.instMonad List.instAlternativeMonad_mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReInterConstElimProof

private abbrev prem (s r : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
    (Term.Boolean true)

private abbrev inner (r ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) ys

private abbrev red (ys s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.re_inter)
      (Term.Apply (Term.UOp UserOp.str_to_re) s))
    ys

private abbrev lhs (r ys s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.re_inter)
      (Term.Apply (Term.UOp UserOp.str_to_re) s))
    (inner r ys)

private abbrev rhs (ys s : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_inter) (red ys s)

private abbrev concl (r ys s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs r ys s)) (rhs ys s)

private abbrev mkConcl (r ys s : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) (lhs r ys s)) (rhs ys s)

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
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

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_eq_eq_true {t s : Term} (h : __eo_eq t s = Term.Boolean true) :
    s = t := by
  unfold __eo_eq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Term.Boolean.injEq, native_teq] at h
    exact of_decide_eq_true h

private theorem eo_and_eq_true {x y : Term}
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

private theorem eqs_of_eo_and2_eq_true
    (x1 y1 x2 y2 : Term)
    (h : __eo_and (__eo_eq x1 y1) (__eo_eq x2 y2) =
        Term.Boolean true) :
    y1 = x1 ∧ y2 = x2 := by
  rcases eo_and_eq_true h with ⟨h1, h2⟩
  exact ⟨eo_eq_eq_true h1, eo_eq_eq_true h2⟩

private theorem eo_typeof_re_concat_ne_stuck_args_reglan (A B : Term)
    (h : __eo_typeof_re_concat A B ≠ Term.Stuck) :
    A = Term.UOp UserOp.RegLan ∧ B = Term.UOp UserOp.RegLan := by
  cases A with
  | UOp opA =>
      cases opA <;> cases B with
      | UOp opB => cases opB <;> simp [__eo_typeof_re_concat] at h ⊢
      | _ => simp [__eo_typeof_re_concat] at h
  | _ => cases B <;> simp [__eo_typeof_re_concat] at h

private theorem eo_typeof_re_concat_eq_reglan_args_reglan (A B : Term)
    (h : __eo_typeof_re_concat A B = Term.UOp UserOp.RegLan) :
    A = Term.UOp UserOp.RegLan ∧ B = Term.UOp UserOp.RegLan := by
  exact eo_typeof_re_concat_ne_stuck_args_reglan A B (by rw [h]; simp)

private theorem eo_typeof_str_to_re_eq_seq_char_of_reglan (T : Term)
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

private theorem prog_form (r ys s P : Term)
    (hNe : __eo_prog_re_inter_const_elim r ys s (Proof.pf P) ≠ Term.Stuck) :
    P = prem s r ∧
      __eo_prog_re_inter_const_elim r ys s (Proof.pf P) = mkConcl r ys s := by
  unfold __eo_prog_re_inter_const_elim at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i hPrem
    injection hPrem with hPremEq
    dsimp only at hNe ⊢
    have hReqArg := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    rcases eqs_of_eo_and2_eq_true _ _ _ _ hReqArg with ⟨hs, hr⟩
    rw [hs, hr] at hPremEq
    exact ⟨hPremEq, hReqEq⟩
  · exact False.elim (hNe rfl)

private theorem smtx_typeof_str_to_re_of_seq_char
    (s : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) = SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hSTy, native_ite, native_Teq]

private theorem smtx_typeof_re_inter_of_args (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y)) =
      SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_inter_eq]
  simp [hx, hy, native_ite, native_Teq]

private theorem str_in_re_true_of_prem
    (M : SmtModel) (s r : Term) (ss : SmtSeq) (rv : SmtRegLan)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hPrem : eo_interprets M (prem s r) true) :
    native_str_in_re (native_unpack_string ss) rv = true := by
  have hUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)
      (Term.Boolean true) hPrem
  have hInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval, hREval,
      hUnpack]
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hInEval, hTrueEval] at hPremRel
  have hValueEq :
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  injection hValueEq

private theorem smt_value_rel_inter_const_elim
    (pat : native_String) (rv rys : SmtRegLan)
    (hPatValid : native_string_valid pat = true)
    (hPatMem : RuleProofs.native_str_in_re pat rv = true) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter (native_str_to_re pat)
          (native_re_inter rv rys)))
      (SmtValue.RegLan (native_re_inter (native_str_to_re pat) rys)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_inter (native_str_to_re pat)
          (native_re_inter rv rys))
        (native_re_inter (native_str_to_re pat) rys)) =
    SmtValue.Boolean true
  congr
  simp
  intro str hValid
  simp only [← RuleProofs.native_str_in_re_eq_model]
  simp only [RuleProofs.native_str_in_re_re_inter]
  cases hSg : RuleProofs.native_str_in_re str (native_str_to_re pat)
  · simp
  · have hStrEq : str = pat :=
      RuleProofs.native_str_in_re_str_to_re_eq hValid (by
        simpa [impl_native_string_to_values, List.map_eq_flatMap] using hSg)
    subst hStrEq
    simp [hPatMem]

private theorem reInter_list_smt_typeof_reglan_of_non_none (t : Term) :
    __eo_is_list (Term.UOp UserOp.re_inter) t = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan := by
  intro hList hNN
  cases t <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at hList ⊢
  next op =>
    cases op <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, __smtx_typeof] at hList ⊢
  next f y =>
    cases f <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList ⊢
    next g x =>
      rw [← hList.1] at hNN ⊢
      have hArgs :
          __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
            __smtx_typeof (__eo_to_smt y) = SmtType.RegLan :=
        reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
          (typeof_re_inter_eq (__eo_to_smt x) (__eo_to_smt y)) hNN
      change __smtx_typeof
          (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan
      rw [typeof_re_inter_eq]
      simp [hArgs.1, hArgs.2, native_ite, native_Teq]

private theorem type_and_facts
    (M : SmtModel) (hM : model_wf M) (r ys s : Term)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hRedList :
      __eo_is_list (Term.UOp UserOp.re_inter) (red ys s) =
        Term.Boolean true) :
    RuleProofs.eo_has_bool_type (concl r ys s) ∧
      (eo_interprets M (prem s r) true ->
        eo_interprets M (concl r ys s) true) := by
  have hStrToReTy := smtx_typeof_str_to_re_of_seq_char s hSTy
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (inner r ys)) = SmtType.RegLan :=
    smtx_typeof_re_inter_of_args r ys hRTy hYsTy
  have hRedTy :
      __smtx_typeof (__eo_to_smt (red ys s)) = SmtType.RegLan :=
    smtx_typeof_re_inter_of_args _ _ hStrToReTy hYsTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs r ys s)) = SmtType.RegLan :=
    smtx_typeof_re_inter_of_args _ _ hStrToReTy hInnerTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs ys s)) = SmtType.RegLan :=
    RuleProofs.reInter_singleton_elim_has_reglan_type
      (red ys s) hRedList hRedTy
  have hBool : RuleProofs.eo_has_bool_type (concl r ys s) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs r ys s) (rhs ys s)
      (by rw [hLhsTy, hRhsTy])
      (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  intro hPrem
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM r hRTy with
    ⟨rv, hREval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM ys hYsTy with
    ⟨rys, hYsEval⟩
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hSEval, __smtx_typeof_value] using hSEvalTy
  have hPatValid : native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSsTy
  have hPatMem :
      RuleProofs.native_str_in_re (native_unpack_string ss) rv = true := by
    rw [RuleProofs.native_str_in_re_eq_model]
    exact str_in_re_true_of_prem M s r ss rv hSEval hREval hSsTy hPrem
  have hSUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  have hRedEval :
      __smtx_model_eval M (__eo_to_smt (red ys s)) =
        SmtValue.RegLan
          (native_re_inter (native_str_to_re (native_unpack_string ss)) rys) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (SmtTerm.str_to_re (__eo_to_smt s))
          (__eo_to_smt ys)) = _
    simp [hSUnpack, __smtx_model_eval, __smtx_model_eval_str_to_re,
      __smtx_model_eval_re_inter, hSEval, hYsEval]
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs r ys s)) =
        SmtValue.RegLan
          (native_re_inter (native_str_to_re (native_unpack_string ss))
            (native_re_inter rv rys)) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter
          (SmtTerm.str_to_re (__eo_to_smt s))
          (SmtTerm.re_inter (__eo_to_smt r) (__eo_to_smt ys))) = _
    simp [hSUnpack, __smtx_model_eval, __smtx_model_eval_str_to_re,
      __smtx_model_eval_re_inter, hSEval, hREval, hYsEval]
  have hRhsRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (rhs ys s)))
        (SmtValue.RegLan
          (native_re_inter (native_str_to_re (native_unpack_string ss)) rys)) := by
    rw [← hRedEval]
    exact RuleProofs.reInter_singleton_elim_rel_eval M (red ys s)
      hRedList ⟨_, hRedEval⟩
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs r ys s) (rhs ys s) hBool <| by
    rw [hLhsEval]
    exact RuleProofs.smt_value_rel_trans _ _ _
      (smt_value_rel_inter_const_elim
        (native_unpack_string ss) rv rys hPatValid hPatMem)
      (RuleProofs.smt_value_rel_symm _ _ hRhsRel)

end ReInterConstElimProof

public theorem cmd_step_re_inter_const_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_const_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_inter_const_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_const_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_inter_const_elim args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons a1 args =>
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons a2 args =>
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons a3 args =>
  cases args with
  | cons _ _ => exact False.elim (hProg rfl)
  | nil =>
  cases premises with
  | nil => exact False.elim (hProg rfl)
  | cons n premises =>
  cases premises with
  | cons _ _ => exact False.elim (hProg rfl)
  | nil =>
  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
  have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
  show StepRuleProperties M [__eo_state_proven_nth s n]
    (__eo_prog_re_inter_const_elim a1 a2 a3
      (Proof.pf (__eo_state_proven_nth s n)))
  generalize hP : __eo_state_proven_nth s n = P
  have hProgNe :
      __eo_prog_re_inter_const_elim a1 a2 a3 (Proof.pf P) ≠ Term.Stuck := by
    rw [← hP]
    exact hProg
  have hResultTyProg :
      __eo_typeof (__eo_prog_re_inter_const_elim a1 a2 a3 (Proof.pf P)) =
        Term.Bool := by
    rw [← hP]
    exact hResultTy
  obtain ⟨hPShape, hProgMk⟩ :=
    ReInterConstElimProof.prog_form a1 a2 a3 P hProgNe
  have hMkNe : ReInterConstElimProof.mkConcl a1 a2 a3 ≠ Term.Stuck := by
    rw [← hProgMk]
    exact hProgNe
  have hRhsNe : ReInterConstElimProof.rhs a2 a3 ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMkNe
  have hProgEq :
      __eo_prog_re_inter_const_elim a1 a2 a3 (Proof.pf P) =
        ReInterConstElimProof.concl a1 a2 a3 := by
    rw [hProgMk]
    exact eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe
  have hRedList :
      __eo_is_list (Term.UOp UserOp.re_inter)
          (ReInterConstElimProof.red a2 a3) = Term.Boolean true :=
    RuleProofs.reInter_singleton_elim_list_of_ne_stuck _ hRhsNe
  have hYsList :
      __eo_is_list (Term.UOp UserOp.re_inter) a2 = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_inter)
      (Term.Apply (Term.UOp UserOp.str_to_re) a3) a2 hRedList
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.RegLan :=
    ReInterConstElimProof.reInter_list_smt_typeof_reglan_of_non_none a2
      hYsList (by simpa [RuleProofs.eo_has_smt_translation] using hA2Trans)
  have hConclTy :
      __eo_typeof (ReInterConstElimProof.concl a1 a2 a3) = Term.Bool := by
    rw [hProgEq] at hResultTyProg
    exact hResultTyProg
  change __eo_typeof_eq
      (__eo_typeof (ReInterConstElimProof.lhs a1 a2 a3))
      (__eo_typeof (ReInterConstElimProof.rhs a2 a3)) =
    Term.Bool at hConclTy
  have hLhsNotStuck :
      __eo_typeof (ReInterConstElimProof.lhs a1 a2 a3) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (ReInterConstElimProof.lhs a1 a2 a3))
      (__eo_typeof (ReInterConstElimProof.rhs a2 a3))
      hConclTy).1
  have hOuterArgs :
      __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_re) a3) =
          Term.UOp UserOp.RegLan ∧
        __eo_typeof (ReInterConstElimProof.inner a1 a2) =
          Term.UOp UserOp.RegLan := by
    change __eo_typeof_re_concat
        (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_re) a3))
        (__eo_typeof (ReInterConstElimProof.inner a1 a2)) ≠
      Term.Stuck at hLhsNotStuck
    exact
      ReInterConstElimProof.eo_typeof_re_concat_ne_stuck_args_reglan
        _ _ hLhsNotStuck
  have hInnerArgs :
      __eo_typeof a1 = Term.UOp UserOp.RegLan ∧
        __eo_typeof a2 = Term.UOp UserOp.RegLan := by
    have hInnerTy := hOuterArgs.2
    change __eo_typeof_re_concat (__eo_typeof a1) (__eo_typeof a2) =
      Term.UOp UserOp.RegLan at hInnerTy
    exact
      ReInterConstElimProof.eo_typeof_re_concat_eq_reglan_args_reglan
        _ _ hInnerTy
  have hA3Ty : __eo_typeof a3 = Term.Apply Term.Seq Term.Char := by
    have hStrToReTy := hOuterArgs.1
    change __eo_typeof_str_to_re (__eo_typeof a3) =
      Term.UOp UserOp.RegLan at hStrToReTy
    exact
      ReInterConstElimProof.eo_typeof_str_to_re_eq_seq_char_of_reglan
        (__eo_typeof a3) hStrToReTy
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hInnerArgs.1] at hTyRaw
    simpa [TranslationProofs.eo_to_smt_type_reglan] using hTyRaw
  have hA3SmtTy :
      __smtx_typeof (__eo_to_smt a3) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a3) = __eo_to_smt_type (__eo_typeof a3) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a3 hA3Trans
    rw [hA3Ty] at hTyRaw
    have hsimpa := hTyRaw
    try simp [TranslationProofs.eo_to_smt_type_seq,
      TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
    exact hsimpa
  have hFacts :=
    ReInterConstElimProof.type_and_facts M hM a1 a2 a3
      hA1SmtTy hA2SmtTy hA3SmtTy hRedList
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by rw [hProgEq]; exact hFacts.1)⟩
  intro hEv
  have hPrem : eo_interprets M (ReInterConstElimProof.prem a3 a1) true := by
    have hHere := hEv.true_here P (by simp)
    simpa [hPShape] using hHere
  rw [hProgEq]
  exact hFacts.2 hPrem
