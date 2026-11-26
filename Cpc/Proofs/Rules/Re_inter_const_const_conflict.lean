module

public import Cpc.Proofs.RuleSupport.ReConstSupport
import all Cpc.Proofs.RuleSupport.ReConstSupport

open Eo
open SmtEval
open Smtm
open ReConstSupport

-- Keep string coercions on the model's explicit string-to-value embedding.
attribute [-instance] List.instMonad List.instAlternativeMonad_mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReInterConstConstConflictProof

private abbrev reStr (s : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) s

private abbrev mkI (r x : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) x

private abbrev tailT (t zs : Term) : Term :=
  mkI (reStr t) zs

private abbrev inner (ys t zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_inter) ys (tailT t zs)

private abbrev midMk (s ys t zs : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_inter) (reStr s))
    (inner ys t zs)

private abbrev mid (s ys t zs : Term) : Term :=
  mkI (reStr s) (inner ys t zs)

private abbrev lhsMk (xs s ys t zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_inter) xs (midMk s ys t zs)

private abbrev lhs (xs s ys t zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_inter) xs (mid s ys t zs)

private abbrev rhs : Term :=
  Term.UOp UserOp.re_none

private abbrev mkConcl (xs s ys t zs : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhsMk xs s ys t zs)) rhs

private abbrev concl (xs s ys t zs : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs s ys t zs)) rhs

private abbrev prem (s t : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) s) t))
    (Term.Boolean false)

private theorem prog_form (xs s ys t zs P : Term)
    (hNe :
      __eo_prog_re_inter_const_const_conflict xs s ys t zs (Proof.pf P) ≠
        Term.Stuck) :
    P = prem s t ∧
      __eo_prog_re_inter_const_const_conflict xs s ys t zs (Proof.pf P) =
        mkConcl xs s ys t zs := by
  unfold __eo_prog_re_inter_const_const_conflict at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i hPrem
    injection hPrem with hPremEq
    have hReqArg := ReInterCstringProof.eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq :=
      ReInterCstringProof.eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    rcases ReInterCstringProof.eo_and_eq_true hReqArg with ⟨hs, ht⟩
    have hs' := ReInterCstringProof.eo_eq_eq_true hs
    have ht' := ReInterCstringProof.eo_eq_eq_true ht
    rw [hs', ht'] at hPremEq
    exact ⟨hPremEq, hReqEq⟩
  · exact False.elim (hNe rfl)

private theorem list_concat_eq_rec (f a b : Term)
    (ha : __eo_is_list f a = Term.Boolean true)
    (hb : __eo_is_list f b = Term.Boolean true) :
    __eo_list_concat f a b = __eo_list_concat_rec a b := by
  simp [__eo_list_concat, ha, hb, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]

private theorem eo_typeof_eq_eq_bool_left (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) : B = A := by
  have hNe : __eo_typeof_eq A B ≠ Term.Stuck := by
    rw [h]
    simp
  unfold __eo_typeof_eq at hNe
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact ReInterCstringProof.eo_eq_eq_true
      (ReInterCstringProof.eo_requires_arg_eq_of_ne_stuck hNe)

private theorem eo_typeof_stuck : __eo_typeof Term.Stuck = Term.Stuck := rfl

private theorem typeof_concat_rec_right_reglan_aux (z : Term) (n : Nat) :
    ∀ xs : Term, sizeOf xs = n ->
      __eo_is_list (Term.UOp UserOp.re_inter) xs = Term.Boolean true ->
      __eo_typeof (__eo_list_concat_rec xs z) = Term.UOp UserOp.RegLan ->
      __eo_typeof z = Term.UOp UserOp.RegLan := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro xs hn hList hTy
  by_cases hz : z = Term.Stuck
  · subst z
    have hRec : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
      cases xs <;> simp [__eo_list_concat_rec]
    rw [hRec] at hTy
    exact hTy
  cases xs with
  | Apply f y =>
      cases f with
      | Apply g x =>
          have hg : g = Term.UOp UserOp.re_inter :=
            eo_is_list_cons_head_eq_of_true _ g x y hList
          subst g
          have hTail :=
            eo_is_list_tail_true_of_cons_self _ x y hList
          have hRecEq :
              __eo_list_concat_rec
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y) z =
                __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_inter) x)
                  (__eo_list_concat_rec y z) := by
            rw [__eo_list_concat_rec.eq_def]
            simp [hz]
          rw [hRecEq] at hTy
          have hMkNe :
              __eo_mk_apply (Term.Apply (Term.UOp UserOp.re_inter) x)
                  (__eo_list_concat_rec y z) ≠ Term.Stuck := by
            intro hBad
            rw [hBad, eo_typeof_stuck] at hTy
            cases hTy
          rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hTy
          change __eo_typeof_re_concat (__eo_typeof x)
              (__eo_typeof (__eo_list_concat_rec y z)) =
            Term.UOp UserOp.RegLan at hTy
          exact ih (sizeOf y) (by subst hn; simp) y rfl hTail
            (ReInterCstringProof.eo_typeof_re_concat_eq_reglan_args_reglan
              _ _ hTy).2
      | _ =>
          simpa [__eo_list_concat_rec, hz] using hTy
  | Stuck =>
      simp [__eo_is_list] at hList
  | _ =>
      simpa [__eo_list_concat_rec, hz] using hTy

private theorem typeof_concat_rec_right_reglan (z xs : Term)
    (hList : __eo_is_list (Term.UOp UserOp.re_inter) xs = Term.Boolean true)
    (hTy : __eo_typeof (__eo_list_concat_rec xs z) = Term.UOp UserOp.RegLan) :
    __eo_typeof z = Term.UOp UserOp.RegLan :=
  typeof_concat_rec_right_reglan_aux z (sizeOf xs) xs rfl hList hTy

private theorem seq_ne_of_prem (M : SmtModel) (s t : Term) (ss tt : SmtSeq)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hTEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq tt)
    (hPrem : eo_interprets M (prem s t) true) :
    ss ≠ tt := by
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) s) t)
      (Term.Boolean false) hPrem
  have hEqEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) s) t)) =
        SmtValue.Boolean (decide (SmtValue.Seq ss = SmtValue.Seq tt)) := by
    change __smtx_model_eval M (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt t)) =
      SmtValue.Boolean (decide (SmtValue.Seq ss = SmtValue.Seq tt))
    simp [__smtx_model_eval, hSEval, hTEval, __smtx_model_eval_eq, native_veq]
  have hFalseEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
        SmtValue.Boolean false := by
    change __smtx_model_eval M (SmtTerm.Boolean false) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hEqEval, hFalseEval] at hPremRel
  have hValueEq :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  intro hEq
  subst hEq
  simp at hValueEq

private theorem type_and_facts
    (M : SmtModel) (hM : model_wf M)
    (xs s ys t zs : Term)
    (hXsList :
      __eo_is_list (Term.UOp UserOp.re_inter) xs = Term.Boolean true)
    (hYsList :
      __eo_is_list (Term.UOp UserOp.re_inter) ys = Term.Boolean true)
    (hZsList :
      __eo_is_list (Term.UOp UserOp.re_inter) zs = Term.Boolean true)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hYsTrans : RuleProofs.eo_has_smt_translation ys)
    (hZsTrans : RuleProofs.eo_has_smt_translation zs)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hTTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (concl xs s ys t zs) ∧
      (eo_interprets M (prem s t) true ->
        eo_interprets M (concl xs s ys t zs) true) := by
  have hXsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.RegLan :=
    reInter_list_smt_typeof_reglan_of_non_none xs hXsList
      (by simpa [RuleProofs.eo_has_smt_translation] using hXsTrans)
  have hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan :=
    reInter_list_smt_typeof_reglan_of_non_none ys hYsList
      (by simpa [RuleProofs.eo_has_smt_translation] using hYsTrans)
  have hZsTy : __smtx_typeof (__eo_to_smt zs) = SmtType.RegLan :=
    reInter_list_smt_typeof_reglan_of_non_none zs hZsList
      (by simpa [RuleProofs.eo_has_smt_translation] using hZsTrans)
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM xs hXsTy with
    ⟨rx, hXsEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM ys hYsTy with
    ⟨ry, hYsEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM zs hZsTy with
    ⟨rz, hZsEval⟩
  rcases seq_char_eval M hM s hSTy with ⟨ss, hSEval, hSsTy⟩
  rcases seq_char_eval M hM t hTTy with ⟨tt, hTEval, hTtTy⟩
  have hSUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  have hTUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hTtTy
  -- tail `re.inter (str.to_re t) zs`
  have hTailList :
      __eo_is_list (Term.UOp UserOp.re_inter) (tailT t zs) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_inter) (reStr t) zs (by simp) hZsList
  have hTailTy : __smtx_typeof (__eo_to_smt (tailT t zs)) = SmtType.RegLan :=
    smtx_typeof_re_inter_of_args _ _
      (smtx_typeof_str_to_re_of_seq_char t hTTy) hZsTy
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt (tailT t zs)) =
        SmtValue.RegLan
          (native_re_inter (native_str_to_re (native_unpack_string tt)) rz) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (SmtTerm.str_to_re (__eo_to_smt t)) (__eo_to_smt zs)) =
      SmtValue.RegLan
        (native_re_inter (native_str_to_re (native_unpack_string tt)) rz)
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
      __smtx_model_eval_re_inter, hTEval, hZsEval, hTUnpack]
  -- inner `ys ++ tail`
  rcases RuleProofs.reInter_list_concat_eval_rel M ys (tailT t zs) ry _
      hYsList hTailList hYsTy hTailTy hYsEval hTailEval with
    ⟨r1, hInnerEval, hInnerTy, hInnerRel⟩
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.re_inter) (inner ys t zs) =
        Term.Boolean true := by
    unfold inner
    rw [list_concat_eq_rec _ _ _ hYsList hTailList]
    exact eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.re_inter) ys (tailT t zs) hYsList hTailList
  -- middle `re.inter (str.to_re s) inner`
  have hMidList :
      __eo_is_list (Term.UOp UserOp.re_inter) (mid s ys t zs) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.re_inter) (reStr s) (inner ys t zs) (by simp)
      hInnerList
  have hMidTy : __smtx_typeof (__eo_to_smt (mid s ys t zs)) = SmtType.RegLan :=
    smtx_typeof_re_inter_of_args _ _
      (smtx_typeof_str_to_re_of_seq_char s hSTy) hInnerTy
  have hMidEval :
      __smtx_model_eval M (__eo_to_smt (mid s ys t zs)) =
        SmtValue.RegLan
          (native_re_inter (native_str_to_re (native_unpack_string ss)) r1) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (SmtTerm.str_to_re (__eo_to_smt s))
          (__eo_to_smt (inner ys t zs))) =
      SmtValue.RegLan
        (native_re_inter (native_str_to_re (native_unpack_string ss)) r1)
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
      __smtx_model_eval_re_inter, hSEval, hInnerEval, hSUnpack]
  rcases RuleProofs.reInter_list_concat_eval_rel M xs (mid s ys t zs) rx _
      hXsList hMidList hXsTy hMidTy hXsEval hMidEval with
    ⟨r, hLhsEval, hLhsTy, hLhsRel⟩
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    change __smtx_typeof SmtTerm.re_none = SmtType.RegLan
    rw [__smtx_typeof.eq_def] <;> simp only
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none = SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_def] <;> simp only
  have hBool : RuleProofs.eo_has_bool_type (concl xs s ys t zs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (lhs xs s ys t zs) rhs
      (by rw [hLhsTy, hRhsTy])
      (by rw [hLhsTy]; simp)
  refine ⟨hBool, ?_⟩
  intro hPrem
  have hNe : ss ≠ tt := seq_ne_of_prem M s t ss tt hSEval hTEval hPrem
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs xs s ys t zs) rhs hBool <| by
    rw [hLhsEval, hRhsEval]
    apply RuleProofs.smt_value_rel_reglan_of_valid_eq
    intro str hValid
    rw [RuleProofs.native_str_in_re_re_none,
      RuleProofs.native_str_in_re_eq_model str r,
      RuleProofs.smt_value_rel_reglan_valid_eq hLhsRel hValid,
      ← RuleProofs.native_str_in_re_eq_model,
      RuleProofs.native_str_in_re_re_inter,
      RuleProofs.native_str_in_re_re_inter,
      RuleProofs.native_str_in_re_eq_model str r1,
      RuleProofs.smt_value_rel_reglan_valid_eq hInnerRel hValid,
      ← RuleProofs.native_str_in_re_eq_model,
      RuleProofs.native_str_in_re_re_inter,
      RuleProofs.native_str_in_re_re_inter]
    cases hS :
        RuleProofs.native_str_in_re str
          (native_str_to_re (native_unpack_string ss)) <;>
      cases hT :
        RuleProofs.native_str_in_re str
          (native_str_to_re (native_unpack_string tt)) <;>
      simp
    exfalso
    have hStrS : str = native_unpack_string ss :=
      RuleProofs.native_str_in_re_str_to_re_eq hValid (by
        simpa [impl_native_string_to_values, List.map_eq_flatMap] using hS)
    have hStrT : str = native_unpack_string tt :=
      RuleProofs.native_str_in_re_str_to_re_eq hValid (by
        simpa [impl_native_string_to_values, List.map_eq_flatMap] using hT)
    apply hNe
    apply smt_seq_eq_of_unpack_eq_same_type ss tt SmtType.Char hSsTy hTtTy
    rw [hSUnpack, hTUnpack, ← hStrS, ← hStrT]

private theorem eo_seq_char_of_reStr_typeof (a : Term)
    (h : __eo_typeof (reStr a) = Term.UOp UserOp.RegLan) :
    __eo_typeof a = Term.Apply Term.Seq Term.Char := by
  change __eo_typeof_str_to_re (__eo_typeof a) = Term.UOp UserOp.RegLan at h
  exact ReInterCstringProof.eo_typeof_str_to_re_eq_seq_char_of_reglan _ h

private theorem main
    (M : SmtModel) (hM : model_wf M) (xs s ys t zs P : Term)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hYsTrans : RuleProofs.eo_has_smt_translation ys)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hZsTrans : RuleProofs.eo_has_smt_translation zs)
    (hProgNe :
      __eo_prog_re_inter_const_const_conflict xs s ys t zs (Proof.pf P) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_re_inter_const_const_conflict xs s ys t zs (Proof.pf P)) =
        Term.Bool) :
    StepRuleProperties M [P]
      (__eo_prog_re_inter_const_const_conflict xs s ys t zs (Proof.pf P)) := by
  obtain ⟨hPShape, hProgEq⟩ := prog_form xs s ys t zs P hProgNe
  have hMkNe : mkConcl xs s ys t zs ≠ Term.Stuck := by
    rw [← hProgEq]
    exact hProgNe
  have hEqFunNe :
      __eo_mk_apply (Term.UOp UserOp.eq) (lhsMk xs s ys t zs) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMkNe
  have hLhsMkNe : lhsMk xs s ys t zs ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
  obtain ⟨hXsList, hMidMkList⟩ :=
    RegexRewriteSupport.list_concat_lists_of_ne_stuck _ _ _ hLhsMkNe
  have hMidMkNe : midMk s ys t zs ≠ Term.Stuck := by
    intro h
    rw [h] at hMidMkList
    simp [__eo_is_list] at hMidMkList
  have hMidEq : midMk s ys t zs = mid s ys t zs :=
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hMidMkNe
  have hInnerNe : inner ys t zs ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidMkNe
  obtain ⟨hYsList, hTailList⟩ :=
    RegexRewriteSupport.list_concat_lists_of_ne_stuck _ _ _ hInnerNe
  have hZsList : __eo_is_list (Term.UOp UserOp.re_inter) zs = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self _ (reStr t) zs hTailList
  have hProgApply :
      __eo_prog_re_inter_const_const_conflict xs s ys t zs (Proof.pf P) =
        concl xs s ys t zs := by
    rw [hProgEq]
    unfold mkConcl
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
    unfold lhsMk
    rw [hMidEq]
  have hConclTy : __eo_typeof (concl xs s ys t zs) = Term.Bool := by
    rw [← hProgApply]
    exact hResultTy
  change __eo_typeof_eq (__eo_typeof (lhs xs s ys t zs)) (__eo_typeof rhs) =
    Term.Bool at hConclTy
  have hLhsEoTy : __eo_typeof (lhs xs s ys t zs) = Term.UOp UserOp.RegLan := by
    have h := eo_typeof_eq_eq_bool_left _ _ hConclTy
    exact h.symm.trans rfl
  have hMidEoTy : __eo_typeof (mid s ys t zs) = Term.UOp UserOp.RegLan := by
    unfold lhs at hLhsEoTy
    rw [list_concat_eq_rec _ _ _ hXsList (by rw [← hMidEq]; exact hMidMkList)]
      at hLhsEoTy
    exact typeof_concat_rec_right_reglan _ _ hXsList hLhsEoTy
  change __eo_typeof_re_concat (__eo_typeof (reStr s))
      (__eo_typeof (inner ys t zs)) = Term.UOp UserOp.RegLan at hMidEoTy
  obtain ⟨hStrSTy, hInnerEoTy⟩ :=
    ReInterCstringProof.eo_typeof_re_concat_eq_reglan_args_reglan _ _ hMidEoTy
  have hTailEoTy : __eo_typeof (tailT t zs) = Term.UOp UserOp.RegLan := by
    unfold inner at hInnerEoTy
    rw [list_concat_eq_rec _ _ _ hYsList hTailList] at hInnerEoTy
    exact typeof_concat_rec_right_reglan _ _ hYsList hInnerEoTy
  change __eo_typeof_re_concat (__eo_typeof (reStr t))
      (__eo_typeof zs) = Term.UOp UserOp.RegLan at hTailEoTy
  have hStrTTy :=
    (ReInterCstringProof.eo_typeof_re_concat_eq_reglan_args_reglan _ _
      hTailEoTy).1
  have hSTy := smt_seq_char_of_eo_type s hSTrans
    (eo_seq_char_of_reStr_typeof s hStrSTy)
  have hTTy := smt_seq_char_of_eo_type t hTTrans
    (eo_seq_char_of_reStr_typeof t hStrTTy)
  have hFacts := type_and_facts M hM xs s ys t zs hXsList hYsList hZsList
    hXsTrans hYsTrans hZsTrans hSTy hTTy
  rw [hProgApply]
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hFacts.1⟩
  intro hEv
  have hPrem : eo_interprets M (prem s t) true := by
    have hHere := hEv.true_here P (by simp)
    simpa [hPShape] using hHere
  exact hFacts.2 hPrem

end ReInterConstConstConflictProof

public theorem cmd_step_re_inter_const_const_conflict_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_const_const_conflict args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_inter_const_const_conflict args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_const_const_conflict args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.re_inter_const_const_conflict args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  rcases premises with _ | ⟨n, _ | ⟨_, _⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  have hTrans :
      cArgListTranslationOk
        (CArgList.cons a1 (CArgList.cons a2 (CArgList.cons a3
          (CArgList.cons a4 (CArgList.cons a5 CArgList.nil))))) :=
    hCmdTrans
  exact ReInterConstConstConflictProof.main M hM a1 a2 a3 a4 a5
    (__eo_state_proven_nth s n)
    hTrans.1 hTrans.2.1 hTrans.2.2.1 hTrans.2.2.2.1 hTrans.2.2.2.2.1
    hProg hResultTy
