module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace StrInReInterElimProof

private abbrev mkStrInRe (s r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r

private abbrev mkReInter (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) s

private abbrev tail (r2 rs : Term) : Term :=
  mkReInter r2 rs

private abbrev singletonTail (r2 rs : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_inter) (tail r2 rs)

private abbrev lhs (s r1 r2 rs : Term) : Term :=
  mkStrInRe s (mkReInter r1 (tail r2 rs))

private abbrev rhs (s r1 r2 rs : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and) (mkStrInRe s r1))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (mkStrInRe s (singletonTail r2 rs)))
      (Term.Boolean true))

private abbrev concl (s r1 r2 rs : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs s r1 r2 rs))
    (rhs s r1 r2 rs)

private abbrev mkRhs (s r1 r2 rs : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.and) (mkStrInRe s r1))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.and)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
          (singletonTail r2 rs)))
      (Term.Boolean true))

private abbrev mkConcl (s r1 r2 rs : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.eq) (lhs s r1 r2 rs))
    (mkRhs s r1 r2 rs)

private theorem prog_mk_form (s r1 r2 rs : Term)
    (hs : s ≠ Term.Stuck) (hr1 : r1 ≠ Term.Stuck)
    (hr2 : r2 ≠ Term.Stuck) (hrs : rs ≠ Term.Stuck) :
    __eo_prog_str_in_re_inter_elim s r1 r2 rs =
      mkConcl s r1 r2 rs := by
  change __eo_prog_str_in_re_inter_elim s r1 r2 rs =
    __eo_mk_apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter) r1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r2) rs))))
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r1))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (__eo_list_singleton_elim (Term.UOp UserOp.re_inter)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r2) rs))))
          (Term.Boolean true)))
  exact __eo_prog_str_in_re_inter_elim.eq_5 s r1 r2 rs hs hr1 hr2 hrs

private theorem eo_typeof_str_in_re_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_str_in_re A B ≠ Term.Stuck) :
    A = Term.Apply Term.Seq Term.Char ∧ B = Term.RegLan := by
  by_cases hA : A = Term.Apply Term.Seq Term.Char
  · by_cases hB : B = Term.RegLan
    · exact ⟨hA, hB⟩
    · exact False.elim
        (h (__eo_typeof_str_in_re.eq_2 A B (fun _ hB' => hB hB')))
  · exact False.elim
      (h (__eo_typeof_str_in_re.eq_2 A B (fun hA' _ => hA hA')))

private theorem eo_typeof_re_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_re_concat A B ≠ Term.Stuck) :
    A = Term.RegLan ∧ B = Term.RegLan := by
  by_cases hA : A = Term.RegLan
  · by_cases hB : B = Term.RegLan
    · exact ⟨hA, hB⟩
    · exact False.elim
        (h (__eo_typeof_re_concat.eq_2 A B (fun _ hB' => hB hB')))
  · exact False.elim
      (h (__eo_typeof_re_concat.eq_2 A B (fun hA' _ => hA hA')))

private theorem smtx_typeof_of_eo_seq_char
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  have hsimpa := hTyRaw
  try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
  exact hsimpa

private theorem smtx_typeof_of_eo_reglan
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_reglan] using hTyRaw

private theorem smtx_typeof_re_inter_of_args (x y : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt (mkReInter x y)) = SmtType.RegLan := by
  intro hx hy
  change __smtx_typeof (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_inter_eq]
  simp [hx, hy, native_ite, native_Teq]

private theorem smtx_typeof_str_in_re_of_args (s r : Term) :
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt (mkStrInRe s r)) = SmtType.Bool := by
  intro hs hr
  change __smtx_typeof (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtType.Bool
  rw [typeof_str_in_re_eq]
  simp [hs, hr, native_ite, native_Teq]

private theorem smtx_typeof_and_of_bool_args (x y : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt y) = SmtType.Bool ->
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) =
      SmtType.Bool := by
  intro hx hy
  change __smtx_typeof (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Bool
  rw [typeof_and_eq]
  simp [hx, hy, native_ite, native_Teq]

private theorem typed_concl
    (s r1 r2 rs : Term)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hR1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.re_inter) (tail r2 rs) =
        Term.Boolean true)
    (hTail : __smtx_typeof (__eo_to_smt (tail r2 rs)) = SmtType.RegLan) :
    RuleProofs.eo_has_bool_type (concl s r1 r2 rs) := by
  have hFullTy :
      __smtx_typeof (__eo_to_smt (mkReInter r1 (tail r2 rs))) =
        SmtType.RegLan :=
    smtx_typeof_re_inter_of_args r1 (tail r2 rs) hR1 hTail
  have hSingTy :
      __smtx_typeof (__eo_to_smt (singletonTail r2 rs)) = SmtType.RegLan :=
    RuleProofs.reInter_singleton_elim_has_reglan_type (tail r2 rs)
      hTailList hTail
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs s r1 r2 rs)) = SmtType.Bool :=
    smtx_typeof_str_in_re_of_args s (mkReInter r1 (tail r2 rs)) hS hFullTy
  have hR1InTy :
      __smtx_typeof (__eo_to_smt (mkStrInRe s r1)) = SmtType.Bool :=
    smtx_typeof_str_in_re_of_args s r1 hS hR1
  have hSingInTy :
      __smtx_typeof (__eo_to_smt (mkStrInRe s (singletonTail r2 rs))) =
        SmtType.Bool :=
    smtx_typeof_str_in_re_of_args s (singletonTail r2 rs) hS hSingTy
  have hTrueTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
    native_decide
  have hInnerAndTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (mkStrInRe s (singletonTail r2 rs)))
              (Term.Boolean true))) =
        SmtType.Bool :=
    smtx_typeof_and_of_bool_args (mkStrInRe s (singletonTail r2 rs))
      (Term.Boolean true) hSingInTy hTrueTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs s r1 r2 rs)) = SmtType.Bool :=
    smtx_typeof_and_of_bool_args (mkStrInRe s r1)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (mkStrInRe s (singletonTail r2 rs)))
        (Term.Boolean true)) hR1InTy hInnerAndTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (lhs s r1 r2 rs) (rhs s r1 r2 rs)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts
    (M : SmtModel) (hM : model_wf M)
    (s r1 r2 rs : Term)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hR1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.re_inter) (tail r2 rs) =
        Term.Boolean true)
    (hTail : __smtx_typeof (__eo_to_smt (tail r2 rs)) = SmtType.RegLan) :
    eo_interprets M (concl s r1 r2 rs) true := by
  have hBool := typed_concl s r1 r2 rs hS hR1 hTailList hTail
  rcases RuleProofs.ReUnfoldNegSupport.smt_eval_seq_char_of_smt_type_seq_char
      M hM (__eo_to_smt s) hS with
    ⟨ss, hSEval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM r1 hR1 with
    ⟨rv1, hR1Eval⟩
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM (tail r2 rs) hTail with
    ⟨rtail, hTailEval⟩
  have hSingTy :
      __smtx_typeof (__eo_to_smt (singletonTail r2 rs)) = SmtType.RegLan :=
    RuleProofs.reInter_singleton_elim_has_reglan_type (tail r2 rs)
      hTailList hTail
  rcases RuleProofs.smt_model_eval_reglan_of_type M hM (singletonTail r2 rs)
      hSingTy with
    ⟨rsing, hSingEval⟩
  have hSingRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rsing) (SmtValue.RegLan rtail) := by
    have hsimpa :=
      RuleProofs.reInter_singleton_elim_rel_eval M (tail r2 rs)
        hTailList ⟨rtail, hTailEval⟩
    -- rewrite before `simp` unfolds `__eo_to_smt (tail ..)` past the
    -- left-hand sides of these evaluation equations
    rw [hSingEval, hTailEval] at hsimpa
    exact hsimpa
  have hEvalTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hS] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hS]
        simp)
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hEvalTy
  have hMemEq :
      RuleProofs.native_str_in_re (native_unpack_string ss) rsing =
        RuleProofs.native_str_in_re (native_unpack_string ss) rtail := by
    have hExt := hSingRel
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hExt
    change SmtValue.Boolean (native_re_ext_eq rsing rtail) =
      SmtValue.Boolean true at hExt
    simp at hExt
    simpa only [RuleProofs.native_str_in_re_eq_model] using
      hExt (native_unpack_string ss) hValid
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs s r1 r2 rs)) =
        SmtValue.Boolean
          (RuleProofs.native_str_in_re (native_unpack_string ss)
            (native_re_inter rv1 rtail)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s)
          (SmtTerm.re_inter (__eo_to_smt r1) (__eo_to_smt (tail r2 rs)))) =
      SmtValue.Boolean
        (RuleProofs.native_str_in_re (native_unpack_string ss)
          (native_re_inter rv1 rtail))
    simp only [__smtx_model_eval]
    rw [hSEval, hR1Eval, hTailEval]
    simp [__smtx_model_eval_str_in_re, __smtx_model_eval_re_inter,
      RuleProofs.model_str_in_re_unpack_eq_string_of_value_type ss
        (native_re_inter rv1 rtail) hEvalTy]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (rhs s r1 r2 rs)) =
        SmtValue.Boolean
          (RuleProofs.native_str_in_re (native_unpack_string ss) rv1 &&
            RuleProofs.native_str_in_re (native_unpack_string ss) rsing) := by
    change __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r1))
          (SmtTerm.and
            (SmtTerm.str_in_re (__eo_to_smt s)
              (__eo_to_smt (singletonTail r2 rs)))
            (SmtTerm.Boolean true))) =
      SmtValue.Boolean
        (RuleProofs.native_str_in_re (native_unpack_string ss) rv1 &&
          RuleProofs.native_str_in_re (native_unpack_string ss) rsing)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
      __smtx_model_eval_and, hSEval, hR1Eval, hSingEval, SmtEval.native_and,
      RuleProofs.model_str_in_re_unpack_eq_string_of_value_type ss rv1 hEvalTy,
      RuleProofs.model_str_in_re_unpack_eq_string_of_value_type ss rsing hEvalTy]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs s r1 r2 rs)
    (rhs s r1 r2 rs) hBool <| by
    rw [hLhsEval, hRhsEval]
    have hPayloadEq :
        RuleProofs.native_str_in_re (native_unpack_string ss)
            (native_re_inter rv1 rtail) =
          (RuleProofs.native_str_in_re (native_unpack_string ss) rv1 &&
            RuleProofs.native_str_in_re (native_unpack_string ss) rsing) := by
      rw [RuleProofs.native_str_in_re_re_inter, hMemEq]
    rw [hPayloadEq]
    exact RuleProofs.smt_value_rel_refl _

end StrInReInterElimProof

public theorem cmd_step_str_in_re_inter_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_inter_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_inter_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_inter_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_inter_elim args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      cases premises with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          have hTrans :
                              cArgListTranslationOk
                                (CArgList.cons a1
                                  (CArgList.cons a2
                                    (CArgList.cons a3
                                      (CArgList.cons a4 CArgList.nil)))) :=
                            hCmdTrans
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                            hTrans.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                            hTrans.2.1
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                            hTrans.2.2.1
                          have hA4Trans : RuleProofs.eo_has_smt_translation a4 :=
                            hTrans.2.2.2.1
                          have hProgLocal :
                              __eo_prog_str_in_re_inter_elim a1 a2 a3 a4 ≠
                                Term.Stuck := by
                            change __eo_prog_str_in_re_inter_elim a1 a2 a3 a4 ≠
                              Term.Stuck at hProg
                            exact hProg
                          have hA1Ne : a1 ≠ Term.Stuck := by
                            intro h
                            subst a1
                            exact hProgLocal
                              (__eo_prog_str_in_re_inter_elim.eq_1 a2 a3 a4)
                          have hA2Ne : a2 ≠ Term.Stuck := by
                            intro h
                            subst a2
                            exact hProgLocal
                              (__eo_prog_str_in_re_inter_elim.eq_2 a1 a3 a4
                                hA1Ne)
                          have hA3Ne : a3 ≠ Term.Stuck := by
                            intro h
                            subst a3
                            exact hProgLocal
                              (__eo_prog_str_in_re_inter_elim.eq_3 a1 a2 a4
                                hA1Ne hA2Ne)
                          have hA4Ne : a4 ≠ Term.Stuck := by
                            intro h
                            subst a4
                            exact hProgLocal
                              (__eo_prog_str_in_re_inter_elim.eq_4 a1 a2 a3
                                hA1Ne hA2Ne hA3Ne)
                          have hProgMk :
                              __eo_cmd_step_proven s CRule.str_in_re_inter_elim
                                  (CArgList.cons a1
                                    (CArgList.cons a2
                                      (CArgList.cons a3
                                        (CArgList.cons a4 CArgList.nil))))
                                  CIndexList.nil =
                                StrInReInterElimProof.mkConcl a1 a2 a3 a4 :=
                            StrInReInterElimProof.prog_mk_form a1 a2 a3 a4
                              hA1Ne hA2Ne hA3Ne hA4Ne
                          have hMkNe :
                              StrInReInterElimProof.mkConcl a1 a2 a3 a4 ≠
                                Term.Stuck := by
                            simpa [hProgMk] using hProg
                          have hRhsMkNe :
                              StrInReInterElimProof.mkRhs a1 a2 a3 a4 ≠
                                Term.Stuck :=
                            eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _
                              hMkNe
                          have hAndTailNe :
                              __eo_mk_apply
                                  (__eo_mk_apply (Term.UOp UserOp.and)
                                    (__eo_mk_apply
                                      (Term.Apply (Term.UOp UserOp.str_in_re) a1)
                                      (StrInReInterElimProof.singletonTail a3 a4)))
                                  (Term.Boolean true) ≠ Term.Stuck :=
                            eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _
                              hRhsMkNe
                          have hAndFunNe :
                              __eo_mk_apply (Term.UOp UserOp.and)
                                  (__eo_mk_apply
                                    (Term.Apply (Term.UOp UserOp.str_in_re) a1)
                                    (StrInReInterElimProof.singletonTail a3 a4)) ≠
                                Term.Stuck :=
                            eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _
                              hAndTailNe
                          have hSingInNe :
                              __eo_mk_apply
                                  (Term.Apply (Term.UOp UserOp.str_in_re) a1)
                                  (StrInReInterElimProof.singletonTail a3 a4) ≠
                                Term.Stuck :=
                            eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _
                              hAndFunNe
                          have hSingNe :
                              StrInReInterElimProof.singletonTail a3 a4 ≠
                                Term.Stuck :=
                            eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _
                              hSingInNe
                          have hTailList :
                              __eo_is_list (Term.UOp UserOp.re_inter)
                                  (StrInReInterElimProof.tail a3 a4) =
                                Term.Boolean true :=
                            RuleProofs.reInter_singleton_elim_list_of_ne_stuck
                              (StrInReInterElimProof.tail a3 a4) hSingNe
                          have hRhsApply :
                              StrInReInterElimProof.mkRhs a1 a2 a3 a4 =
                                StrInReInterElimProof.rhs a1 a2 a3 a4 := by
                            unfold StrInReInterElimProof.mkRhs
                              StrInReInterElimProof.rhs
                            rw [eo_mk_apply_eq_apply_of_ne_stuck
                              _ _ hRhsMkNe]
                            rw [eo_mk_apply_eq_apply_of_ne_stuck
                              _ _ hAndTailNe]
                            rw [eo_mk_apply_eq_apply_of_ne_stuck
                              _ _ hAndFunNe]
                            rw [eo_mk_apply_eq_apply_of_ne_stuck
                              _ _ hSingInNe]
                          have hProgApply :
                              __eo_cmd_step_proven s CRule.str_in_re_inter_elim
                                  (CArgList.cons a1
                                    (CArgList.cons a2
                                      (CArgList.cons a3
                                        (CArgList.cons a4 CArgList.nil))))
                                  CIndexList.nil =
                                StrInReInterElimProof.concl a1 a2 a3 a4 := by
                            rw [hProgMk]
                            unfold StrInReInterElimProof.mkConcl
                              StrInReInterElimProof.concl
                            rw [eo_mk_apply_eq_apply_of_ne_stuck
                              _ _ hMkNe]
                            rw [hRhsApply]
                          have hConclTy :
                              __eo_typeof
                                  (StrInReInterElimProof.concl a1 a2 a3 a4) =
                                Term.Bool := by
                            rw [← hProgApply]
                            exact hResultTy
                          rw [StrInReInterElimProof.concl] at hConclTy
                          change __eo_typeof_eq
                              (__eo_typeof
                                (StrInReInterElimProof.lhs a1 a2 a3 a4))
                              (__eo_typeof
                                (StrInReInterElimProof.rhs a1 a2 a3 a4)) =
                            Term.Bool at hConclTy
                          have hLhsTyNe :
                              __eo_typeof
                                  (StrInReInterElimProof.lhs a1 a2 a3 a4) ≠
                                Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              _ _ hConclTy).1
                          have hStrArgs :=
                            StrInReInterElimProof.eo_typeof_str_in_re_args_of_ne_stuck
                              (__eo_typeof a1)
                              (__eo_typeof
                                (StrInReInterElimProof.mkReInter a2
                                  (StrInReInterElimProof.tail a3 a4)))
                              (by
                                change __eo_typeof_str_in_re (__eo_typeof a1)
                                  (__eo_typeof
                                    (StrInReInterElimProof.mkReInter a2
                                      (StrInReInterElimProof.tail a3 a4))) ≠
                                  Term.Stuck at hLhsTyNe
                                exact hLhsTyNe)
                          have hFullTyNe :
                              __eo_typeof_re_concat (__eo_typeof a2)
                                  (__eo_typeof (StrInReInterElimProof.tail a3 a4)) ≠
                                Term.Stuck := by
                            have hFullTyEq := hStrArgs.2
                            change __eo_typeof_re_concat (__eo_typeof a2)
                                (__eo_typeof (StrInReInterElimProof.tail a3 a4)) =
                              Term.RegLan at hFullTyEq
                            rw [hFullTyEq]
                            simp
                          have hFullArgs :=
                            StrInReInterElimProof.eo_typeof_re_args_of_ne_stuck
                              (__eo_typeof a2)
                              (__eo_typeof (StrInReInterElimProof.tail a3 a4))
                              hFullTyNe
                          have hTailTyNe :
                              __eo_typeof_re_concat (__eo_typeof a3)
                                  (__eo_typeof a4) ≠ Term.Stuck := by
                            have hTailTyEq := hFullArgs.2
                            change __eo_typeof_re_concat (__eo_typeof a3)
                                (__eo_typeof a4) =
                              Term.RegLan at hTailTyEq
                            rw [hTailTyEq]
                            simp
                          have hTailArgs :=
                            StrInReInterElimProof.eo_typeof_re_args_of_ne_stuck
                              (__eo_typeof a3) (__eo_typeof a4) hTailTyNe
                          have hSmtS :=
                            StrInReInterElimProof.smtx_typeof_of_eo_seq_char
                              a1 hA1Trans hStrArgs.1
                          have hSmtR1 :=
                            StrInReInterElimProof.smtx_typeof_of_eo_reglan
                              a2 hA2Trans hFullArgs.1
                          have hSmtR2 :=
                            StrInReInterElimProof.smtx_typeof_of_eo_reglan
                              a3 hA3Trans hTailArgs.1
                          have hSmtRs :=
                            StrInReInterElimProof.smtx_typeof_of_eo_reglan
                              a4 hA4Trans hTailArgs.2
                          have hSmtTail :
                              __smtx_typeof
                                  (__eo_to_smt
                                    (StrInReInterElimProof.tail a3 a4)) =
                                SmtType.RegLan :=
                            StrInReInterElimProof.smtx_typeof_re_inter_of_args
                              a3 a4 hSmtR2 hSmtRs
                          have hBool :
                              RuleProofs.eo_has_bool_type
                                (StrInReInterElimProof.concl a1 a2 a3 a4) :=
                            StrInReInterElimProof.typed_concl a1 a2 a3 a4
                              hSmtS hSmtR1 hTailList hSmtTail
                          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            (by simpa [hProgApply] using hBool)⟩
                          intro _hTrue
                          rw [hProgApply]
                          exact StrInReInterElimProof.facts M hM a1 a2 a3 a4
                            hSmtS hSmtR1 hTailList hSmtTail
