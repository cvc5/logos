module

public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.RegexValueSupport
import all Cpc.Proofs.RuleSupport.RegexValueSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev mkStrInRe (s r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r

private abbrev mkStrConcat (s t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) t

private abbrev mkReConcat (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r) s

private abbrev emptyStrInRe : Term :=
  mkStrInRe (Term.String (native_string_lit "")) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String (native_string_lit "")))

private theorem eo_get_nil_rec_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        Term.Boolean true := by
  intro ps
  induction ps with
  | nil =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not]
  | cons p ps ih =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires, ih,
        native_ite, native_teq, native_not, SmtEval.native_not]

private theorem eo_list_rev_rec_and_premiseAndFormulaList :
    ∀ xs ys : List Term,
      __eo_list_rev_rec (premiseAndFormulaList xs) (premiseAndFormulaList ys) =
        premiseAndFormulaList (xs.reverse ++ ys) := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      cases ys <;> rfl
  | cons p xs ih =>
      cases ys with
      | nil =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih [p]
      | cons y ys =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih (p :: y :: ys)

private theorem eo_list_rev_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_list_rev (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        premiseAndFormulaList ps.reverse := by
  intro ps
  unfold __eo_list_rev
  simp [__eo_requires, premiseAndFormulaList_is_and_list,
    eo_get_nil_rec_and_premiseAndFormulaList, native_ite, native_teq,
    native_not, SmtEval.native_not]
  simpa [premiseAndFormulaList] using
    eo_list_rev_rec_and_premiseAndFormulaList ps []

private theorem all_interpreted_true_reverse
    (M : SmtModel) (ps : List Term) :
    AllInterpretedTrue M ps ->
    AllInterpretedTrue M ps.reverse := by
  intro h t ht
  exact h t (by simpa using List.mem_reverse.mp ht)

private theorem all_have_bool_type_reverse
    (ps : List Term) :
    AllHaveBoolType ps ->
    AllHaveBoolType ps.reverse := by
  intro h t ht
  exact h t (by simpa using List.mem_reverse.mp ht)

private theorem str_in_re_concat_has_bool_type
    (s r accS accR : Term) :
    RuleProofs.eo_has_bool_type (mkStrInRe s r) ->
    RuleProofs.eo_has_bool_type (mkStrInRe accS accR) ->
    RuleProofs.eo_has_bool_type (mkStrInRe (mkStrConcat s accS) (mkReConcat r accR)) := by
  intro hSR hAcc
  unfold RuleProofs.eo_has_bool_type at hSR hAcc ⊢
  change __smtx_typeof (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtType.Bool at hSR
  change __smtx_typeof (SmtTerm.str_in_re (__eo_to_smt accS) (__eo_to_smt accR)) =
    SmtType.Bool at hAcc
  have hNNSR :
      term_has_non_none_type (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    rw [hSR]
    simp
  have hNNAcc :
      term_has_non_none_type
        (SmtTerm.str_in_re (__eo_to_smt accS) (__eo_to_smt accR)) := by
    unfold term_has_non_none_type
    rw [hAcc]
    simp
  have hArgsSR := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re)
    (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt r)) hNNSR
  have hArgsAcc := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re)
    (typeof_str_in_re_eq (__eo_to_smt accS) (__eo_to_smt accR)) hNNAcc
  change __smtx_typeof
      (SmtTerm.str_in_re (SmtTerm.str_concat (__eo_to_smt s) (__eo_to_smt accS))
        (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt accR))) = SmtType.Bool
  rw [typeof_str_in_re_eq, typeof_str_concat_eq, typeof_re_concat_eq]
  simp [hArgsSR.1, hArgsSR.2, hArgsAcc.1, hArgsAcc.2,
    __smtx_typeof_seq_op_2, native_ite, native_Teq]

private theorem native_unpack_seq_pack (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => by rfl
  | x :: xs => by simp [native_pack_seq, native_unpack_seq, native_unpack_seq_pack T xs]

private theorem native_unpack_string_pack_concat
    (T : SmtType) (ss1 ss2 : SmtSeq) :
    native_unpack_string
        (native_pack_seq T (native_seq_concat (native_unpack_seq ss1) (native_unpack_seq ss2))) =
      native_unpack_string ss1 ++ native_unpack_string ss2 := by
  simp [native_unpack_string, native_seq_concat,
    native_unpack_seq_pack, List.map_append]

private theorem facts_str_in_re_concat
    (M : SmtModel) (s r accS accR : Term)
    (hSRBool : RuleProofs.eo_has_bool_type (mkStrInRe s r))
    (hAccBool : RuleProofs.eo_has_bool_type (mkStrInRe accS accR))
    (hSRTrue : eo_interprets M (mkStrInRe s r) true)
    (hAccTrue : eo_interprets M (mkStrInRe accS accR) true) :
    eo_interprets M (mkStrInRe (mkStrConcat s accS) (mkReConcat r accR)) true := by
  have hBool := str_in_re_concat_has_bool_type s r accS accR hSRBool hAccBool
  apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hSRTrue hAccTrue
  cases hSRTrue with
  | intro_true _ hEvalSR =>
      cases hAccTrue with
      | intro_true _ hEvalAcc =>
          change __smtx_model_eval M
              (SmtTerm.str_in_re
                (SmtTerm.str_concat (__eo_to_smt s) (__eo_to_smt accS))
                (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt accR))) =
            SmtValue.Boolean true
          rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_81,
            __smtx_model_eval.eq_114]
          change __smtx_model_eval M
              (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
            SmtValue.Boolean true at hEvalSR
          change __smtx_model_eval M
              (SmtTerm.str_in_re (__eo_to_smt accS) (__eo_to_smt accR)) =
            SmtValue.Boolean true at hEvalAcc
          rw [__smtx_model_eval.eq_119] at hEvalSR hEvalAcc
          cases hs : __smtx_model_eval M (__eo_to_smt s) with
          | Seq ss =>
              cases hr : __smtx_model_eval M (__eo_to_smt r) with
              | RegLan rr =>
                  simp [hs, hr, __smtx_model_eval_str_in_re] at hEvalSR
                  cases haccS : __smtx_model_eval M (__eo_to_smt accS) with
                  | Seq accSs =>
                      cases haccR : __smtx_model_eval M (__eo_to_smt accR) with
                      | RegLan accRr =>
                          simp [haccS, haccR, __smtx_model_eval_str_in_re] at hEvalAcc
                          simp [__smtx_model_eval_str_concat,
                            __smtx_model_eval_re_concat, __smtx_model_eval_str_in_re,
                            RuleProofs.native_unpack_seq_pack_seq,
                            native_seq_concat,
                            RuleProofs.model_str_in_re_re_concat_intro _ _ _ _
                              hEvalSR hEvalAcc]
                      | _ =>
                          simp [haccS, haccR, __smtx_model_eval_str_in_re] at hEvalAcc
                  | _ =>
                      cases haccR : __smtx_model_eval M (__eo_to_smt accR) <;>
                        simp [haccS, haccR, __smtx_model_eval_str_in_re] at hEvalAcc
              | _ =>
                  simp [hs, hr, __smtx_model_eval_str_in_re] at hEvalSR
          | _ =>
              cases hr : __smtx_model_eval M (__eo_to_smt r) <;>
                simp [hs, hr, __smtx_model_eval_str_in_re] at hEvalSR

private theorem empty_str_in_re_has_bool_type :
    RuleProofs.eo_has_bool_type emptyStrInRe := by
  unfold RuleProofs.eo_has_bool_type emptyStrInRe mkStrInRe
  change __smtx_typeof
      (SmtTerm.str_in_re (SmtTerm.String (native_string_lit ""))
        (SmtTerm.str_to_re (SmtTerm.String (native_string_lit "")))) = SmtType.Bool
  rw [typeof_str_in_re_eq, typeof_str_to_re_eq]
  simp [__smtx_typeof.eq_4, native_ite, native_Teq, native_string_valid,
    native_string_lit]

private theorem empty_str_in_re_true (M : SmtModel) :
    eo_interprets M emptyStrInRe true := by
  apply RuleProofs.eo_interprets_of_bool_eval M _ true empty_str_in_re_has_bool_type
  unfold emptyStrInRe mkStrInRe
  change __smtx_model_eval M
      (SmtTerm.str_in_re (SmtTerm.String (native_string_lit ""))
        (SmtTerm.str_to_re (SmtTerm.String (native_string_lit "")))) =
    SmtValue.Boolean true
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re, __smtx_model_eval_str_in_re,
    native_str_to_re, Smtm.native_str_in_re, impl_native_re_of_list, native_pack_string,
    native_pack_seq, native_unpack_seq,
    native_re_nullable, native_re_str_valid, native_string_lit]

private theorem mk_re_concat_cons_shape
    (p : Term) (ps : List Term) (accS accR : Term) :
    __mk_re_concat (premiseAndFormulaList (p :: ps)) (mkStrInRe accS accR) ≠ Term.Stuck ->
    ∃ s r,
      p = mkStrInRe s r ∧
      __mk_re_concat (premiseAndFormulaList (p :: ps)) (mkStrInRe accS accR) =
        __mk_re_concat (premiseAndFormulaList ps)
          (mkStrInRe (mkStrConcat s accS) (mkReConcat r accR)) := by
  intro h
  cases p with
  | Apply f r =>
      cases f with
      | Apply op s =>
          cases op with
          | UOp u =>
              cases u <;> try (simp [premiseAndFormulaList, mkStrInRe, __mk_re_concat] at h)
              case str_in_re =>
                exact ⟨s, r, rfl, by rfl⟩
          | _ => simp [premiseAndFormulaList, mkStrInRe, __mk_re_concat] at h
      | _ => simp [premiseAndFormulaList, mkStrInRe, __mk_re_concat] at h
  | _ => simp [premiseAndFormulaList, mkStrInRe, __mk_re_concat] at h

private theorem mk_re_concat_premises_has_bool_type :
    ∀ (qs : List Term) (accS accR : Term),
      AllHaveBoolType qs ->
      RuleProofs.eo_has_bool_type (mkStrInRe accS accR) ->
      __mk_re_concat (premiseAndFormulaList qs) (mkStrInRe accS accR) ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type
        (__mk_re_concat (premiseAndFormulaList qs) (mkStrInRe accS accR))
  | [], accS, accR, _hQsBool, hAccBool, _hNe => by
      simpa [premiseAndFormulaList, mkStrInRe, __mk_re_concat] using hAccBool
  | p :: ps, accS, accR, hQsBool, hAccBool, hNe => by
      rcases mk_re_concat_cons_shape p ps accS accR hNe with ⟨s, r, hp, hEq⟩
      have hPBool : RuleProofs.eo_has_bool_type (mkStrInRe s r) := by
        have h := hQsBool p (by simp)
        simpa [hp] using h
      have hNewBool :
          RuleProofs.eo_has_bool_type
            (mkStrInRe (mkStrConcat s accS) (mkReConcat r accR)) :=
        str_in_re_concat_has_bool_type s r accS accR hPBool hAccBool
      have hTailBool : AllHaveBoolType ps := by
        intro q hq
        exact hQsBool q (by simp [hq])
      have hTailNe :
          __mk_re_concat (premiseAndFormulaList ps)
              (mkStrInRe (mkStrConcat s accS) (mkReConcat r accR)) ≠ Term.Stuck := by
        intro hStuck
        exact hNe (by rw [hEq, hStuck])
      simpa [hEq] using
        mk_re_concat_premises_has_bool_type ps
          (mkStrConcat s accS) (mkReConcat r accR)
          hTailBool hNewBool hTailNe

private theorem mk_re_concat_premises_true
    (M : SmtModel) :
    ∀ (qs : List Term) (accS accR : Term),
      AllHaveBoolType qs ->
      AllInterpretedTrue M qs ->
      RuleProofs.eo_has_bool_type (mkStrInRe accS accR) ->
      eo_interprets M (mkStrInRe accS accR) true ->
      __mk_re_concat (premiseAndFormulaList qs) (mkStrInRe accS accR) ≠ Term.Stuck ->
      eo_interprets M
        (__mk_re_concat (premiseAndFormulaList qs) (mkStrInRe accS accR)) true
  | [], accS, accR, _hQsBool, _hQsTrue, _hAccBool, hAccTrue, _hNe => by
      simpa [premiseAndFormulaList, mkStrInRe, __mk_re_concat] using hAccTrue
  | p :: ps, accS, accR, hQsBool, hQsTrue, hAccBool, hAccTrue, hNe => by
      rcases mk_re_concat_cons_shape p ps accS accR hNe with ⟨s, r, hp, hEq⟩
      have hPBool : RuleProofs.eo_has_bool_type (mkStrInRe s r) := by
        have h := hQsBool p (by simp)
        simpa [hp] using h
      have hPTrue : eo_interprets M (mkStrInRe s r) true := by
        have h := hQsTrue p (by simp)
        simpa [hp] using h
      have hNewBool :
          RuleProofs.eo_has_bool_type
            (mkStrInRe (mkStrConcat s accS) (mkReConcat r accR)) :=
        str_in_re_concat_has_bool_type s r accS accR hPBool hAccBool
      have hNewTrue :
          eo_interprets M (mkStrInRe (mkStrConcat s accS) (mkReConcat r accR)) true :=
        facts_str_in_re_concat M s r accS accR hPBool hAccBool hPTrue hAccTrue
      have hTailBool : AllHaveBoolType ps := by
        intro q hq
        exact hQsBool q (by simp [hq])
      have hTailTrue : AllInterpretedTrue M ps := by
        intro q hq
        exact hQsTrue q (by simp [hq])
      have hTailNe :
          __mk_re_concat (premiseAndFormulaList ps)
              (mkStrInRe (mkStrConcat s accS) (mkReConcat r accR)) ≠ Term.Stuck := by
        intro hStuck
        exact hNe (by rw [hEq, hStuck])
      simpa [hEq] using
        mk_re_concat_premises_true M ps
          (mkStrConcat s accS) (mkReConcat r accR)
          hTailBool hTailTrue hNewBool hNewTrue hTailNe

public theorem cmd_step_re_concat_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_concat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_concat args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      let ps := premiseTermList s premises
      have hMkPrem :
          __eo_mk_premise_list (Term.UOp UserOp.and) premises s =
            premiseAndFormulaList ps := by
        simpa [ps] using mk_premise_list_and_eq_premiseAndFormulaList s premises
      change StepRuleProperties M ps
        (__mk_re_concat
          (__eo_list_rev (Term.UOp UserOp.and)
            (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))
          emptyStrInRe)
      rw [hMkPrem, eo_list_rev_and_premiseAndFormulaList ps]
      have hProgLocal :
          __mk_re_concat (premiseAndFormulaList ps.reverse) emptyStrInRe ≠ Term.Stuck := by
        change __mk_re_concat
            (__eo_list_rev (Term.UOp UserOp.and)
              (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))
            emptyStrInRe ≠ Term.Stuck at hProg
        rw [hMkPrem, eo_list_rev_and_premiseAndFormulaList ps] at hProg
        exact hProg
      have hRevBool : AllHaveBoolType ps.reverse :=
        all_have_bool_type_reverse ps hPremisesBool
      have hResultBool :
          RuleProofs.eo_has_bool_type
            (__mk_re_concat (premiseAndFormulaList ps.reverse) emptyStrInRe) :=
        mk_re_concat_premises_has_bool_type ps.reverse (Term.String (native_string_lit ""))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String (native_string_lit "")))
          hRevBool empty_str_in_re_has_bool_type hProgLocal
      refine ⟨?_, ?_⟩
      · intro hTrue
        exact mk_re_concat_premises_true M ps.reverse (Term.String (native_string_lit ""))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String (native_string_lit "")))
          hRevBool (all_interpreted_true_reverse M ps hTrue.true_here)
          empty_str_in_re_has_bool_type (empty_str_in_re_true M) hProgLocal
      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hResultBool
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
