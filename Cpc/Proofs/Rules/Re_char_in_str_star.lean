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

namespace ReCharInStrStarProof

private abbrev reStar (s : Term) : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) (Term.Apply (Term.UOp UserOp.str_to_re) s)

private abbrev lhs (c s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) c) (reStar s)

private abbrev rhs (c s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) s) c

private abbrev concl (c s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs c s)) (rhs c s)

private abbrev prem (c : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) (Term.Apply (Term.UOp UserOp.str_len) c))
    (Term.Numeral 1)

private theorem prog_form (c s P : Term)
    (hNe : __eo_prog_re_char_in_str_star c s (Proof.pf P) ≠ Term.Stuck) :
    P = prem c ∧ __eo_prog_re_char_in_str_star c s (Proof.pf P) = concl c s := by
  unfold __eo_prog_re_char_in_str_star at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i hPrem
    injection hPrem with hPremEq
    have hReqArg := RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ hNe
    have hReqEq := RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ hNe
    have hc := ReInterCstringProof.eo_eq_eq_true hReqArg
    rw [hc] at hPremEq
    exact ⟨hPremEq, hReqEq⟩
  · exact False.elim (hNe rfl)

private theorem eo_typeof_re_mult_arg_of_ne_stuck (T : Term)
    (h : __eo_typeof_re_mult T ≠ Term.Stuck) :
    T = Term.UOp UserOp.RegLan := by
  cases T with
  | UOp op => cases op <;> simp [__eo_typeof_re_mult] at h ⊢
  | _ => simp [__eo_typeof_re_mult] at h

private theorem nativeListInRe_single_mult (ch : native_Char) (R : SmtRegLan) :
    RuleProofs.nativeListInRe [ch] (native_re_mult R) =
      RuleProofs.nativeListInRe [ch] R := by
  cases R <;> simp [native_re_mult, RuleProofs.nativeListInRe, native_re_deriv,
    RuleProofs.native_re_nullable_mk_concat, native_re_nullable]

private theorem str_in_re_mult_single (ct : SmtSeq) (R : SmtRegLan)
    (hCtTy : __smtx_typeof_seq_value ct = SmtType.Seq SmtType.Char)
    (hLen : (native_unpack_seq ct).length = 1) :
    Smtm.native_str_in_re (native_unpack_seq ct) (native_re_mult R) =
      Smtm.native_str_in_re (native_unpack_seq ct) R := by
  have hStrLen : (native_unpack_string ct).length = 1 := by
    simpa [native_unpack_string] using hLen
  rw [native_unpack_seq_eq_string_to_values_of_typeof_seq_char hCtTy,
    ← RuleProofs.native_str_in_re_eq_model,
    ← RuleProofs.native_str_in_re_eq_model]
  generalize native_unpack_string ct = str at hStrLen ⊢
  match str, hStrLen with
  | [ch], _ =>
      simp [RuleProofs.native_str_in_re, nativeListInRe_single_mult]

private theorem smtx_model_eval_char_in_star_eq
    (ct ss : SmtSeq)
    (hCtTy : __smtx_typeof_seq_value ct = SmtType.Seq SmtType.Char)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hLen : (native_unpack_seq ct).length = 1) :
    __smtx_model_eval_str_in_re (SmtValue.Seq ct)
        (SmtValue.RegLan
          (native_re_mult (native_str_to_re (native_unpack_seq ss)))) =
      __smtx_model_eval_eq (SmtValue.Seq ss) (SmtValue.Seq ct) := by
  have h := smtx_model_eval_re_in_cstring_eq ct ss hCtTy hSsTy
  change SmtValue.Boolean
      (Smtm.native_str_in_re (native_unpack_seq ct)
        (native_re_mult (native_str_to_re (native_unpack_seq ss)))) = _
  rw [str_in_re_mult_single ct _ hCtTy hLen]
  change SmtValue.Boolean
      (Smtm.native_str_in_re (native_unpack_seq ct)
        (native_str_to_re (native_unpack_seq ss))) = _ at h
  rw [h]
  simp [__smtx_model_eval_eq, native_veq, eq_comm]

private theorem len_one_of_prem (M : SmtModel) (c : Term) (ct : SmtSeq)
    (hCEval : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq ct)
    (hPrem : eo_interprets M (prem c) true) :
    (native_unpack_seq ct).length = 1 := by
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.UOp UserOp.str_len) c) (Term.Numeral 1) hPrem
  have hLenEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) c)) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ct).length) := by
    change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt c)) = _
    simp [__smtx_model_eval, hCEval, __smtx_model_eval_str_len, native_seq_len]
  have hOneEval :
      __smtx_model_eval M (__eo_to_smt (Term.Numeral 1)) =
        SmtValue.Numeral 1 := by
    change __smtx_model_eval M (SmtTerm.Numeral 1) = SmtValue.Numeral 1
    simp [__smtx_model_eval]
  rw [hLenEval, hOneEval] at hPremRel
  have hValueEq :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  injection hValueEq with hInt
  exact Int.ofNat.inj hInt

private theorem main
    (M : SmtModel) (hM : model_wf M) (c s P : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation c)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hProgNe : __eo_prog_re_char_in_str_star c s (Proof.pf P) ≠ Term.Stuck)
    (hResultTy :
      __eo_typeof (__eo_prog_re_char_in_str_star c s (Proof.pf P)) =
        Term.Bool) :
    StepRuleProperties M [P]
      (__eo_prog_re_char_in_str_star c s (Proof.pf P)) := by
  obtain ⟨hPShape, hProgEq⟩ := prog_form c s P hProgNe
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq (__eo_typeof (lhs c s)) (__eo_typeof (rhs c s)) =
    Term.Bool at hResultTy
  have hLhsNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  change __eo_typeof_str_in_re (__eo_typeof c) (__eo_typeof (reStar s)) ≠
    Term.Stuck at hLhsNotStuck
  obtain ⟨hCTy, hStarTy⟩ :=
    eo_typeof_str_in_re_args_of_ne_stuck _ _ hLhsNotStuck
  change __eo_typeof_re_mult
      (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
    Term.RegLan at hStarTy
  have hStrToReTy :=
    eo_typeof_re_mult_arg_of_ne_stuck _ (by rw [hStarTy]; simp)
  change __eo_typeof_str_to_re (__eo_typeof s) = Term.UOp UserOp.RegLan
    at hStrToReTy
  have hSTy :=
    eo_typeof_str_to_re_eq_seq_char_of_ne_stuck _ (by rw [hStrToReTy]; simp)
  have hCSmtTy := smt_seq_char_of_eo_type c hCTrans hCTy
  have hSSmtTy := smt_seq_char_of_eo_type s hSTrans hSTy
  have hStrToReSmtTy :
      __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) = SmtType.RegLan := by
    rw [typeof_str_to_re_eq]
    simp [hSSmtTy, native_ite, native_Teq]
  have hStarSmtTy :
      __smtx_typeof (SmtTerm.re_mult (SmtTerm.str_to_re (__eo_to_smt s))) =
        SmtType.RegLan := by
    rw [typeof_re_mult_eq]
    simp [hStrToReSmtTy, native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs c s)) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.str_in_re (__eo_to_smt c)
        (SmtTerm.re_mult (SmtTerm.str_to_re (__eo_to_smt s)))) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hCSmtTy, hStarSmtTy, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt (rhs c s)) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt c)) = SmtType.Bool
    rw [typeof_eq_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hCSmtTy, hSSmtTy,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type (concl c s) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs c s) (rhs c s)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool⟩
  intro hEv
  have hPrem : eo_interprets M (prem c) true := by
    have hHere := hEv.true_here P (by simp)
    simpa [hPShape] using hHere
  rcases seq_char_eval M hM c hCSmtTy with ⟨ct, hCEval, hCtTy⟩
  rcases seq_char_eval M hM s hSSmtTy with ⟨ss, hSEval, hSsTy⟩
  have hLen := len_one_of_prem M c ct hCEval hPrem
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs c s)) =
        __smtx_model_eval M (__eo_to_smt (rhs c s)) := by
    change
      __smtx_model_eval M
          (SmtTerm.str_in_re (__eo_to_smt c)
            (SmtTerm.re_mult (SmtTerm.str_to_re (__eo_to_smt s)))) =
        __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt c))
    simp [__smtx_model_eval]
    change
      __smtx_model_eval_str_in_re
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval_re_mult
            (__smtx_model_eval_str_to_re
              (__smtx_model_eval M (__eo_to_smt s)))) =
        __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt c))
    rw [hCEval, hSEval]
    simp only [__smtx_model_eval_str_to_re, __smtx_model_eval_re_mult]
    exact smtx_model_eval_char_in_star_eq ct ss hCtTy hSsTy hLen
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs c s) (rhs c s) hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

end ReCharInStrStarProof

public theorem cmd_step_re_char_in_str_star_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_char_in_str_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_char_in_str_star args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_char_in_str_star args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.re_char_in_str_star args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨_, _⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  rcases premises with _ | ⟨n, _ | ⟨_, _⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  have hTrans :
      cArgListTranslationOk (CArgList.cons a1 (CArgList.cons a2 CArgList.nil)) :=
    hCmdTrans
  exact ReCharInStrStarProof.main M hM a1 a2 (__eo_state_proven_nth s n)
    hTrans.1 hTrans.2.1 hProg hResultTy
