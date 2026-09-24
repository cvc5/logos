module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReInCStringProof

private abbrev lhs (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_in_re t)
    (Term.Apply (Term.UOp UserOp.str_to_re) s)

private abbrev rhs (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq t) s

private theorem eo_typeof_str_in_re_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_str_in_re A B ≠ Term.Stuck) :
    A = Term.Apply Term.Seq Term.Char ∧ B = Term.RegLan := by
  cases A with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_in_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_in_re] at h ⊢
                cases B with
                | UOp opb =>
                    cases opb <;> simp [__eo_typeof_str_in_re] at h ⊢
                | _ => simp [__eo_typeof_str_in_re] at h
            | _ => simp [__eo_typeof_str_in_re] at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

private theorem eo_typeof_str_to_re_eq_seq_char_of_ne_stuck (T : Term)
    (h : __eo_typeof_str_to_re T ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char := by
  cases T with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_to_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_to_re] at h ⊢
            | _ => simp [__eo_typeof_str_to_re] at h
      | _ => simp [__eo_typeof_str_to_re] at h
  | _ => simp [__eo_typeof_str_to_re] at h

private theorem list_typed_char_pack_unpack :
    ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs ->
        xs.map (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) = xs
  | [], _ => rfl
  | v :: vs, hxs => by
      rcases hxs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, hvc, _hc⟩
      rw [hvc]
      simpa [impl_native_ssm_char_of_value] using list_typed_char_pack_unpack hvs

private theorem native_pack_string_unpack_string_of_typeof_seq_char
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_string (native_unpack_string ss) = ss := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  unfold native_pack_string native_unpack_string
  simp only [List.map_map]
  change native_pack_seq SmtType.Char
      ((native_unpack_seq ss).map
        (fun v => SmtValue.Char (impl_native_ssm_char_of_value v))) =
    ss
  rw [hMap]
  simpa [hElem] using native_pack_unpack_seq ss

private theorem nativeListInRe_char_self
    (c : native_Char) (hc : native_char_valid c = true) :
    RuleProofs.nativeListInRe [c] (SmtRegLan.char c) = true := by
  simp [RuleProofs.nativeListInRe, native_re_deriv, native_re_nullable, hc]

private theorem nativeListInRe_re_of_list_self :
    ∀ pat : native_String,
      native_string_valid pat = true ->
        RuleProofs.nativeListInRe pat (impl_native_re_of_list pat) = true
  | [], _ => by
      simp [impl_native_re_of_list, RuleProofs.nativeListInRe, native_re_nullable]
  | c :: cs, hValid => by
      rcases RuleProofs.native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hHead : RuleProofs.nativeListInRe [c] (SmtRegLan.char c) = true :=
        nativeListInRe_char_self c hc
      have hTail : RuleProofs.nativeListInRe cs (impl_native_re_of_list cs) = true :=
        nativeListInRe_re_of_list_self cs hcs
      have hConcat :
          RuleProofs.nativeListInRe (c :: cs)
              (native_re_mk_concat (SmtRegLan.char c)
                (impl_native_re_of_list cs)) = true :=
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          (c :: cs) (SmtRegLan.char c) (impl_native_re_of_list cs)).2
          ⟨[c], cs, rfl, hHead, hTail⟩
      simpa [impl_native_re_of_list] using hConcat

private theorem native_str_in_re_str_to_re_self
    (pat : native_String)
    (hValid : native_string_valid pat = true) :
    native_str_in_re pat (native_str_to_re pat) = true := by
  rw [← RuleProofs.native_str_in_re_eq_model]
  simpa [RuleProofs.native_str_in_re, hValid, native_str_to_re] using
    nativeListInRe_re_of_list_self pat hValid

private theorem smtx_model_eval_re_in_cstring_eq
    (st ss : SmtSeq)
    (hStTy : __smtx_typeof_seq_value st = SmtType.Seq SmtType.Char)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    __smtx_model_eval_str_in_re (SmtValue.Seq st)
        (SmtValue.RegLan (native_str_to_re (native_unpack_seq ss))) =
      __smtx_model_eval_eq (SmtValue.Seq st) (SmtValue.Seq ss) := by
  have hStUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hStTy
  have hSsUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  change
    SmtValue.Boolean
        (Smtm.native_str_in_re (native_unpack_seq st)
          (native_str_to_re (native_unpack_seq ss))) =
      SmtValue.Boolean (native_veq (SmtValue.Seq st) (SmtValue.Seq ss))
  rw [hStUnpack, hSsUnpack]
  by_cases hEq : st = ss
  · subst st
    have hValid : native_string_valid (native_unpack_string ss) = true :=
      native_unpack_string_valid_of_typeof_seq_char hSsTy
    have hMem :
        native_str_in_re (native_unpack_string ss)
          (native_str_to_re (native_unpack_string ss)) = true :=
      native_str_in_re_str_to_re_self (native_unpack_string ss) hValid
    simp [hMem, native_veq]
  · have hValueNe : SmtValue.Seq st ≠ SmtValue.Seq ss := by
      intro hVal
      cases hVal
      exact hEq rfl
    have hMemFalse :
        native_str_in_re (native_unpack_string st)
          (native_str_to_re (native_unpack_string ss)) = false := by
      cases hMem :
          native_str_in_re (native_unpack_string st)
            (native_str_to_re (native_unpack_string ss))
      · rfl
      · have hMemStr :
            RuleProofs.native_str_in_re (native_unpack_string st)
                (native_str_to_re (native_unpack_string ss)) = true := by
          rw [RuleProofs.native_str_in_re_eq_model]
          exact hMem
        have hStrEq :
            native_unpack_string st = native_unpack_string ss :=
          RuleProofs.native_str_in_re_str_to_re_eq
            (native_unpack_string_valid_of_typeof_seq_char hStTy) hMemStr
        have hPackSt :
            native_pack_string (native_unpack_string st) = st :=
          native_pack_string_unpack_string_of_typeof_seq_char st hStTy
        have hPackSs :
            native_pack_string (native_unpack_string ss) = ss :=
          native_pack_string_unpack_string_of_typeof_seq_char ss hSsTy
        have hSeqEq : st = ss := by
          rw [← hPackSt, ← hPackSs, hStrEq]
        exact False.elim (hEq hSeqEq)
    simp [hMemFalse, native_veq, hValueNe]

private theorem smtx_typeof_str_to_re_of_seq_char
    (s : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
      SmtType.RegLan := by
  have hSSmtTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt s) = __eo_to_smt_type (__eo_typeof s) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation s hSTrans
    rw [hSTy] at hTyRaw
    have hsimpa := hTyRaw
    try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
    exact hsimpa
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hSSmtTy, native_ite, native_Teq]

private theorem typed___eo_prog_re_in_cstring_impl
    (a1 a2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char)
    (hA2Ty : __eo_typeof a2 = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (__eo_prog_re_in_cstring a1 a2) := by
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty] at hTyRaw
    have hsimpa := hTyRaw
    try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
    exact hsimpa
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a2) = __eo_to_smt_type (__eo_typeof a2) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a2 hA2Trans
    rw [hA2Ty] at hTyRaw
    have hsimpa := hTyRaw
    try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
    exact hsimpa
  have hStrToReTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) a2)) =
        SmtType.RegLan :=
    smtx_typeof_str_to_re_of_seq_char a2 hA2Trans hA2Ty
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs a1 a2)) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.str_in_re (__eo_to_smt a1)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) a2))) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hA1SmtTy, hStrToReTy, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt (rhs a1 a2)) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.eq (__eo_to_smt a1) (__eo_to_smt a2)) = SmtType.Bool
    rw [typeof_eq_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hA1SmtTy, hA2SmtTy,
      native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs a1 a2) (rhs a1 a2)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA1Ty
  have hA2NotStuck : a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA2Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA2Ty
  have hProg :
      __eo_prog_re_in_cstring a1 a2 =
        Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2) := by
    cases hA1 : a1 <;>
      first | exact False.elim (hA1NotStuck hA1) | all_goals
        cases hA2 : a2 <;>
          first | exact False.elim (hA2NotStuck hA2) | rfl
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_re_in_cstring_impl
    (M : SmtModel) (hM : model_wf M) (a1 a2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char)
    (hA2Ty : __eo_typeof a2 = Term.Apply Term.Seq Term.Char) :
    eo_interprets M (__eo_prog_re_in_cstring a1 a2) true := by
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty] at hTyRaw
    have hsimpa := hTyRaw
    try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
    exact hsimpa
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.Seq SmtType.Char := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a2) = __eo_to_smt_type (__eo_typeof a2) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a2 hA2Trans
    rw [hA2Ty] at hTyRaw
    have hsimpa := hTyRaw
    try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
    exact hsimpa
  have hA1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hA1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a1) (by
        unfold term_has_non_none_type
        rw [hA1SmtTy]
        simp)
  have hA2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hA2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a2) (by
        unfold term_has_non_none_type
        rw [hA2SmtTy]
        simp)
  rcases seq_value_canonical hA1EvalTy with ⟨st, hst⟩
  rcases seq_value_canonical hA2EvalTy with ⟨ss, hss⟩
  have hStTy : __smtx_typeof_seq_value st = SmtType.Seq SmtType.Char := by
    simpa [hst, __smtx_typeof_value] using hA1EvalTy
  have hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hss, __smtx_typeof_value] using hA2EvalTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2)) := by
    have hTyped :=
      typed___eo_prog_re_in_cstring_impl a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
    have hA1NotStuck : a1 ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hA1Ty
      have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
        native_decide
      exact hBad hA1Ty
    have hA2NotStuck : a2 ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hA2Ty
      have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
        native_decide
      exact hBad hA2Ty
    have hProg :
        __eo_prog_re_in_cstring a1 a2 =
          Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2) := by
      cases hA1 : a1 <;>
        first | exact False.elim (hA1NotStuck hA1) | all_goals
          cases hA2 : a2 <;>
            first | exact False.elim (hA2NotStuck hA2) | rfl
    rwa [hProg] at hTyped
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs a1 a2)) =
        __smtx_model_eval M (__eo_to_smt (rhs a1 a2)) := by
    change
      __smtx_model_eval M
          (SmtTerm.str_in_re (__eo_to_smt a1)
            (SmtTerm.str_to_re (__eo_to_smt a2))) =
        __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt a1) (__eo_to_smt a2))
    simp [__smtx_model_eval]
    change
      __smtx_model_eval_str_in_re
          (__smtx_model_eval M (__eo_to_smt a1))
          (__smtx_model_eval_str_to_re
            (__smtx_model_eval M (__eo_to_smt a2))) =
        __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt a1))
          (__smtx_model_eval M (__eo_to_smt a2))
    rw [hst, hss]
    simp [__smtx_model_eval_str_to_re]
    exact smtx_model_eval_re_in_cstring_eq st ss hStTy hSsTy
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA1Ty
  have hA2NotStuck : a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA2Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA2Ty
  have hProg :
      __eo_prog_re_in_cstring a1 a2 =
        Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2) := by
    cases hA1 : a1 <;>
      first | exact False.elim (hA1NotStuck hA1) | all_goals
        cases hA2 : a2 <;>
          first | exact False.elim (hA2NotStuck hA2) | rfl
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs a1 a2) (rhs a1 a2) hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt (rhs a1 a2)))

end ReInCStringProof

public theorem cmd_step_re_in_cstring_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_cstring args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_in_cstring args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_cstring args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_in_cstring args premises ≠ Term.Stuck :=
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
              cases premises with
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                  have hA1NotStuck : a1 ≠ Term.Stuck := by
                    intro hStuck
                    subst a1
                    apply hProg
                    rfl
                  have hA2NotStuck : a2 ≠ Term.Stuck := by
                    intro hStuck
                    subst a2
                    apply hProg
                    cases a1 <;> rfl
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.re_in_cstring
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        Term.Apply
                          (Term.Apply Term.eq
                            (ReInCStringProof.lhs a1 a2))
                          (ReInCStringProof.rhs a1 a2) := by
                    cases hA1 : a1 <;>
                      first | exact False.elim (hA1NotStuck hA1) | all_goals
                        cases hA2 : a2 <;>
                          first | exact False.elim (hA2NotStuck hA2) | rfl
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq
                      (__eo_typeof (ReInCStringProof.lhs a1 a2))
                      (__eo_typeof (ReInCStringProof.rhs a1 a2)) = Term.Bool
                    at hResultTy
                  have hLhsNotStuck :
                      __eo_typeof (ReInCStringProof.lhs a1 a2) ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof (ReInCStringProof.lhs a1 a2))
                      (__eo_typeof (ReInCStringProof.rhs a1 a2))
                      hResultTy).1
                  have hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char := by
                    change __eo_typeof_str_in_re (__eo_typeof a1)
                        (__eo_typeof
                          (Term.Apply (Term.UOp UserOp.str_to_re) a2)) ≠
                      Term.Stuck at hLhsNotStuck
                    exact (ReInCStringProof.eo_typeof_str_in_re_args_of_ne_stuck
                      (__eo_typeof a1)
                      (__eo_typeof
                        (Term.Apply (Term.UOp UserOp.str_to_re) a2))
                      hLhsNotStuck).1
                  have hStrToReTy :
                      __eo_typeof
                          (Term.Apply (Term.UOp UserOp.str_to_re) a2) =
                        Term.RegLan := by
                    change __eo_typeof_str_in_re (__eo_typeof a1)
                        (__eo_typeof
                          (Term.Apply (Term.UOp UserOp.str_to_re) a2)) ≠
                      Term.Stuck at hLhsNotStuck
                    exact (ReInCStringProof.eo_typeof_str_in_re_args_of_ne_stuck
                      (__eo_typeof a1)
                      (__eo_typeof
                        (Term.Apply (Term.UOp UserOp.str_to_re) a2))
                      hLhsNotStuck).2
                  have hA2Ty : __eo_typeof a2 = Term.Apply Term.Seq Term.Char := by
                    change __eo_typeof_str_to_re (__eo_typeof a2) =
                      Term.RegLan at hStrToReTy
                    have hStrToReNotStuck :
                        __eo_typeof_str_to_re (__eo_typeof a2) ≠ Term.Stuck := by
                      rw [hStrToReTy]
                      simp
                    exact ReInCStringProof.eo_typeof_str_to_re_eq_seq_char_of_ne_stuck
                      (__eo_typeof a2) hStrToReNotStuck
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_re_in_cstring a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (ReInCStringProof.typed___eo_prog_re_in_cstring_impl
                        a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty)⟩
                    intro _hTrue
                    exact ReInCStringProof.facts___eo_prog_re_in_cstring_impl
                      M hM a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
                  change StepRuleProperties M []
                    (__eo_prog_re_in_cstring a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
