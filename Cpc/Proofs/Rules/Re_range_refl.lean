module

public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReRangeReflProof

private abbrev mkLenOne (s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.str_len) s))
    (Term.Numeral 1)

private abbrev lhs (s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s) s

private abbrev rhs (s : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) s

private abbrev concl (s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs s)) (rhs s)

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not, SmtEval.native_not]
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

private theorem eo_typeof_eq_bool_operands_not_stuck (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · exact ⟨hA, hB⟩

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

private theorem prog_form (s P : Term)
    (hNe : __eo_prog_re_range_refl s (Proof.pf P) ≠ Term.Stuck) :
    P = mkLenOne s ∧
      __eo_prog_re_range_refl s (Proof.pf P) = concl s := by
  unfold __eo_prog_re_range_refl at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · rename_i heqP
    injection heqP with hP
    have hReqArg := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    have hsEq := eo_eq_eq_true hReqArg
    rw [hsEq] at hP
    exact ⟨hP, hReqEq⟩
  · exact False.elim (hNe rfl)

private theorem native_unpack_string_singleton_of_seq_len_one (ss : SmtSeq)
    (hLen : native_seq_len (native_unpack_seq ss) = 1) :
    ∃ c : native_Char, native_unpack_string ss = [c] := by
  cases hUnpack : native_unpack_seq ss with
  | nil =>
      simp [native_seq_len, hUnpack] at hLen
  | cons v vs =>
      cases vs with
      | nil =>
          exact ⟨impl_native_ssm_char_of_value v, by simp [native_unpack_string, hUnpack]⟩
      | cons w ws =>
          have hLen' : (Int.ofNat (List.length (v :: w :: ws))) = 1 := by
            simpa [native_seq_len, hUnpack] using hLen
          have hLen'' : (Int.ofNat ws.length) + 1 + 1 = 1 := by
            simpa using hLen'
          have hNonneg : (0 : Int) ≤ Int.ofNat ws.length := Int.natCast_nonneg _
          omega

private theorem native_string_valid_cons_parts
    {c : native_Char} {cs : native_String}
    (h : native_string_valid (c :: cs) = true) :
    native_char_valid c = true ∧ native_string_valid cs = true := by
  simp [native_string_valid] at h
  constructor
  · exact h.1
  · rw [native_string_valid, List.all_eq_true]
    intro x hx
    exact h.2 x hx

private theorem native_str_in_re_range_refl_eq_str_to_re
    (c : native_Char) (hc : native_char_valid c = true)
    (str : native_String) (hValid : native_string_valid str = true) :
    native_str_in_re str (native_re_range [c] [c]) =
      native_str_in_re str (native_str_to_re [c]) := by
  cases str with
  | nil =>
      simp [native_re_range, native_str_to_re, impl_native_re_of_list,
        native_re_mk_concat, native_re_concat, native_str_in_re, impl_native_string_to_values,
              native_re_str_valid, native_re_elem_valid, impl_native_re_elem_le, hValid, native_re_nullable]
  | cons d rest =>
      rcases native_string_valid_cons_parts hValid with ⟨hd, hRestValid⟩
      cases rest with
      | nil =>
          by_cases hdc : d = c
          · subst d
            simp [native_re_range, native_str_to_re, impl_native_re_of_list,
              native_re_mk_concat, native_re_concat, native_str_in_re, impl_native_string_to_values,
              native_re_str_valid, native_re_elem_valid, impl_native_re_elem_le, hValid, native_re_deriv,
              native_re_nullable, hc]
          · have hBounds : ¬ (c ≤ d ∧ d ≤ c) := by
              intro h
              exact hdc (Nat.le_antisymm h.2 h.1)
            simp [native_re_range, native_str_to_re, impl_native_re_of_list,
              native_re_mk_concat, native_re_concat, native_str_in_re, impl_native_string_to_values,
              native_re_str_valid, native_re_elem_valid, impl_native_re_elem_le, hValid, native_re_deriv,
              native_re_nullable, hc, hd, hdc, hBounds]
      | cons e es =>
          have hTailEmpty := RuleProofs.nativeListInRe_empty es
          by_cases hBounds : c ≤ d ∧ d ≤ c
          · have hdc : d = c := Nat.le_antisymm hBounds.2 hBounds.1
            subst d
            simp [native_re_range, native_str_to_re, impl_native_re_of_list,
              native_re_mk_concat, native_re_concat, native_str_in_re, impl_native_string_to_values,
              native_re_str_valid, native_re_elem_valid, impl_native_re_elem_le, hValid, native_re_deriv,
              native_re_nullable, hc, RuleProofs.nativeListInRe, hTailEmpty]
          · have hdc : d ≠ c := by
              intro hdc
              subst d
              exact hBounds ⟨Nat.le_refl c, Nat.le_refl c⟩
            simp [native_re_range, native_str_to_re, impl_native_re_of_list,
              native_re_mk_concat, native_re_concat, native_str_in_re, impl_native_string_to_values,
              native_re_str_valid, native_re_elem_valid, impl_native_re_elem_le, hValid, native_re_deriv,
              native_re_nullable, hc, hd, hdc, hBounds, RuleProofs.nativeListInRe,
              hTailEmpty]

private theorem typed_concl
    (s : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (concl s) := by
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs s)) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_range (__eo_to_smt s) (__eo_to_smt s)) =
      SmtType.RegLan
    rw [typeof_re_range_eq]
    simp [hSTy, native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs s)) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
      SmtType.RegLan
    rw [typeof_str_to_re_eq]
    simp [hSTy, native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs s) (rhs s)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; decide)

private theorem facts
    (M : SmtModel) (hM : model_wf M) (s : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hPrem : eo_interprets M (mkLenOne s) true) :
    eo_interprets M (concl s) true := by
  have hBool : RuleProofs.eo_has_bool_type (concl s) :=
    typed_concl s hSTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases seq_value_canonical hEvalTy with ⟨ss, hSEval⟩
  have hSSTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simp only [hSEval] at hEvalTy
    exact hEvalTy
  have hSSValid : native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSSTy
  have hUnpack :
      native_unpack_seq ss = impl_native_string_to_values (native_unpack_string ss) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSSTy
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.UOp UserOp.str_len) s) (Term.Numeral 1) hPrem
  have hLenEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
        SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) := by
    change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
      SmtValue.Numeral (native_seq_len (native_unpack_seq ss))
    simp [__smtx_model_eval, __smtx_model_eval_str_len, hSEval]
  have hOneEval :
      __smtx_model_eval M (__eo_to_smt (Term.Numeral 1)) =
        SmtValue.Numeral 1 := by
    change __smtx_model_eval M (SmtTerm.Numeral 1) = SmtValue.Numeral 1
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hLenEval, hOneEval] at hPremRel
  have hLenValueEq :
      SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) =
        SmtValue.Numeral 1 :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  have hLen : native_seq_len (native_unpack_seq ss) = 1 := by
    injection hLenValueEq
  rcases native_unpack_string_singleton_of_seq_len_one ss hLen with ⟨c, hString⟩
  have hc : native_char_valid c = true := by
    simpa [hString, native_string_valid] using hSSValid
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs s)) =
        SmtValue.RegLan
          (native_re_range (native_unpack_string ss) (native_unpack_string ss)) := by
    change __smtx_model_eval M (SmtTerm.re_range (__eo_to_smt s) (__eo_to_smt s)) =
      SmtValue.RegLan
        (native_re_range (native_unpack_string ss) (native_unpack_string ss))
    simp [__smtx_model_eval, __smtx_model_eval_re_range, hSEval, hUnpack]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (rhs s)) =
        SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) := by
    change __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt s)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss))
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hSEval, hUnpack]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs s) (rhs s) hBool <| by
    rw [hLhsEval, hRhsEval, hString]
    change SmtValue.Boolean
        (native_re_ext_eq (native_re_range [c] [c]) (native_str_to_re [c])) =
      SmtValue.Boolean true
    congr
    simp
    intro str hValid
    exact native_str_in_re_range_refl_eq_str_to_re c hc str hValid

end ReRangeReflProof

public theorem cmd_step_re_range_refl_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_range_refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_range_refl args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_range_refl args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_range_refl args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  show StepRuleProperties M [__eo_state_proven_nth s n1]
                    (__eo_prog_re_range_refl a1
                      (Proof.pf (__eo_state_proven_nth s n1)))
                  generalize hP : __eo_state_proven_nth s n1 = P
                  have hProgNe :
                      __eo_prog_re_range_refl a1 (Proof.pf P) ≠ Term.Stuck := by
                    rw [← hP]
                    change __eo_cmd_step_proven s CRule.re_range_refl
                        (CArgList.cons a1 CArgList.nil)
                        (CIndexList.cons n1 CIndexList.nil) ≠ Term.Stuck
                    exact hProg
                  obtain ⟨hPremShape, hProgEq⟩ :=
                    ReRangeReflProof.prog_form a1 P hProgNe
                  have hResultTyProg :
                      __eo_typeof (__eo_prog_re_range_refl a1 (Proof.pf P)) =
                        Term.Bool := by
                    rw [← hP]
                    change __eo_typeof (__eo_cmd_step_proven s CRule.re_range_refl
                        (CArgList.cons a1 CArgList.nil)
                        (CIndexList.cons n1 CIndexList.nil)) = Term.Bool
                    exact hResultTy
                  have hConclTy :
                      __eo_typeof (ReRangeReflProof.concl a1) = Term.Bool := by
                    rw [hProgEq] at hResultTyProg
                    exact hResultTyProg
                  have hRhsTyNe :
                      __eo_typeof (ReRangeReflProof.rhs a1) ≠ Term.Stuck := by
                      change __eo_typeof_eq
                          (__eo_typeof (ReRangeReflProof.lhs a1))
                          (__eo_typeof (ReRangeReflProof.rhs a1)) =
                        Term.Bool at hConclTy
                      exact (ReRangeReflProof.eo_typeof_eq_bool_operands_not_stuck
                        (__eo_typeof (ReRangeReflProof.lhs a1))
                        (__eo_typeof (ReRangeReflProof.rhs a1)) hConclTy).2
                  have hA1Ty :
                      __eo_typeof a1 = Term.Apply Term.Seq Term.Char := by
                    change __eo_typeof_str_to_re (__eo_typeof a1) ≠
                      Term.Stuck at hRhsTyNe
                    exact ReRangeReflProof.eo_typeof_str_to_re_eq_seq_char_of_ne_stuck
                      (__eo_typeof a1) hRhsTyNe
                  have hA1SmtTy :
                      __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char := by
                    have hTyRaw :
                        __smtx_typeof (__eo_to_smt a1) =
                          __eo_to_smt_type (__eo_typeof a1) :=
                      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
                    rw [hA1Ty] at hTyRaw
                    simp only [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hTyRaw
                    exact hTyRaw
                  have hBool :=
                    ReRangeReflProof.typed_concl a1 hA1SmtTy
                  rw [hProgEq]
                  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                    hBool⟩
                  intro hEv
                  have hPrem :
                      eo_interprets M (ReRangeReflProof.mkLenOne a1) true := by
                    have h := hEv.true_here P (by simp)
                    rwa [hPremShape] at h
                  exact ReRangeReflProof.facts M hM a1 hA1SmtTy hPrem
