module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport
public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport
public import Cpc.Proofs.RuleSupport.StrContainsConcatSupport
import all Cpc.Proofs.RuleSupport.StrContainsConcatSupport
public import Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
import all Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrContainsStripFromIntPreProof

private abbrev op : Term := Term.UOp UserOp.str_concat

private abbrev concat (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private abbrev fromInt (n : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_from_int) n

private abbrev ctn (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y

private abbrev prem (s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.str_is_digit)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s)
            (Term.Numeral 0))
          (Term.Numeral 1))))
    (Term.Boolean false)

private abbrev lhs (n x xs s : Term) : Term :=
  ctn (concat (fromInt n) (concat x xs)) s

private abbrev rhs (x xs s : Term) : Term :=
  ctn (__eo_list_singleton_elim op (concat x xs)) s

private abbrev concl (n x xs s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs n x xs s))
    (rhs x xs s)

private theorem mk_apply_fun_ne_stuck_local {f x : Term}
    (h : __eo_mk_apply f x ≠ Term.Stuck) : f ≠ Term.Stuck := by
  intro hf
  subst f
  cases x <;> simp [__eo_mk_apply] at h

private theorem mk_apply_arg_ne_stuck_local {f x : Term}
    (h : __eo_mk_apply f x ≠ Term.Stuck) : x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem mk_apply_eq_apply_local {f x : Term}
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  have hf := mk_apply_fun_ne_stuck_local h
  have hx := mk_apply_arg_ne_stuck_local h
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem requires_eq_of_ne_stuck_local {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) : x = y := by
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

private theorem requires_body_of_ne_stuck_local {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) : __eo_requires x y z = z := by
  have hxy := requires_eq_of_ne_stuck_local h
  subst hxy
  unfold __eo_requires at h ⊢
  by_cases hs : x = Term.Stuck
  · subst hs
    simp [native_teq, native_ite, native_not, SmtEval.native_not] at h
  · simp [native_teq, native_ite, native_not, SmtEval.native_not, hs]

private theorem prog_info (n x xs s P : Term)
    (hProg :
      __eo_prog_str_contains_strip_from_int_pre n x xs s (Proof.pf P) ≠
        Term.Stuck) :
    P = prem s ∧
      __eo_is_list op (concat x xs) = Term.Boolean true ∧
      __eo_prog_str_contains_strip_from_int_pre n x xs s (Proof.pf P) =
        concl n x xs s := by
  unfold __eo_prog_str_contains_strip_from_int_pre at hProg ⊢
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hS := RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    have hBody := requires_body_of_ne_stuck_local hProg
    rw [hBody] at hProg
    have hR := mk_apply_arg_ne_stuck_local hProg
    have hRF := mk_apply_fun_ne_stuck_local hR
    have hE := mk_apply_arg_ne_stuck_local hRF
    have hList := requires_eq_of_ne_stuck_local hE
    refine ⟨rfl, hList, ?_⟩
    simp only []
    rw [hBody, mk_apply_eq_apply_local hProg, mk_apply_eq_apply_local hR,
      mk_apply_eq_apply_local hRF]

/-! ### Native facts -/

private theorem digit_values_of_from_int (z : native_Int) :
    ∀ v ∈ (native_str_from_int z).map SmtValue.Char,
      ∃ ch, v = SmtValue.Char ch ∧ impl_native_char_is_digit ch = true := by
  intro v hv
  rcases List.mem_map.mp hv with ⟨ch, hch, rfl⟩
  have hAll := StrInReFromIntDigRangeProof.native_str_from_int_all_digits z
  rw [List.all_eq_true] at hAll
  exact ⟨ch, rfl, hAll ch hch⟩

private theorem no_compat_digits
    (Dv : List SmtValue) (c : SmtValue)
    (hDigits : ∀ v ∈ Dv,
      ∃ ch, v = SmtValue.Char ch ∧ impl_native_char_is_digit ch = true)
    (hc : impl_native_char_is_digit (impl_native_ssm_char_of_value c) = false) :
    ∀ k, k < Dv.length → ¬ RuleProofs.native_seq_compat (Dv.drop k) [c] := by
  intro k hk hCompat
  rcases hDigits _ (List.getElem_mem hk) with ⟨ch, hv, hch⟩
  have hDrop := List.drop_eq_getElem_cons hk
  generalize Dv.drop k = d at hCompat hDrop
  generalize Dv.drop (k + 1) = d' at hDrop
  subst hDrop
  have hEq : Dv[k] = c := by
    rcases hCompat with h | h
    · rcases (RuleProofs.native_seq_prefix_eq_iff _ _).1 h with ⟨r, hr⟩
      simp only [List.cons_append, List.cons.injEq] at hr
      exact hr.1.symm
    · rcases (RuleProofs.native_seq_prefix_eq_iff _ _).1 h with ⟨r, hr⟩
      simp only [List.cons_append, List.cons.injEq] at hr
      exact hr.1
  rw [← hEq, hv] at hc
  simp [impl_native_ssm_char_of_value, hch] at hc

private theorem contains_digits_prefix_eq
    (Dv R S : List SmtValue)
    (hDigits : ∀ v ∈ Dv,
      ∃ ch, v = SmtValue.Char ch ∧ impl_native_char_is_digit ch = true)
    (hS : S = [] ∨ ∃ c rest, S = c :: rest ∧
      impl_native_char_is_digit (impl_native_ssm_char_of_value c) = false) :
    native_seq_contains (Dv ++ R) S = native_seq_contains R S := by
  rcases hS with rfl | ⟨c, rest, rfl, hc⟩
  · rw [StrContainsReplCharSupport.native_seq_contains_nil,
      StrContainsReplCharSupport.native_seq_contains_nil]
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      have hTrim :=
        RuleProofs.native_seq_contains_drop_left_of_no_endpoint_overlap
          Dv R [c] rest (no_compat_digits Dv c hDigits hc) (by simpa using h)
      simpa using hTrim
    · intro h
      exact StrContainsConcatSupport.native_seq_contains_append_left Dv R _ h

/-! ### Premise evaluation -/

private theorem smtx_eval_str_is_digit_term_eq_local
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_is_digit x) =
      __smtx_model_eval_str_is_digit (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_substr_term_eq_local
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr (__smtx_model_eval M x)
        (__smtx_model_eval M y) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_local (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_local (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem is_digit_single_true (c : SmtValue) (T : SmtType)
    (hd : impl_native_char_is_digit (impl_native_ssm_char_of_value c) = true) :
    __smtx_model_eval_str_is_digit (SmtValue.Seq (native_pack_seq T [c])) =
      SmtValue.Boolean true := by
  have hValid := StrInReFromIntDigRangeProof.native_char_valid_of_digit _ hd
  have hd' := hd
  simp [impl_native_char_is_digit] at hd'
  simp [__smtx_model_eval_str_is_digit, __smtx_model_eval_str_to_code,
    native_unpack_string, Smtm.native_unpack_pack_seq, native_str_to_code,
    hValid, __smtx_model_eval_leq, __smtx_model_eval_and, native_and,
    SmtEval.native_zleq, hd'.1, hd'.2]

private theorem premise_first_char
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hPrem : eo_interprets M (prem s) true) :
    native_unpack_seq ss = [] ∨ ∃ c rest, native_unpack_seq ss = c :: rest ∧
      impl_native_char_is_digit (impl_native_ssm_char_of_value c) = false := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq
            (SmtTerm.str_is_digit
              (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
                (SmtTerm.Numeral 1)))
            (SmtTerm.Boolean false)) = SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq, smtx_eval_str_is_digit_term_eq_local,
        smtx_eval_str_substr_term_eq_local, hSEval, smtx_eval_numeral_local,
        smtx_eval_numeral_local, smtx_eval_boolean_local] at hEval
      cases hU : native_unpack_seq ss with
      | nil => exact Or.inl rfl
      | cons c rest =>
          refine Or.inr ⟨c, rest, rfl, ?_⟩
          cases hd : impl_native_char_is_digit (impl_native_ssm_char_of_value c)
          · rfl
          · exfalso
            have hExt : native_seq_extract (c :: rest) 0 1 = [c] := by
              simp [native_seq_extract]
            simp only [__smtx_model_eval_str_substr, hU, hExt,
              is_digit_single_true c _ hd] at hEval
            simp [__smtx_model_eval_eq, native_veq] at hEval

/-! ### Typing and semantics of the conclusion -/

private theorem contains_bool_type_local (x y : Term) (T : SmtType)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (ctn x y)) = SmtType.Bool := by
  change __smtx_typeof
      (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
  rw [typeof_str_contains_eq]
  simp [hX, hY, __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]

private theorem seq_eval_local
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    ∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq T := by
    simpa [hxTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hxTy]
        simp)
  exact seq_value_canonical hValTy

private theorem seq_char_smt_type_local (x : Term)
    (hTrans : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char := by
  simpa using
    StrConcatClashSupport.smtx_typeof_seq_of_eo_typeof x Term.Char hTrans hTy

private theorem main_facts
    (M : SmtModel) (hM : model_wf M) (n x xs s : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTy : __eo_typeof n = Term.Int)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq Term.Char)
    (hXsTy : __eo_typeof xs = Term.Apply Term.Seq Term.Char)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (hList : __eo_is_list op (concat x xs) = Term.Boolean true) :
    RuleProofs.eo_has_bool_type (concl n x xs s) ∧
      (eo_interprets M (prem s) true →
        eo_interprets M (concl n x xs s) true) := by
  have hNSmt :=
    StrInReFromIntDigRangeProof.smtx_typeof_of_eo_int n hNTrans hNTy
  have hXSmt := seq_char_smt_type_local x hXTrans hXTy
  have hXsSmt := seq_char_smt_type_local xs hXsTrans hXsTy
  have hSSmt := seq_char_smt_type_local s hSTrans hSTy
  have hFTy :
      __smtx_typeof (__eo_to_smt (fromInt n)) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) = _
    rw [typeof_str_from_int_eq, hNSmt]
    simp [native_ite, native_Teq]
  have hTlTy := smt_typeof_str_concat_of_seq x xs _ hXSmt hXsSmt
  have hWTy :=
    smt_typeof_str_concat_of_seq (fromInt n) (concat x xs) _ hFTy hTlTy
  have hETy :=
    StringRewriteSupport.singleton_elim_has_seq_type (concat x xs) _
      hList hTlTy
  have hLTy := contains_bool_type_local _ s _ hWTy hSSmt
  have hRTy := contains_bool_type_local _ s _ hETy hSSmt
  have hBool : RuleProofs.eo_has_bool_type (concl n x xs s) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs n x xs s)
      (rhs x xs s) (by rw [hLTy, hRTy]) (by rw [hLTy]; simp)
  refine ⟨hBool, fun hPrem => ?_⟩
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmt] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmt]
        simp)
  rcases int_value_canonical hNEvalTy with ⟨z, hNEval⟩
  rcases seq_eval_local M hM x _ hXSmt with ⟨sx, hXEval⟩
  rcases seq_eval_local M hM xs _ hXsSmt with ⟨sxs, hXsEval⟩
  rcases seq_eval_local M hM s _ hSSmt with ⟨ss, hSEval⟩
  rcases StrContainsConcatSupport.str_concat_unpack_eval M x xs sx sxs
      hXEval hXsEval with ⟨sTl, hTlEval, _hTlUnpack⟩
  have hFEval :
      __smtx_model_eval M (__eo_to_smt (fromInt n)) =
        SmtValue.Seq (native_pack_string (native_str_from_int z)) := by
    change __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt n)) = _
    rw [StrInReFromIntDigRangeProof.smtx_eval_str_from_int_term_eq, hNEval]
    rfl
  rcases StrContainsConcatSupport.str_concat_unpack_eval M (fromInt n)
      (concat x xs) _ sTl hFEval hTlEval with ⟨sW, hWEval, hWUnpack⟩
  have hEEval :=
    StringRewriteSupport.singleton_elim_eval M hM (concat x xs) _ sTl
      hList hTlTy hTlEval
  have hLEval :=
    StrContainsConcatSupport.str_contains_eval_eq M _ s sW ss hWEval hSEval
  have hREval :=
    StrContainsConcatSupport.str_contains_eval_eq M _ s sTl ss hEEval hSEval
  have hFirst := premise_first_char M s ss hSEval hPrem
  have hNative :
      native_seq_contains (native_unpack_seq sW) (native_unpack_seq ss) =
        native_seq_contains (native_unpack_seq sTl) (native_unpack_seq ss) := by
    rw [hWUnpack]
    have hD :
        native_unpack_seq (native_pack_string (native_str_from_int z)) =
          (native_str_from_int z).map SmtValue.Char := by
      simp [native_pack_string, Smtm.native_unpack_pack_seq]
    rw [hD]
    exact contains_digits_prefix_eq _ _ _ (digit_values_of_from_int z) hFirst
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ hBool (by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (StrContainsConcatSupport.containsTerm
          (concat (fromInt n) (concat x xs)) s)))
      (__smtx_model_eval M (__eo_to_smt
        (StrContainsConcatSupport.containsTerm
          (__eo_list_singleton_elim op (concat x xs)) s)))
    rw [hLEval, hREval, hNative]
    exact RuleProofs.smt_value_rel_refl _)

private theorem typeof_args_of_concl_bool (n x xs s : Term)
    (hTy : __eo_typeof (concl n x xs s) = Term.Bool) :
    __eo_typeof n = Term.Int ∧
      __eo_typeof x = Term.Apply Term.Seq Term.Char ∧
      __eo_typeof xs = Term.Apply Term.Seq Term.Char ∧
      __eo_typeof s = Term.Apply Term.Seq Term.Char := by
  change __eo_typeof_eq (__eo_typeof (lhs n x xs s))
      (__eo_typeof (rhs x xs s)) = Term.Bool at hTy
  have hL := (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
  change __eo_typeof_str_contains
      (__eo_typeof (concat (fromInt n) (concat x xs)))
      (__eo_typeof s) ≠ Term.Stuck at hL
  rcases StrContainsReplCharSupport.eo_typeof_str_contains_args_of_ne_stuck
      _ _ hL with ⟨U, hW, hS⟩
  have hArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq _ _ U hW
  have hFromTy := hArgs.1
  have hNInt : __eo_typeof n = Term.Int := by
    change __eo_typeof_str_from_code (__eo_typeof n) =
      Term.Apply Term.Seq U at hFromTy
    cases hN : __eo_typeof n <;>
      simp [__eo_typeof_str_from_code, hN] at hFromTy
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_from_code, hN] at hFromTy
      case Int =>
        rfl
  have hFromChar :
      __eo_typeof (fromInt n) = Term.Apply Term.Seq Term.Char := by
    change __eo_typeof_str_from_code (__eo_typeof n) = _
    rw [hNInt]
    rfl
  have hU : U = Term.Char := by
    rw [hFromChar] at hFromTy
    exact (Term.Apply.inj hFromTy).2.symm
  subst hU
  have hTl :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq x xs _
      hArgs.2
  exact ⟨hNInt, hTl.1, hTl.2, hS⟩

end StrContainsStripFromIntPreProof

public theorem cmd_step_str_contains_strip_from_int_pre_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_strip_from_int_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_strip_from_int_pre args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_strip_from_int_pre args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_contains_strip_from_int_pre args
          premises ≠ Term.Stuck :=
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
        | nil => exact False.elim (hProg rfl)
        | cons a4 args =>
          cases args with
          | cons _ _ => exact False.elim (hProg rfl)
          | nil =>
            cases premises with
            | nil => exact False.elim (hProg rfl)
            | cons n1 premises =>
              cases premises with
              | cons _ _ => exact False.elim (hProg rfl)
              | nil =>
                have hTrans : cArgListTranslationOk
                    (CArgList.cons a1 (CArgList.cons a2
                      (CArgList.cons a3 (CArgList.cons a4 CArgList.nil)))) :=
                  hCmdTrans
                have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                  hTrans.1
                have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                  hTrans.2.1
                have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                  hTrans.2.2.1
                have hA4Trans : RuleProofs.eo_has_smt_translation a4 :=
                  hTrans.2.2.2.1
                let P := __eo_state_proven_nth s n1
                change __eo_typeof
                    (__eo_prog_str_contains_strip_from_int_pre a1 a2 a3 a4
                      (Proof.pf P)) = Term.Bool at hResultTy
                have hRuleProg :
                    __eo_prog_str_contains_strip_from_int_pre a1 a2 a3 a4
                        (Proof.pf P) ≠ Term.Stuck :=
                  term_ne_stuck_of_typeof_bool hResultTy
                rcases StrContainsStripFromIntPreProof.prog_info
                    a1 a2 a3 a4 P hRuleProg with ⟨hP, hList, hProgEq⟩
                rw [hProgEq] at hResultTy
                rcases StrContainsStripFromIntPreProof.typeof_args_of_concl_bool
                    a1 a2 a3 a4 hResultTy with ⟨hNTy, hXTy, hXsTy, hSTy⟩
                have hFacts := StrContainsStripFromIntPreProof.main_facts
                  M hM a1 a2 a3 a4 hA1Trans hA2Trans hA3Trans hA4Trans
                  hNTy hXTy hXsTy hSTy hList
                change StepRuleProperties M [P]
                  (__eo_prog_str_contains_strip_from_int_pre a1 a2 a3 a4
                    (Proof.pf P))
                rw [hProgEq]
                refine ⟨?_,
                  RuleProofs.eo_has_smt_translation_of_has_bool_type _
                    hFacts.1⟩
                intro hTrue
                have hPremRaw : eo_interprets M P true :=
                  hTrue.true_here P (by simp)
                exact hFacts.2 (by simpa [hP] using hPremRaw)
