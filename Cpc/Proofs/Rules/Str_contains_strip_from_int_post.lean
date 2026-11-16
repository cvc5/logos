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
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.RuleSupport.StrContainsStripFromIntSupport
import all Cpc.Proofs.RuleSupport.StrContainsStripFromIntSupport
public import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import all Cpc.Proofs.RuleSupport.RegexRewriteSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrContainsStripFromIntPostProof

open StrContainsStripFromIntSupport

private abbrev emp : Term := Term.String []

private abbrev sfx (n : Term) : Term := concat (fromInt n) emp

private abbrev wholeTail (x n : Term) : Term := concat x (sfx n)

private abbrev whole (xs x n : Term) : Term :=
  __eo_list_concat op xs (wholeTail x n)

private abbrev joinedTail (x : Term) : Term := concat x emp

private abbrev joined (xs x : Term) : Term :=
  __eo_list_concat op xs (joinedTail x)

private abbrev prem (s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.str_is_digit)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) s))
              (Term.Numeral 1)))
          (Term.Numeral 1))))
    (Term.Boolean false)

private abbrev lhs (xs x n s : Term) : Term :=
  ctn (whole xs x n) s

private abbrev rhs (xs x s : Term) : Term :=
  ctn (__eo_list_singleton_elim op (joined xs x)) s

private abbrev concl (xs x n s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs x n s))
    (rhs xs x s)

private theorem prog_info (xs x n s P : Term)
    (hProg :
      __eo_prog_str_contains_strip_from_int_post xs x n s (Proof.pf P) ≠
        Term.Stuck) :
    P = prem s ∧
      whole xs x n ≠ Term.Stuck ∧
      __eo_list_singleton_elim op (joined xs x) ≠ Term.Stuck ∧
      __eo_prog_str_contains_strip_from_int_post xs x n s (Proof.pf P) =
        concl xs x n s := by
  unfold __eo_prog_str_contains_strip_from_int_post at hProg ⊢
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨h2, h3⟩
    subst_vars
    have hBody := requires_body_of_ne_stuck hProg
    rw [hBody] at hProg
    have hR := mk_apply_arg_ne_stuck hProg
    have hEqF := mk_apply_fun_ne_stuck hProg
    have hL := mk_apply_arg_ne_stuck hEqF
    have hLF := mk_apply_fun_ne_stuck hL
    have hW := mk_apply_arg_ne_stuck hLF
    have hRF := mk_apply_fun_ne_stuck hR
    have hE := mk_apply_arg_ne_stuck hRF
    refine ⟨rfl, hW, hE, ?_⟩
    simp only []
    rw [hBody, mk_apply_eq_apply hProg, mk_apply_eq_apply hEqF,
      mk_apply_eq_apply hL, mk_apply_eq_apply hLF,
      mk_apply_eq_apply hR, mk_apply_eq_apply hRF]

/-! ### Native facts -/

private theorem contains_digits_suffix_eq
    (R Dv S : List SmtValue)
    (hDigits : ∀ v ∈ Dv,
      ∃ ch, v = SmtValue.Char ch ∧ impl_native_char_is_digit ch = true)
    (hS : S = [] ∨ ∃ L c, S = L ++ [c] ∧
      impl_native_char_is_digit (impl_native_ssm_char_of_value c) = false) :
    native_seq_contains (R ++ Dv) S = native_seq_contains R S := by
  rcases hS with rfl | ⟨L, c, rfl, hc⟩
  · rw [StrContainsReplCharSupport.native_seq_contains_nil,
      StrContainsReplCharSupport.native_seq_contains_nil]
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      have hRevDigits : ∀ v ∈ Dv.reverse,
          ∃ ch, v = SmtValue.Char ch ∧ impl_native_char_is_digit ch = true := by
        intro v hv
        exact hDigits v (List.mem_reverse.mp hv)
      exact RuleProofs.native_seq_contains_drop_right_of_no_endpoint_overlap
        R Dv L [c]
        (by simpa using no_compat_digits Dv.reverse c hRevDigits hc) h
    · intro h
      exact StrContainsConcatSupport.native_seq_contains_append_right R Dv _ h

/-! ### Premise evaluation -/

private theorem smtx_eval_neg_term_eq_local
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem extract_last (L : List SmtValue) (c : SmtValue) :
    native_seq_extract (L ++ [c])
        (native_zplus (native_seq_len (L ++ [c])) (native_zneg 1)) 1 = [c] := by
  have hIdx :
      native_zplus (native_seq_len (L ++ [c])) (native_zneg 1) =
        (L.length : Int) := by
    simp [native_zplus, native_zneg, native_seq_len, SmtEval.native_zplus]
  rw [hIdx]
  unfold native_seq_extract
  have hMin : min (1 : Int) ((L ++ [c]).length - (L.length : Int)) = 1 := by
    simp
  simp only [hMin]
  simp

private theorem premise_last_char
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hPrem : eo_interprets M (prem s) true) :
    native_unpack_seq ss = [] ∨ ∃ L c, native_unpack_seq ss = L ++ [c] ∧
      impl_native_char_is_digit (impl_native_ssm_char_of_value c) = false := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq
            (SmtTerm.str_is_digit
              (SmtTerm.str_substr (__eo_to_smt s)
                (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt s))
                  (SmtTerm.Numeral 1))
                (SmtTerm.Numeral 1)))
            (SmtTerm.Boolean false)) = SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq, smtx_eval_str_is_digit_term_eq,
        StrSubstrContainsSupport.smtx_eval_str_substr_term_eq, smtx_eval_neg_term_eq_local,
        smtx_eval_str_len_term_eq, hSEval, smtx_eval_numeral,
        smtx_eval_boolean] at hEval
      rcases List.eq_nil_or_concat (native_unpack_seq ss) with hNil | ⟨L, c, hU⟩
      · exact Or.inl hNil
      · rw [List.concat_eq_append] at hU
        refine Or.inr ⟨L, c, hU, ?_⟩
        cases hd : impl_native_char_is_digit (impl_native_ssm_char_of_value c)
        · rfl
        · exfalso
          simp only [__smtx_model_eval_str_len, __smtx_model_eval__,
            __smtx_model_eval_str_substr, hU] at hEval
          rw [extract_last, is_digit_single_true c _ hd] at hEval
          simp [__smtx_model_eval_eq, native_veq] at hEval

/-! ### Typing and semantics of the conclusion -/

private theorem rec_type_transfer (z : Term) (T : SmtType) :
    ∀ xs z',
      __eo_is_list op xs = Term.Boolean true →
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z)) =
        SmtType.Seq T →
      __smtx_typeof (__eo_to_smt z') = SmtType.Seq T →
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z')) =
        SmtType.Seq T := by
  intro xs z'
  induction xs, z' using __eo_list_concat_rec.induct with
  | case1 z' =>
      intro h
      simp [__eo_is_list] at h
  | case2 xs hxs =>
      intro _ _ h
      exact absurd rfl (term_ne_stuck_of_smt_type_seq _ T h)
  | case3 g x y z' hz' ih =>
      intro hList hTy hz'Ty
      have hg := eo_is_list_cons_head_eq_of_true op g x y hList
      subst hg
      have hyList := eo_is_list_tail_true_of_cons_self op x y hList
      have hzNe : z ≠ Term.Stuck := by
        intro h
        subst h
        have hS : __eo_list_concat_rec (concat x y) Term.Stuck = Term.Stuck := by
          simp [__eo_list_concat_rec]
        rw [hS] at hTy
        exact absurd rfl (term_ne_stuck_of_smt_type_seq _ T hTy)
      have hRecNe := eo_list_concat_rec_ne_stuck_of_list op y z hyList hzNe
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck x y z hRecNe]
        at hTy
      have hArgs := str_concat_args_of_seq_type x _ T hTy
      have hRest := ih hyList hArgs.2 hz'Ty
      have hRecNe' := eo_list_concat_rec_ne_stuck_of_list op y z' hyList hz'
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck x y z' hRecNe']
      exact smt_typeof_str_concat_of_seq _ _ T hArgs.1 hRest
  | case4 nil z' hNil hz' hNot =>
      intro _ _ hz'Ty
      simpa [__eo_list_concat_rec] using hz'Ty

private theorem emp_type_local :
    __smtx_typeof (__eo_to_smt emp) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.String []) = _
  rw [__smtx_typeof.eq_4]
  simp [native_string_valid, native_ite]

private theorem emp_eval_local (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt emp) =
      SmtValue.Seq (native_pack_string []) := by
  change __smtx_model_eval M (SmtTerm.String []) = _
  rw [__smtx_model_eval.eq_def]

private theorem main_facts
    (M : SmtModel) (hM : model_wf M) (xs x n s : Term)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTy : __eo_typeof n = Term.Int)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq Term.Char)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (hWholeTy :
      __smtx_typeof (__eo_to_smt (whole xs x n)) = SmtType.Seq SmtType.Char)
    (hXsList : __eo_is_list op xs = Term.Boolean true)
    (hWTailList : __eo_is_list op (wholeTail x n) = Term.Boolean true)
    (hJTailList : __eo_is_list op (joinedTail x) = Term.Boolean true) :
    RuleProofs.eo_has_bool_type (concl xs x n s) ∧
      (eo_interprets M (prem s) true →
        eo_interprets M (concl xs x n s) true) := by
  have hNSmt :=
    StrInReFromIntDigRangeProof.smtx_typeof_of_eo_int n hNTrans hNTy
  have hXSmt := seq_char_smt_type x hXTrans hXTy
  have hSSmt := seq_char_smt_type s hSTrans hSTy
  have hJTailTy := smt_typeof_str_concat_of_seq x emp _ hXSmt emp_type_local
  have hWholeRed :=
    StringRewriteSupport.list_concat_reduce xs (wholeTail x n) hXsList
      hWTailList
  have hJoinedRed :=
    StringRewriteSupport.list_concat_reduce xs (joinedTail x) hXsList
      hJTailList
  have hJoinedTy :
      __smtx_typeof (__eo_to_smt (joined xs x)) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof (__eo_to_smt
      (__eo_list_concat op xs (joinedTail x))) = _
    rw [hJoinedRed]
    exact rec_type_transfer (wholeTail x n) _ xs (joinedTail x) hXsList
      (by rw [← hWholeRed]; exact hWholeTy) hJTailTy
  have hJoinedList :=
    StringRewriteSupport.list_concat_is_list xs (joinedTail x) hXsList
      hJTailList
  have hETy :=
    StringRewriteSupport.singleton_elim_has_seq_type (joined xs x) _
      hJoinedList hJoinedTy
  have hLTy := contains_bool_type _ s _ hWholeTy hSSmt
  have hRTy := contains_bool_type _ s _ hETy hSSmt
  have hBool : RuleProofs.eo_has_bool_type (concl xs x n s) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs xs x n s)
      (rhs xs x s) (by rw [hLTy, hRTy]) (by rw [hLTy]; simp)
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
  rcases seq_eval M hM x _ hXSmt with ⟨sx, hXEval⟩
  rcases seq_eval M hM s _ hSSmt with ⟨ss, hSEval⟩
  have hFEval :
      __smtx_model_eval M (__eo_to_smt (fromInt n)) =
        SmtValue.Seq (native_pack_string (native_str_from_int z)) := by
    change __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt n)) = _
    rw [StrInReFromIntDigRangeProof.smtx_eval_str_from_int_term_eq, hNEval]
    rfl
  rcases StrContainsConcatSupport.str_concat_unpack_eval M (fromInt n) emp
      _ _ hFEval (emp_eval_local M) with ⟨sSfx, hSfxEval, hSfxUnpack⟩
  rcases StrContainsConcatSupport.str_concat_unpack_eval M x (sfx n)
      _ _ hXEval hSfxEval with ⟨sWT, hWTEval, hWTUnpack⟩
  rcases StrContainsConcatSupport.str_concat_unpack_eval M x emp
      _ _ hXEval (emp_eval_local M) with ⟨sJT, hJTEval, hJTUnpack⟩
  rcases StringRewriteSupport.list_concat_eval_prefix_of_translation
      M hM xs (wholeTail x n) sWT hXsList hWTailList hXsTrans hWTEval with
    ⟨sW, hWEval, hWUnpack⟩
  rcases StringRewriteSupport.list_concat_eval_prefix_of_translation
      M hM xs (joinedTail x) sJT hXsList hJTailList hXsTrans hJTEval with
    ⟨sJ, hJEval, hJUnpack⟩
  have hEEval :=
    StringRewriteSupport.singleton_elim_eval M hM (joined xs x) _ sJ
      hJoinedList hJoinedTy hJEval
  have hLEval :=
    StrContainsConcatSupport.str_contains_eval_eq M _ s sW ss hWEval hSEval
  have hREval :=
    StrContainsConcatSupport.str_contains_eval_eq M _ s sJ ss hEEval hSEval
  have hLast := premise_last_char M s ss hSEval hPrem
  have hD :
      native_unpack_seq (native_pack_string (native_str_from_int z)) =
        (native_str_from_int z).map SmtValue.Char := by
    simp [native_pack_string, Smtm.native_unpack_pack_seq]
  have hE0 : native_unpack_seq (native_pack_string []) = [] := by
    simp [native_pack_string, Smtm.native_unpack_pack_seq]
  have hNative :
      native_seq_contains (native_unpack_seq sW) (native_unpack_seq ss) =
        native_seq_contains (native_unpack_seq sJ) (native_unpack_seq ss) := by
    rw [hWUnpack, hJUnpack, hWTUnpack, hJTUnpack, hSfxUnpack, hD, hE0]
    have hCore := contains_digits_suffix_eq
      (StringRewriteSupport.listEvalPrefix M xs ++ native_unpack_seq sx)
      _ _ (digit_values_of_from_int z) hLast
    simpa [List.append_assoc] using hCore
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ hBool (by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (StrContainsConcatSupport.containsTerm (whole xs x n) s)))
      (__smtx_model_eval M (__eo_to_smt
        (StrContainsConcatSupport.containsTerm
          (__eo_list_singleton_elim op (joined xs x)) s)))
    rw [hLEval, hREval, hNative]
    exact RuleProofs.smt_value_rel_refl _)

private theorem typeof_args_of_concl_bool (xs x n s : Term)
    (hXsTrans : RuleProofs.eo_has_smt_translation xs)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : __eo_typeof (concl xs x n s) = Term.Bool) :
    __eo_typeof n = Term.Int ∧
      __eo_typeof x = Term.Apply Term.Seq Term.Char ∧
      __eo_typeof s = Term.Apply Term.Seq Term.Char ∧
      __smtx_typeof (__eo_to_smt (whole xs x n)) =
        SmtType.Seq SmtType.Char := by
  change __eo_typeof_eq (__eo_typeof (lhs xs x n s))
      (__eo_typeof (rhs xs x s)) = Term.Bool at hTy
  have hL := (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
  change __eo_typeof_str_contains (__eo_typeof (whole xs x n))
      (__eo_typeof s) ≠ Term.Stuck at hL
  rcases StrContainsReplCharSupport.eo_typeof_str_contains_args_of_ne_stuck
      _ _ hL with ⟨U, hW, hS⟩
  have hStruct :=
    StrContainsConcatSupport.concat_middle_structure xs x (sfx n) U hW
  have hSfxArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq _ _ U
      hStruct.2.2.2.2.2
  have hFromTy := hSfxArgs.1
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
  have hNSmt :=
    StrInReFromIntDigRangeProof.smtx_typeof_of_eo_int n hNTrans hNInt
  have hFTy :
      __smtx_typeof (__eo_to_smt (fromInt n)) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) = _
    rw [typeof_str_from_int_eq, hNSmt]
    simp [native_ite, native_Teq]
  have hSfxTy := smt_typeof_str_concat_of_seq (fromInt n) emp _ hFTy
    emp_type_local
  have hSfxTrans : RuleProofs.eo_has_smt_translation (sfx n) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSfxTy]
    exact seq_ne_none _
  have hTypes :=
    StrContainsConcatSupport.concat_middle_smt_types xs x (sfx n) Term.Char
      hXsTrans hXTrans hSfxTrans hW
  exact ⟨hNInt, hStruct.2.2.2.2.1, hS, by simpa using hTypes.1⟩

end StrContainsStripFromIntPostProof

public theorem cmd_step_str_contains_strip_from_int_post_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_strip_from_int_post args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_strip_from_int_post args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_strip_from_int_post args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_contains_strip_from_int_post args
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
                    (__eo_prog_str_contains_strip_from_int_post a1 a2 a3 a4
                      (Proof.pf P)) = Term.Bool at hResultTy
                have hRuleProg :
                    __eo_prog_str_contains_strip_from_int_post a1 a2 a3 a4
                        (Proof.pf P) ≠ Term.Stuck :=
                  term_ne_stuck_of_typeof_bool hResultTy
                rcases StrContainsStripFromIntPostProof.prog_info
                    a1 a2 a3 a4 P hRuleProg with ⟨hP, hWNe, hENe, hProgEq⟩
                rw [hProgEq] at hResultTy
                have hWLists :=
                  RegexRewriteSupport.list_concat_lists_of_ne_stuck
                    (Term.UOp UserOp.str_concat) a1
                    (StrContainsStripFromIntPostProof.wholeTail a2 a3) hWNe
                have hJList :=
                  StrContainsStripFromIntSupport.requires_eq_of_ne_stuck
                    hENe
                have hJNe :
                    StrContainsStripFromIntPostProof.joined a1 a2 ≠
                      Term.Stuck := by
                  intro h
                  rw [h] at hJList
                  simp [__eo_is_list] at hJList
                have hJLists :=
                  RegexRewriteSupport.list_concat_lists_of_ne_stuck
                    (Term.UOp UserOp.str_concat) a1
                    (StrContainsStripFromIntPostProof.joinedTail a2) hJNe
                rcases StrContainsStripFromIntPostProof.typeof_args_of_concl_bool
                    a1 a2 a3 a4 hA1Trans hA2Trans hA3Trans hResultTy with
                  ⟨hNTy, hXTy, hSTy, hWholeTy⟩
                have hFacts := StrContainsStripFromIntPostProof.main_facts
                  M hM a1 a2 a3 a4 hA1Trans hA2Trans hA3Trans hA4Trans
                  hNTy hXTy hSTy hWholeTy hWLists.1 hWLists.2 hJLists.2
                change StepRuleProperties M [P]
                  (__eo_prog_str_contains_strip_from_int_post a1 a2 a3 a4
                    (Proof.pf P))
                rw [hProgEq]
                refine ⟨?_,
                  RuleProofs.eo_has_smt_translation_of_has_bool_type _
                    hFacts.1⟩
                intro hTrue
                have hPremRaw : eo_interprets M P true :=
                  hTrue.true_here P (by simp)
                exact hFacts.2 (by simpa [hP] using hPremRaw)
