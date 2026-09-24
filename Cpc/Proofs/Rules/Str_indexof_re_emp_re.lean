module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.SmtModel

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem native_string_lit_empty :
    native_string_lit "" = ([] : native_String) := by
  simp [native_string_lit]

private theorem native_re_prefix_match_len?_empty_of_nullable
    (r : SmtRegLan) (xs : native_String)
    (h : native_re_nullable r = true) :
  native_re_prefix_match_len? r xs = some 0 := by
  rw [native_re_prefix_match_len?.eq_1]
  cases xs with
  | nil =>
      simp only [impl_native_string_to_values, List.map]
      rw [impl_native_re_prefix_match_len_go.eq_1]
      simp [h]
  | cons c cs =>
      simp only [impl_native_string_to_values, List.map]
      rw [impl_native_re_prefix_match_len_go.eq_2]
      simp [h]

private theorem native_re_find_idx_from_empty_of_nullable
    (r : SmtRegLan) (xs : native_String) (start : Nat)
    (h : native_re_nullable r = true) :
    native_re_find_idx_from r xs start = some (start, 0) := by
  unfold native_re_find_idx_from
  rw [impl_native_re_find_idx_aux.eq_def]
  have hPref :=
    native_re_prefix_match_len?_empty_of_nullable r (xs.drop start) h
  simp only [impl_native_string_to_values, List.map_drop] at hPref ⊢
  rw [hPref]

private theorem native_str_indexof_re_empty_hit
    (s : native_String) (r : SmtRegLan) (i : native_Int)
    (hEmpty : native_str_in_re (native_string_lit "") r = true)
    (hGe : (-1 : native_Int) <= i)
    (hLe : i <= Int.ofNat s.length)
    (hValid : native_string_valid s = true) :
    native_str_indexof_re s r i = i := by
  have hNullable : native_re_nullable r = true := by
    have hParts :
        native_string_valid ([] : native_String) = true ∧
          native_re_nullable r = true := by
      simpa [native_str_in_re, native_string_lit_empty, native_re_deriv, native_re_str_valid, impl_native_string_to_values, native_string_valid] using hEmpty
    exact hParts.2
  change (-1 : Int) <= i at hGe
  cases i with
  | ofNat n =>
    have hStart : n <= s.length := by
      change (n : Int) <= (s.length : Int) at hLe
      omega
    have hFind :
        native_re_find_idx_from r s n = some (n, 0) :=
      native_re_find_idx_from_empty_of_nullable r s n hNullable
    have hStartValues : n <= (impl_native_string_to_values s).length := by
      simpa [impl_native_string_to_values] using hStart
    simp [native_str_indexof_re, hStartValues, hFind]
  | negSucc n =>
      cases n with
      | zero =>
          simp [native_str_indexof_re]
      | succ n =>
          omega

private theorem smtx_typeof_str_indexof_re
    (s r n : SmtTerm)
    (hs : __smtx_typeof s = SmtType.Seq SmtType.Char)
    (hr : __smtx_typeof r = SmtType.RegLan)
    (hn : __smtx_typeof n = SmtType.Int) :
    __smtx_typeof (SmtTerm.str_indexof_re s r n) = SmtType.Int := by
  rw [typeof_str_indexof_re_eq]
  simp [hs, hr, hn, native_ite, native_Teq]

private theorem eo_typeof_str_indexof_re_args_of_ne_stuck
    (T R N : Term)
    (h : __eo_typeof_str_indexof_re T R N ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char ∧ R = Term.RegLan ∧ N = Term.Int := by
  cases T <;> simp [__eo_typeof_str_indexof_re] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases x <;> simp at h ⊢
        case UOp opx =>
          cases opx <;> simp at h ⊢
          cases R <;> simp at h ⊢
          case UOp opr =>
            cases opr <;> simp at h ⊢
            case RegLan =>
              cases N <;> simp at h ⊢
              case UOp opn =>
                cases opn <;> simp at h ⊢

private theorem smtx_typeof_of_eo_seq_char
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char,
    __smtx_typeof_guard, native_ite, native_Teq]
    using hTyRaw

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

private theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_int] using hTyRaw

private theorem typed_str_indexof_re_emp_re_body
    (t r n : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq Term.Char)
    (hRTy : __eo_typeof r = Term.RegLan)
    (hNTy : __eo_typeof n = Term.Int) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply Term.eq
          (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re t) r) n))
        n) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re t) r) n
  have hTSmtTy := smtx_typeof_of_eo_seq_char t hTTrans hTTy
  have hRSmtTy := smtx_typeof_of_eo_reglan r hRTrans hRTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
      (SmtTerm.str_indexof_re (__eo_to_smt t) (__eo_to_smt r) (__eo_to_smt n)) =
        SmtType.Int
    exact smtx_typeof_str_indexof_re (__eo_to_smt t) (__eo_to_smt r) (__eo_to_smt n)
      hTSmtTy hRSmtTy hNSmtTy
  have hRhsTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int := hNSmtTy
  change RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) n)
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs n
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem eval_empty_in_re_eq_true_of_premise
    (M : SmtModel) (r : Term)
    (rr : SmtRegLan)
    (hrEval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rr)
    (hPrem :
      eo_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.str_in_re (Term.String (native_string_lit ""))) r))
          (Term.Boolean true))
        true) :
    native_str_in_re (native_string_lit "") rr = true := by
  have hEval :
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply Term.str_in_re (Term.String (native_string_lit ""))) r))
            (Term.Boolean true))) =
        SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.str_in_re (Term.String (native_string_lit ""))) r))
          (Term.Boolean true)) true).mp hPrem with
    | intro_true _ hEval => exact hEval
  have hTranslate :
      __eo_to_smt
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.str_in_re (Term.String (native_string_lit ""))) r))
          (Term.Boolean true)) =
        SmtTerm.eq
          (SmtTerm.str_in_re (SmtTerm.String (native_string_lit "")) (__eo_to_smt r))
          (SmtTerm.Boolean true) := by
    rfl
  rw [hTranslate] at hEval
  simpa [__smtx_model_eval, hrEval, __smtx_model_eval_str_in_re, __smtx_model_eval_eq, native_veq, native_string_lit_empty, native_pack_string, native_unpack_string, native_pack_seq, native_unpack_seq, impl_native_string_to_values] using hEval

private theorem eval_len_geq_n_eq_true_of_premise
    (M : SmtModel) (t n : Term) (ss : SmtSeq) (ni : native_Int)
    (htEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss)
    (hnEval : __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral ni)
    (hPrem :
      eo_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.geq (Term.Apply Term.str_len t)) n))
          (Term.Boolean true))
        true) :
    ni <= Int.ofNat (native_unpack_string ss).length := by
  have hEval :
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply Term.eq
              (Term.Apply
                (Term.Apply Term.geq (Term.Apply Term.str_len t)) n))
            (Term.Boolean true))) =
        SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.geq (Term.Apply Term.str_len t)) n))
          (Term.Boolean true)) true).mp hPrem with
    | intro_true _ hEval => exact hEval
  change
    __smtx_model_eval M
      (SmtTerm.eq
        (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt t)) (__eo_to_smt n))
        (SmtTerm.Boolean true)) =
      SmtValue.Boolean true at hEval
  simp [__smtx_model_eval, htEval, hnEval, __smtx_model_eval_str_len,
    __smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_eq,
    native_seq_len, native_zleq, native_veq] at hEval
  simpa [native_unpack_string] using hEval

private theorem eval_geq_neg_one_eq_true_of_premise
    (M : SmtModel) (n : Term)
    (ni : native_Int)
    (hnEval : __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral ni)
    (hPrem :
      eo_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.geq n) (Term.Numeral (-1 : native_Int))))
          (Term.Boolean true))
        true) :
    (-1 : native_Int) <= ni := by
  have hEval :
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply Term.geq n) (Term.Numeral (-1 : native_Int))))
            (Term.Boolean true))) =
        SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.geq n) (Term.Numeral (-1 : native_Int))))
          (Term.Boolean true)) true).mp hPrem with
    | intro_true _ hEval => exact hEval
  have hTranslate :
      __eo_to_smt
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.geq n) (Term.Numeral (-1 : native_Int))))
          (Term.Boolean true)) =
        SmtTerm.eq
          (SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral (-1 : native_Int)))
          (SmtTerm.Boolean true) := by
    rfl
  rw [hTranslate] at hEval
  simp [__smtx_model_eval, hnEval, __smtx_model_eval_geq, __smtx_model_eval_leq,
    __smtx_model_eval_eq, native_zleq, native_veq] at hEval
  exact hEval

private theorem facts_str_indexof_re_emp_re_body
    (M : SmtModel) (hM : model_wf M) (t r n : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq Term.Char)
    (hRTy : __eo_typeof r = Term.RegLan)
    (hNTy : __eo_typeof n = Term.Int)
    (hPremEmpty :
      eo_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.str_in_re (Term.String (native_string_lit ""))) r))
          (Term.Boolean true))
        true)
    (hPremLen :
      eo_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.geq (Term.Apply Term.str_len t)) n))
          (Term.Boolean true))
        true)
    (hPremGe :
      eo_interprets M
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.geq n) (Term.Numeral (-1 : native_Int))))
          (Term.Boolean true))
        true) :
    eo_interprets M
      (Term.Apply
        (Term.Apply Term.eq
          (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re t) r) n))
        n)
      true := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re t) r) n
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) n) := by
    exact typed_str_indexof_re_emp_re_body t r n hTTrans hRTrans hNTrans hTTy hRTy hNTy
  have hTSmtTy := smtx_typeof_of_eo_seq_char t hTTrans hTTy
  have hRSmtTy := smtx_typeof_of_eo_reglan r hRTrans hRTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
        simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨ss, hss⟩
  rcases reglan_value_canonical hREvalTy with ⟨rr, hrr⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hni⟩
  have hEmpty : native_str_in_re (native_string_lit "") rr = true :=
    eval_empty_in_re_eq_true_of_premise M r rr hrr hPremEmpty
  have hSsTy :
      __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hss, __smtx_typeof_value] using hTEvalTy
  have hValid : native_string_valid (native_unpack_string ss) = true := by
    apply native_unpack_string_valid_of_typeof_seq_char
    exact hSsTy
  have hLen : ni <= Int.ofNat (native_unpack_string ss).length :=
    eval_len_geq_n_eq_true_of_premise M t n ss ni hss hni hPremLen
  have hGe : (-1 : native_Int) <= ni :=
    eval_geq_neg_one_eq_true_of_premise M n ni hni hPremGe
  have hIndex :
      native_str_indexof_re (native_unpack_seq ss) rr ni = ni := by
    rw [native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy]
    exact native_str_indexof_re_empty_hit
      (native_unpack_string ss) rr ni hEmpty hGe hLen hValid
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt n) := by
    change
      __smtx_model_eval M
          (SmtTerm.str_indexof_re (__eo_to_smt t) (__eo_to_smt r) (__eo_to_smt n)) =
        __smtx_model_eval M (__eo_to_smt n)
    simp [__smtx_model_eval, hss, hrr, hni, __smtx_model_eval_str_indexof_re,
      hIndex]
  change eo_interprets M (Term.Apply (Term.Apply Term.eq lhs) n) true
  exact RuleProofs.eo_interprets_eq_of_rel M lhs n hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt n))

private theorem eo_and_eq_true_elim (x y : Term)
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  cases x <;> cases y <;> simp [__eo_and] at h ⊢
  case Boolean.Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [native_and] at h ⊢
  case Binary.Binary w₁ n₁ w₂ n₂ =>
    by_cases hw : w₁ = w₂ <;>
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, hw] at h

private theorem eo_requires_true_eq (x body : Term)
    (h : x = Term.Boolean true) :
    __eo_requires x (Term.Boolean true) body = body := by
  subst x
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

private theorem str_indexof_re_emp_requires_eqs
    (t lvT r lvR n lvN₁ lvN₂ body : Term)
    (hReq :
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq r lvR) (__eo_eq t lvT))
            (__eo_eq n lvN₁))
          (__eo_eq n lvN₂))
        (Term.Boolean true) body ≠ Term.Stuck) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq r lvR) (__eo_eq t lvT))
            (__eo_eq n lvN₁))
          (__eo_eq n lvN₂))
        (Term.Boolean true) body = body ∧
      lvR = r ∧ lvT = t ∧ lvN₁ = n ∧ lvN₂ = n := by
  have hReq' := hReq
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hReq'
  rcases hReq' with ⟨hCond, hBody⟩
  have hReqEq :
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq r lvR) (__eo_eq t lvT))
            (__eo_eq n lvN₁))
          (__eo_eq n lvN₂))
        (Term.Boolean true) body = body :=
    eo_requires_true_eq _ body hCond
  have hTop := eo_and_eq_true_elim _ _ hCond
  have hLeft₁ := eo_and_eq_true_elim _ _ hTop.1
  have hLeft₂ := eo_and_eq_true_elim _ _ hLeft₁.1
  have hR : lvR = r := RuleProofs.eq_of_eo_eq_true r lvR hLeft₂.1
  have hT : lvT = t := RuleProofs.eq_of_eo_eq_true t lvT hLeft₂.2
  have hN₁ : lvN₁ = n := RuleProofs.eq_of_eo_eq_true n lvN₁ hLeft₁.2
  have hN₂ : lvN₂ = n := RuleProofs.eq_of_eo_eq_true n lvN₂ hTop.2
  exact ⟨hReqEq, hR, hT, hN₁, hN₂⟩

public theorem cmd_step_str_indexof_re_emp_re_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_re_emp_re args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_re_emp_re args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_re_emp_re args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hCmdNe : __eo_cmd_step_proven s CRule.str_indexof_re_emp_re args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hCmdNe
      exact False.elim (hCmdNe rfl)
  | cons t args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hCmdNe
          exact False.elim (hCmdNe rfl)
      | cons r args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hCmdNe
              exact False.elim (hCmdNe rfl)
          | cons n args =>
              cases args with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hCmdNe
                  exact False.elim (hCmdNe rfl)
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hCmdNe
                      exact False.elim (hCmdNe rfl)
                  | cons i₁ premises =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hCmdNe
                          exact False.elim (hCmdNe rfl)
                      | cons i₂ premises =>
                          cases premises with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hCmdNe
                              exact False.elim (hCmdNe rfl)
                          | cons i₃ premises =>
                              cases premises with
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hCmdNe
                                  exact False.elim (hCmdNe rfl)
                              | nil =>
                                  let P₁ := __eo_state_proven_nth s i₁
                                  let P₂ := __eo_state_proven_nth s i₂
                                  let P₃ := __eo_state_proven_nth s i₃
                                  have hTTrans : RuleProofs.eo_has_smt_translation t := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                                  have hRTrans : RuleProofs.eo_has_smt_translation r := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                                  have hNTrans : RuleProofs.eo_has_smt_translation n := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
                                  let tArg := t
                                  let rArg := r
                                  let nArg := n
                                  have hTTransArg : RuleProofs.eo_has_smt_translation tArg := by
                                    simpa [tArg] using hTTrans
                                  have hRTransArg : RuleProofs.eo_has_smt_translation rArg := by
                                    simpa [rArg] using hRTrans
                                  have hNTransArg : RuleProofs.eo_has_smt_translation nArg := by
                                    simpa [nArg] using hNTrans
                                  change
                                    __eo_typeof
                                      (__eo_prog_str_indexof_re_emp_re tArg rArg nArg
                                        (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃)) =
                                      Term.Bool at hResultTy
                                  change
                                    StepRuleProperties M [P₁, P₂, P₃]
                                      (__eo_prog_str_indexof_re_emp_re tArg rArg nArg
                                        (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃))
                                  change
                                    __eo_prog_str_indexof_re_emp_re tArg rArg nArg
                                        (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃) ≠
                                      Term.Stuck at hCmdNe
                                  unfold __eo_prog_str_indexof_re_emp_re at hResultTy hCmdNe ⊢
                                  repeat' (split at * <;> try (subst_vars; simp at hResultTy hCmdNe))
                                  all_goals
                                    try
                                      exact False.elim (by
                                        change Term.Stuck = Term.Bool at hResultTy
                                        cases hResultTy)
                                  rename_i
                                    lvR lvT lvN₂ lvN₃ hP₁Eq hP₂Eq hP₃Eq
                                    _htNe _hrNe _hnNe
                                    _mt₂ _mr₂ _mn₂ _mp₄ _mp₅ _mp₆
                                    _lvR' _lvT' _lvN₂' _lvN₃'
                                    _hP₁Eq' _hP₂Eq' _hP₃Eq'
                                    _htNe' _hrNe' _hnNe'
                                  let body :=
                                    Term.Apply
                                      (Term.Apply Term.eq
                                        (Term.Apply
                                          (Term.Apply (Term.Apply Term.str_indexof_re tArg) rArg)
                                          nArg))
                                      nArg
                                  have hReqNe :
                                      __eo_requires
                                        (__eo_and
                                          (__eo_and
                                            (__eo_and (__eo_eq rArg lvR) (__eo_eq tArg lvT))
                                            (__eo_eq nArg lvN₂))
                                          (__eo_eq nArg lvN₃))
                                        (Term.Boolean true) body ≠ Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases str_indexof_re_emp_requires_eqs
                                      tArg lvT rArg lvR nArg lvN₂ lvN₃ body hReqNe with
                                    ⟨hReqEq, hLvR, hLvT, hLvN₂, hLvN₃⟩
                                  have hP₁TermEq :
                                      P₁ =
                                        Term.Apply
                                          (Term.Apply Term.eq
                                            (Term.Apply
                                              (Term.Apply Term.str_in_re (Term.String (native_string_lit "")))
                                              lvR))
                                          (Term.Boolean true) := by
                                    injection hP₁Eq
                                  have hP₂TermEq :
                                      P₂ =
                                        Term.Apply
                                          (Term.Apply Term.eq
                                            (Term.Apply
                                              (Term.Apply Term.geq
                                                (Term.Apply Term.str_len lvT))
                                              lvN₂))
                                          (Term.Boolean true) := by
                                    injection hP₂Eq
                                  have hP₃TermEq :
                                      P₃ =
                                        Term.Apply
                                          (Term.Apply Term.eq
                                            (Term.Apply
                                              (Term.Apply Term.geq lvN₃)
                                              (Term.Numeral (-1 : native_Int))))
                                          (Term.Boolean true) := by
                                    injection hP₃Eq
                                  rw [hReqEq] at hResultTy ⊢
                                  have hLhsNotStuck :
                                      __eo_typeof
                                          (Term.Apply
                                            (Term.Apply (Term.Apply Term.str_indexof_re tArg) rArg)
                                            nArg) ≠ Term.Stuck :=
                                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                      (__eo_typeof
                                        (Term.Apply
                                          (Term.Apply (Term.Apply Term.str_indexof_re tArg) rArg)
                                          nArg))
                                      (__eo_typeof nArg) hResultTy).1
                                  have hArgTypes :
                                      __eo_typeof tArg = Term.Apply Term.Seq Term.Char ∧
                                        __eo_typeof rArg = Term.RegLan ∧
                                        __eo_typeof nArg = Term.Int := by
                                    change
                                      __eo_typeof_str_indexof_re
                                          (__eo_typeof tArg) (__eo_typeof rArg) (__eo_typeof nArg) ≠
                                        Term.Stuck at hLhsNotStuck
                                    exact eo_typeof_str_indexof_re_args_of_ne_stuck
                                      (__eo_typeof tArg) (__eo_typeof rArg) (__eo_typeof nArg)
                                      hLhsNotStuck
                                  have hTyped :
                                      RuleProofs.eo_has_bool_type body := by
                                    exact typed_str_indexof_re_emp_re_body tArg rArg nArg
                                      hTTransArg hRTransArg hNTransArg
                                      hArgTypes.1 hArgTypes.2.1 hArgTypes.2.2
                                  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type body hTyped⟩
                                  intro hTrue
                                  have hPremEmpty :
                                      eo_interprets M
                                        (Term.Apply
                                          (Term.Apply Term.eq
                                            (Term.Apply
                                              (Term.Apply Term.str_in_re (Term.String (native_string_lit "")))
                                              rArg))
                                          (Term.Boolean true))
                                        true := by
                                    simpa [hP₁TermEq, hLvR] using
                                      hTrue P₁ (by simp [P₁])
                                  have hPremLen :
                                      eo_interprets M
                                        (Term.Apply
                                          (Term.Apply Term.eq
                                            (Term.Apply
                                              (Term.Apply Term.geq
                                                (Term.Apply Term.str_len tArg))
                                              nArg))
                                          (Term.Boolean true))
                                        true := by
                                    simpa [hP₂TermEq, hLvT, hLvN₂] using
                                      hTrue P₂ (by simp [P₂])
                                  have hPremGe :
                                      eo_interprets M
                                        (Term.Apply
                                          (Term.Apply Term.eq
                                            (Term.Apply
                                              (Term.Apply Term.geq nArg)
                                              (Term.Numeral (-1 : native_Int))))
                                          (Term.Boolean true))
                                        true := by
                                    simpa [hP₃TermEq, hLvN₃] using
                                      hTrue P₃ (by simp [P₃])
                                  exact facts_str_indexof_re_emp_re_body M hM tArg rArg nArg
                                    hTTransArg hRTransArg hNTransArg
                                    hArgTypes.1 hArgTypes.2.1 hArgTypes.2.2
                                    hPremEmpty hPremLen hPremGe
