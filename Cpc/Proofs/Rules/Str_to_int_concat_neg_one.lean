module

public import Cpc.Proofs.RuleSupport.StrContainsConcatSupport
import all Cpc.Proofs.RuleSupport.StrContainsConcatSupport

open Eo
open SmtEval
open Smtm
open StrContainsConcatSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev toIntConcatNegOneValuePremise (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_to_int s))
    (Term.Numeral (-1 : native_Int))

private abbrev toIntConcatNegOneNonemptyPremise (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.eq (Term.Apply Term.str_len s))
        (Term.Numeral 0)))
    (Term.Boolean false)

private abbrev toIntConcatNegOneWhole (s₁ s₂ s₃ : Term) : Term :=
  concatMiddle s₁ s₂ s₃

private abbrev toIntConcatNegOneLhs (s₁ s₂ s₃ : Term) : Term :=
  Term.Apply Term.str_to_int (toIntConcatNegOneWhole s₁ s₂ s₃)

private abbrev toIntConcatNegOneConclusion
    (s₁ s₂ s₃ : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (toIntConcatNegOneLhs s₁ s₂ s₃))
    (Term.Numeral (-1 : native_Int))

private abbrev toIntConcatNegOneGeneratedConclusion
    (s₁ s₂ s₃ : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.UOp UserOp.str_to_int)
        (toIntConcatNegOneWhole s₁ s₂ s₃)))
    (Term.Numeral (-1 : native_Int))

private theorem mk_apply_eq (f a : Term)
    (hF : f ≠ Term.Stuck) (hA : a ≠ Term.Stuck) :
    __eo_mk_apply f a = Term.Apply f a := by
  cases f <;> cases a <;> simp [__eo_mk_apply] at hF hA ⊢

private theorem generated_conclusion_eq
    (s₁ s₂ s₃ : Term)
    (hWhole : toIntConcatNegOneWhole s₁ s₂ s₃ ≠ Term.Stuck) :
    toIntConcatNegOneGeneratedConclusion s₁ s₂ s₃ =
      toIntConcatNegOneConclusion s₁ s₂ s₃ := by
  have hToIntHead :
      __eo_mk_apply (Term.UOp UserOp.str_to_int)
          (toIntConcatNegOneWhole s₁ s₂ s₃) =
        Term.Apply (Term.UOp UserOp.str_to_int)
          (toIntConcatNegOneWhole s₁ s₂ s₃) :=
    mk_apply_eq _ _ (by simp) hWhole
  have hEqHead :
      __eo_mk_apply (Term.UOp UserOp.eq)
          (__eo_mk_apply (Term.UOp UserOp.str_to_int)
            (toIntConcatNegOneWhole s₁ s₂ s₃)) =
        Term.Apply (Term.UOp UserOp.eq)
          (toIntConcatNegOneLhs s₁ s₂ s₃) := by
    rw [hToIntHead]
    exact mk_apply_eq _ _ (by simp) (by simp)
  rw [toIntConcatNegOneGeneratedConclusion, hEqHead]
  exact mk_apply_eq _ _ (by simp) (by simp)

private theorem generated_whole_ne_stuck
    (s₁ s₂ s₃ : Term)
    (hGenerated :
      toIntConcatNegOneGeneratedConclusion s₁ s₂ s₃ ≠ Term.Stuck) :
    toIntConcatNegOneWhole s₁ s₂ s₃ ≠ Term.Stuck := by
  have hEqHead :
      __eo_mk_apply (Term.UOp UserOp.eq)
          (__eo_mk_apply (Term.UOp UserOp.str_to_int)
            (toIntConcatNegOneWhole s₁ s₂ s₃)) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _
      (Term.Numeral (-1 : native_Int)) hGenerated
  have hToInt :
      __eo_mk_apply (Term.UOp UserOp.str_to_int)
          (toIntConcatNegOneWhole s₁ s₂ s₃) ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq) _ hEqHead
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.str_to_int) _ hToInt

private theorem eo_typeof_str_to_int_arg_char_of_ne_stuck
    (A : Term) (h : __eo_typeof_str_to_code A ≠ Term.Stuck) :
    A = Term.Apply Term.Seq Term.Char := by
  cases A <;> simp [__eo_typeof_str_to_code] at h ⊢
  case Apply f a =>
    cases f <;> simp [__eo_typeof_str_to_code] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_to_code] at h ⊢
      case Seq =>
        cases a <;> simp [__eo_typeof_str_to_code] at h ⊢
        case UOp elem =>
          cases elem <;> simp [__eo_typeof_str_to_code] at h ⊢

private theorem smtx_eval_str_to_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_to_int x) =
      __smtx_model_eval_str_to_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem prog_str_to_int_concat_neg_one_info
    (s₁ s₂ s₃ P₁ P₂ : Term)
    (hProg :
      __eo_prog_str_to_int_concat_neg_one s₁ s₂ s₃
          (Proof.pf P₁) (Proof.pf P₂) ≠ Term.Stuck) :
    ∃ sValue sLen,
      P₁ = toIntConcatNegOneValuePremise sValue ∧
      P₂ = toIntConcatNegOneNonemptyPremise sLen ∧
      sValue = s₂ ∧ sLen = s₂ ∧
      __eo_prog_str_to_int_concat_neg_one s₁ s₂ s₃
          (Proof.pf P₁) (Proof.pf P₂) =
        toIntConcatNegOneGeneratedConclusion s₁ s₂ s₃ := by
  unfold __eo_prog_str_to_int_concat_neg_one at hProg
  split at hProg <;> try contradiction
  next heq₁ heq₂ =>
    cases heq₁
    cases heq₂
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hS₁, hS₂⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_to_int_concat_neg_one, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, toIntConcatNegOneGeneratedConclusion,
      toIntConcatNegOneWhole]

private theorem typed___eo_prog_str_to_int_concat_neg_one_impl
    (s₁ s₂ s₃ P₁ P₂ : Term)
    (hWholeTy :
      __smtx_typeof (__eo_to_smt (toIntConcatNegOneWhole s₁ s₂ s₃)) =
        SmtType.Seq SmtType.Char)
    (hProgEq :
      __eo_prog_str_to_int_concat_neg_one s₁ s₂ s₃
          (Proof.pf P₁) (Proof.pf P₂) =
        toIntConcatNegOneConclusion s₁ s₂ s₃) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_to_int_concat_neg_one s₁ s₂ s₃
        (Proof.pf P₁) (Proof.pf P₂)) := by
  let lhs := toIntConcatNegOneLhs s₁ s₂ s₃
  let rhs := Term.Numeral (-1 : native_Int)
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_to_int
          (__eo_to_smt (toIntConcatNegOneWhole s₁ s₂ s₃))) =
      SmtType.Int
    rw [typeof_str_to_int_eq, hWholeTy]
    simp [native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) = SmtType.Int
    rw [__smtx_typeof.eq_def]
  have hBool : RuleProofs.eo_has_bool_type
      (toIntConcatNegOneConclusion s₁ s₂ s₃) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem string_nonempty_of_seq_nonempty
    (ss : SmtSeq) (hNe : native_unpack_seq ss ≠ []) :
    native_unpack_string ss ≠ [] := by
  intro hNil
  apply hNe
  cases h : native_unpack_seq ss with
  | nil => rfl
  | cons v vs =>
      simp [native_unpack_string, h] at hNil

private theorem native_str_to_int_neg_one_nonempty_not_all_digits
    (s : native_String) (hNe : s ≠ [])
    (hToInt : native_str_to_int s = (-1 : native_Int)) :
    s.all impl_native_char_is_digit ≠ true := by
  cases s with
  | nil => exact False.elim (hNe rfl)
  | cons c cs =>
      intro hDigits
      simp [native_str_to_int, hDigits] at hToInt

private theorem contained_unpack_string_all_digits
    (whole needle : SmtSeq)
    (hWholeDigits :
      (native_unpack_string whole).all impl_native_char_is_digit = true)
    (hContains :
      native_seq_contains (native_unpack_seq whole)
        (native_unpack_seq needle) = true) :
    (native_unpack_string needle).all impl_native_char_is_digit = true := by
  rcases (StrContainsReplCharSupport.native_seq_contains_iff_decomp
      (native_unpack_seq whole) (native_unpack_seq needle)).1 hContains with
    ⟨before, after, hWhole⟩
  change
    ((native_unpack_seq whole).map impl_native_ssm_char_of_value).all
        impl_native_char_is_digit = true at hWholeDigits
  rw [hWhole] at hWholeDigits
  simp only [List.map_append, List.all_append, Bool.and_eq_true] at hWholeDigits
  change
    ((native_unpack_seq needle).map impl_native_ssm_char_of_value).all
      impl_native_char_is_digit = true
  exact hWholeDigits.1.2

private theorem native_str_to_int_neg_one_of_nonempty_not_all_digits
    (s : native_String) (hNe : s ≠ [])
    (hDigits : s.all impl_native_char_is_digit ≠ true) :
    native_str_to_int s = (-1 : native_Int) := by
  cases s with
  | nil => exact False.elim (hNe rfl)
  | cons c cs =>
      simp [native_str_to_int, hDigits]

private theorem facts___eo_prog_str_to_int_concat_neg_one_impl
    (M : SmtModel) (hM : model_wf M)
    (s₁ s₂ s₃ P₁ P₂ : Term)
    (hStructure :
      __eo_is_list (Term.UOp UserOp.str_concat) s₁ = Term.Boolean true ∧
      toIntConcatNegOneWhole s₁ s₂ s₃ =
        __eo_list_concat_rec s₁ (concatTail s₂ s₃))
    (hWholeTy :
      __smtx_typeof (__eo_to_smt (toIntConcatNegOneWhole s₁ s₂ s₃)) =
        SmtType.Seq SmtType.Char)
    (hS₂Ty : __smtx_typeof (__eo_to_smt s₂) =
      SmtType.Seq SmtType.Char)
    (hS₃Ty : __smtx_typeof (__eo_to_smt s₃) =
      SmtType.Seq SmtType.Char)
    (hPremValue : eo_interprets M
      (toIntConcatNegOneValuePremise s₂) true)
    (hPremNonempty : eo_interprets M
      (toIntConcatNegOneNonemptyPremise s₂) true)
    (hProgEq :
      __eo_prog_str_to_int_concat_neg_one s₁ s₂ s₃
          (Proof.pf P₁) (Proof.pf P₂) =
        toIntConcatNegOneConclusion s₁ s₂ s₃) :
    eo_interprets M
      (__eo_prog_str_to_int_concat_neg_one s₁ s₂ s₃
        (Proof.pf P₁) (Proof.pf P₂)) true := by
  let whole := toIntConcatNegOneWhole s₁ s₂ s₃
  let lhs := toIntConcatNegOneLhs s₁ s₂ s₃
  let rhs := Term.Numeral (-1 : native_Int)
  have hBool : RuleProofs.eo_has_bool_type
      (toIntConcatNegOneConclusion s₁ s₂ s₃) := by
    simpa [hProgEq] using
      typed___eo_prog_str_to_int_concat_neg_one_impl
        s₁ s₂ s₃ P₁ P₂ hWholeTy hProgEq
  have hWholeEvalTy := smt_model_eval_preserves_type M hM
    (__eo_to_smt whole) (SmtType.Seq SmtType.Char) hWholeTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hS₂EvalTy := smt_model_eval_preserves_type M hM
    (__eo_to_smt s₂) (SmtType.Seq SmtType.Char) hS₂Ty
    (seq_ne_none _) (type_inhabited_seq _)
  rcases seq_value_canonical hWholeEvalTy with ⟨swhole, hWholeEval⟩
  rcases seq_value_canonical hS₂EvalTy with ⟨ss₂, hS₂Eval⟩
  have hS₂ContainsSelf := eval_contains_self M hM s₂ SmtType.Char hS₂Ty
  have hWholeContainsEval := eval_contains_concat_middle M hM
    s₁ s₂ s₃ s₂ SmtType.Char hStructure.1 hStructure.2
    hWholeTy hS₂Ty hS₃Ty hS₂Ty hS₂ContainsSelf
  have hWholeContains :
      native_seq_contains (native_unpack_seq swhole)
        (native_unpack_seq ss₂) = true := by
    rw [str_contains_eval_eq M whole s₂ swhole ss₂
      hWholeEval hS₂Eval] at hWholeContainsEval
    exact SmtValue.Boolean.inj hWholeContainsEval
  have hS₂ToInt :
      native_str_to_int (native_unpack_string ss₂) =
        (-1 : native_Int) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremValue
    cases hPremValue with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_to_int (__eo_to_smt s₂))
              (SmtTerm.Numeral (-1 : native_Int))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_to_int_term_eq,
          hS₂Eval, StrEqReplSupport.smtx_eval_numeral_term_eq] at hEval
        simpa [__smtx_model_eval_str_to_int, __smtx_model_eval_eq,
          native_veq] using hEval
  have hS₂NonemptySeq : native_unpack_seq ss₂ ≠ [] := by
    intro hEmpty
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremNonempty
    cases hPremNonempty with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt s₂))
                (SmtTerm.Numeral 0))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq,
          smtx_eval_str_len_term_eq, hS₂Eval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        simp [__smtx_model_eval_str_len, __smtx_model_eval_eq,
          native_seq_len, native_veq, hEmpty] at hEval
  have hS₂NonemptyString : native_unpack_string ss₂ ≠ [] :=
    string_nonempty_of_seq_nonempty ss₂ hS₂NonemptySeq
  have hS₂NotDigits :
      (native_unpack_string ss₂).all impl_native_char_is_digit ≠ true :=
    native_str_to_int_neg_one_nonempty_not_all_digits
      (native_unpack_string ss₂) hS₂NonemptyString hS₂ToInt
  have hWholeNotDigits :
      (native_unpack_string swhole).all impl_native_char_is_digit ≠ true := by
    intro hDigits
    exact hS₂NotDigits
      (contained_unpack_string_all_digits swhole ss₂ hDigits
        hWholeContains)
  have hWholeNonemptySeq : native_unpack_seq swhole ≠ [] := by
    intro hEmpty
    have hLen := StrContainsReplCharSupport.native_seq_length_le_of_contains
      (native_unpack_seq swhole) (native_unpack_seq ss₂) hWholeContains
    rw [hEmpty] at hLen
    simp at hLen
    exact hS₂NonemptySeq hLen
  have hWholeNonemptyString : native_unpack_string swhole ≠ [] :=
    string_nonempty_of_seq_nonempty swhole hWholeNonemptySeq
  have hWholeToInt :
      native_str_to_int (native_unpack_string swhole) =
        (-1 : native_Int) :=
    native_str_to_int_neg_one_of_nonempty_not_all_digits
      (native_unpack_string swhole) hWholeNonemptyString hWholeNotDigits
  have hEvalEq : __smtx_model_eval M (__eo_to_smt lhs) =
      __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_int (__eo_to_smt whole)) =
      __smtx_model_eval M (SmtTerm.Numeral (-1 : native_Int))
    rw [smtx_eval_str_to_int_term_eq, hWholeEval,
      StrEqReplSupport.smtx_eval_numeral_term_eq]
    simp [__smtx_model_eval_str_to_int, hWholeToInt]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_to_int_concat_neg_one_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_int_concat_neg_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_to_int_concat_neg_one args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_int_concat_neg_one args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_to_int_concat_neg_one args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons s₁ args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons s₂ args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons s₃ args =>
              cases args with
              | cons _ _ => exact absurd rfl hProg
              | nil =>
                  cases premises with
                  | nil => exact absurd rfl hProg
                  | cons i₁ premises =>
                      cases premises with
                      | nil => exact absurd rfl hProg
                      | cons i₂ premises =>
                          cases premises with
                          | cons _ _ => exact absurd rfl hProg
                          | nil =>
                              let P₁ := __eo_state_proven_nth s i₁
                              let P₂ := __eo_state_proven_nth s i₂
                              have hS₁Trans :
                                  RuleProofs.eo_has_smt_translation s₁ := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.1
                              have hS₂Trans :
                                  RuleProofs.eo_has_smt_translation s₂ := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.2.1
                              have hS₃Trans :
                                  RuleProofs.eo_has_smt_translation s₃ := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.1
                              change __eo_typeof
                                  (__eo_prog_str_to_int_concat_neg_one
                                    s₁ s₂ s₃ (Proof.pf P₁)
                                    (Proof.pf P₂)) = Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_to_int_concat_neg_one
                                      s₁ s₂ s₃ (Proof.pf P₁)
                                      (Proof.pf P₂) ≠ Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_to_int_concat_neg_one_info
                                  s₁ s₂ s₃ P₁ P₂ hRuleProg with
                                ⟨sValue, sLen, hP₁, hP₂,
                                  hsValue, hsLen, hProgGenerated⟩
                              subst sValue
                              subst sLen
                              have hGeneratedNe :
                                  toIntConcatNegOneGeneratedConclusion
                                      s₁ s₂ s₃ ≠ Term.Stuck := by
                                rw [← hProgGenerated]
                                exact hRuleProg
                              have hWholeNe := generated_whole_ne_stuck
                                s₁ s₂ s₃ hGeneratedNe
                              have hGeneratedEq := generated_conclusion_eq
                                s₁ s₂ s₃ hWholeNe
                              have hProgEq :
                                  __eo_prog_str_to_int_concat_neg_one
                                      s₁ s₂ s₃ (Proof.pf P₁)
                                      (Proof.pf P₂) =
                                    toIntConcatNegOneConclusion s₁ s₂ s₃ := by
                                rw [hProgGenerated, hGeneratedEq]
                              rw [hProgEq] at hResultTy
                              have hLhsNN :=
                                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                  (__eo_typeof
                                    (toIntConcatNegOneLhs s₁ s₂ s₃))
                                  (__eo_typeof
                                    (Term.Numeral (-1 : native_Int)))
                                  hResultTy).1
                              change __eo_typeof_str_to_code
                                  (__eo_typeof
                                    (toIntConcatNegOneWhole s₁ s₂ s₃)) ≠
                                Term.Stuck at hLhsNN
                              have hWholeEoTy :
                                  __eo_typeof
                                      (toIntConcatNegOneWhole s₁ s₂ s₃) =
                                    Term.Apply Term.Seq Term.Char :=
                                eo_typeof_str_to_int_arg_char_of_ne_stuck
                                  _ hLhsNN
                              have hStructureFull := concat_middle_structure
                                s₁ s₂ s₃ Term.Char hWholeEoTy
                              have hTypes := concat_middle_smt_types
                                s₁ s₂ s₃ Term.Char
                                hS₁Trans hS₂Trans hS₃Trans hWholeEoTy
                              have hStructure :
                                  __eo_is_list (Term.UOp UserOp.str_concat) s₁ =
                                      Term.Boolean true ∧
                                    toIntConcatNegOneWhole s₁ s₂ s₃ =
                                      __eo_list_concat_rec s₁
                                        (concatTail s₂ s₃) :=
                                ⟨hStructureFull.1, hStructureFull.2.2.1⟩
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPrem₁Raw : eo_interprets M P₁ true :=
                                  hTrue P₁ (by simp [P₁, premiseTermList])
                                have hPrem₂Raw : eo_interprets M P₂ true :=
                                  hTrue P₂ (by simp [P₂, premiseTermList])
                                have hPrem₁ : eo_interprets M
                                    (toIntConcatNegOneValuePremise s₂) true := by
                                  simpa [hP₁] using hPrem₁Raw
                                have hPrem₂ : eo_interprets M
                                    (toIntConcatNegOneNonemptyPremise s₂) true := by
                                  simpa [hP₂] using hPrem₂Raw
                                exact
                                  facts___eo_prog_str_to_int_concat_neg_one_impl
                                    M hM s₁ s₂ s₃ P₁ P₂ hStructure
                                    hTypes.1 hTypes.2.1 hTypes.2.2
                                    hPrem₁ hPrem₂ hProgEq
                              · exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _
                                    (typed___eo_prog_str_to_int_concat_neg_one_impl
                                      s₁ s₂ s₃ P₁ P₂ hTypes.1 hProgEq)
