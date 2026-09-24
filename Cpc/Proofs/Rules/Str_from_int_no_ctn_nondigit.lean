module

public import Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
import all Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrFromIntNoCtnNondigitProof

private abbrev nonemptyPrem (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.eq s) (Term.String [])))
    (Term.Boolean false)

private abbrev toIntNegOnePrem (s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_to_int s))
    (Term.Numeral (-1 : native_Int))

private abbrev lhs (n s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains
    (Term.Apply Term.str_from_int n)) s

private abbrev concl (n s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lhs n s)) (Term.Boolean false)

private theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_to_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_to_int x) =
      __smtx_model_eval_str_to_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_string_empty
    (M : SmtModel) :
    __smtx_model_eval M (SmtTerm.String []) =
      SmtValue.Seq (native_pack_string []) := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_numeral_term_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem eo_typeof_str_contains_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              have hyx : y = x :=
                RuleProofs.eq_of_requires_eq_true_not_stuck x y Term.Bool h
              exact hyx

private theorem smtx_typeof_of_eo_seq
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_seq,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hComponentNN)

private theorem prog_form (n s P1 P2 : Term)
    (hProg : __eo_prog_str_from_int_no_ctn_nondigit n s
        (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck) :
    P1 = nonemptyPrem s ∧
      P2 = toIntNegOnePrem s ∧
      __eo_prog_str_from_int_no_ctn_nondigit n s
        (Proof.pf P1) (Proof.pf P2) =
        concl n s := by
  unfold __eo_prog_str_from_int_no_ctn_nondigit at hProg ⊢
  split at hProg <;> try contradiction
  next heqP1 heqP2 =>
    cases heqP1
    cases heqP2
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg with
      ⟨hs2, hs3⟩
    subst_vars
    refine ⟨rfl, rfl, ?_⟩
    simp [__eo_prog_str_from_int_no_ctn_nondigit, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, nonemptyPrem, toIntNegOnePrem, concl, lhs]

private theorem typeof_args_of_concl_bool
    (n s : Term)
    (hTy : __eo_typeof (concl n s) = Term.Bool) :
    __eo_typeof n = Term.Int ∧
      __eo_typeof s = Term.Apply Term.Seq Term.Char := by
  change __eo_typeof_eq (__eo_typeof (lhs n s))
      (__eo_typeof (Term.Boolean false)) = Term.Bool at hTy
  have hLhsNotStuck : __eo_typeof (lhs n s) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (lhs n s)) (__eo_typeof (Term.Boolean false)) hTy).1
  have hContainsArgs :
      ∃ T,
        __eo_typeof (Term.Apply Term.str_from_int n) =
          Term.Apply Term.Seq T ∧
        __eo_typeof s = Term.Apply Term.Seq T := by
    change __eo_typeof_str_contains
        (__eo_typeof (Term.Apply Term.str_from_int n))
        (__eo_typeof s) ≠ Term.Stuck at hLhsNotStuck
    exact eo_typeof_str_contains_args_of_ne_stuck
      (__eo_typeof (Term.Apply Term.str_from_int n)) (__eo_typeof s)
      hLhsNotStuck
  rcases hContainsArgs with ⟨T, hFromTy, hSTy⟩
  have hNInt : __eo_typeof n = Term.Int := by
    change __eo_typeof_str_from_code (__eo_typeof n) =
      Term.Apply Term.Seq T at hFromTy
    cases hN : __eo_typeof n <;>
      simp [__eo_typeof_str_from_code, hN] at hFromTy
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_from_code, hN] at hFromTy
      case Int =>
        rfl
  have hFromChar :
      __eo_typeof (Term.Apply Term.str_from_int n) =
        Term.Apply Term.Seq Term.Char := by
    change __eo_typeof_str_from_code (__eo_typeof n) =
      Term.Apply Term.Seq Term.Char
    rw [hNInt]
    rfl
  have hSeqEq : Term.Apply Term.Seq T = Term.Apply Term.Seq Term.Char := by
    rw [← hFromTy, hFromChar]
  exact ⟨hNInt, by simpa [(Term.Apply.inj hSeqEq).2] using hSTy⟩

private theorem typed_concl
    (n s : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTy : __eo_typeof n = Term.Int)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (concl n s) := by
  have hNSmtTy :=
    StrInReFromIntDigRangeProof.smtx_typeof_of_eo_int n hNTrans hNTy
  have hSSmtTy := smtx_typeof_of_eo_seq s Term.Char hSTrans hSTy
  have hFromTy :
      __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) =
        SmtType.Seq SmtType.Char := by
    rw [typeof_str_from_int_eq, hNSmtTy]
    simp [native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs n s)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains
          (SmtTerm.str_from_int (__eo_to_smt n)) (__eo_to_smt s)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hFromTy, hSSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean false)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs n s)
    (Term.Boolean false) (by rw [hLhsTy, hRhsTy])
    (by rw [hLhsTy]; simp)

private theorem smtseq_empty_char_of_unpack_nil
    (ss : SmtSeq)
    (hNil : native_unpack_seq ss = [])
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    ss = native_pack_string [] := by
  cases ss with
  | empty T =>
      simp [__smtx_typeof_seq_value] at hTy
      subst T
      simp [native_pack_string, native_pack_seq]
  | cons v vs =>
      simp [native_unpack_seq] at hNil

private theorem string_nonempty_of_seq_nonempty
    (ss : SmtSeq)
    (hNe : native_unpack_seq ss ≠ []) :
    native_unpack_string ss ≠ [] := by
  intro hNil
  apply hNe
  cases h : native_unpack_seq ss with
  | nil => rfl
  | cons v vs =>
      simp [native_unpack_string, h] at hNil

private theorem native_str_to_int_neg_one_nonempty_not_all_digits
    (s : native_String)
    (hNe : s ≠ [])
    (hToInt : native_str_to_int s = (-1 : native_Int)) :
    s.all impl_native_char_is_digit ≠ true := by
  cases s with
  | nil => exact False.elim (hNe rfl)
  | cons c cs =>
      intro hDigits
      simp [native_str_to_int, hDigits] at hToInt

private theorem all_digit_values_of_all_digits
    (xs : native_String)
    (hDigits : xs.all impl_native_char_is_digit = true) :
    (xs.map SmtValue.Char).all
        (fun v => impl_native_char_is_digit (impl_native_ssm_char_of_value v)) =
      true := by
  rw [List.all_eq_true] at hDigits ⊢
  intro v hv
  rcases List.mem_map.mp hv with ⟨c, hc, rfl⟩
  simpa [impl_native_ssm_char_of_value] using hDigits c hc

private theorem all_digits_unpack_string_of_value_digits
    (xs : List SmtValue)
    (hDigits :
      xs.all (fun v => impl_native_char_is_digit (impl_native_ssm_char_of_value v)) =
        true) :
    (xs.map impl_native_ssm_char_of_value).all impl_native_char_is_digit = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hParts :
          impl_native_char_is_digit (impl_native_ssm_char_of_value x) = true ∧
            xs.all
              (fun v => impl_native_char_is_digit (impl_native_ssm_char_of_value v)) =
              true := by
        simpa [Bool.and_eq_true] using hDigits
      simp [hParts.1, ih hParts.2]

private theorem native_seq_contains_decomp_exists_local
    (xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    ∃ before after, xs = before ++ pat ++ after := by
  have hGe : 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at h
    exact of_decide_eq_true h
  exact ⟨_, _, (native_seq_indexof_zero_decomp xs pat hGe).symm⟩

private theorem contained_string_all_digits
    (hay : native_String) (needle : SmtSeq)
    (hHayDigits : hay.all impl_native_char_is_digit = true)
    (hContains :
      native_seq_contains (native_unpack_seq (native_pack_string hay))
        (native_unpack_seq needle) = true) :
    (native_unpack_string needle).all impl_native_char_is_digit = true := by
  rcases native_seq_contains_decomp_exists_local
      (native_unpack_seq (native_pack_string hay)) (native_unpack_seq needle)
      hContains with
    ⟨pre, post, hDecomp⟩
  have hHayVals :
      (native_unpack_seq (native_pack_string hay)).all
          (fun v => impl_native_char_is_digit (impl_native_ssm_char_of_value v)) =
        true := by
    simpa [native_pack_string, Smtm.native_unpack_pack_seq] using
      all_digit_values_of_all_digits hay hHayDigits
  rw [hDecomp] at hHayVals
  have hNeedleVals :
      (native_unpack_seq needle).all
          (fun v => impl_native_char_is_digit (impl_native_ssm_char_of_value v)) =
        true := by
    have hParts :
        pre.all (fun v => impl_native_char_is_digit (impl_native_ssm_char_of_value v)) =
            true ∧
          (native_unpack_seq needle).all
              (fun v => impl_native_char_is_digit (impl_native_ssm_char_of_value v)) =
            true ∧
          post.all (fun v => impl_native_char_is_digit (impl_native_ssm_char_of_value v)) =
            true := by
      simpa [List.all_append, Bool.and_eq_true, List.append_assoc] using
        hHayVals
    exact hParts.2.1
  simpa [native_unpack_string] using
    all_digits_unpack_string_of_value_digits (native_unpack_seq needle)
      hNeedleVals

private theorem premise_nonempty_seq
    (M : SmtModel) (hM : model_wf M)
    (s : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (ss : SmtSeq)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hPrem : eo_interprets M (nonemptyPrem s) true) :
    native_unpack_seq ss ≠ [] := by
  intro hNil
  have hSSmtTy := smtx_typeof_of_eo_seq s Term.Char hSTrans hSTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hSSeqTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    have hsimpa := hSEvalTy
    try simp [hSEval] at hsimpa ⊢
    exact hsimpa
  have hSeqEmpty : ss = native_pack_string [] :=
    smtseq_empty_char_of_unpack_nil ss hNil hSSeqTy
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      have hEvalFalse :
          __smtx_model_eval M (__eo_to_smt (nonemptyPrem s)) =
            SmtValue.Boolean false := by
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.eq (__eo_to_smt s) (SmtTerm.String []))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean false
        rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq, hSEval,
          smtx_eval_string_empty, smtx_eval_boolean_term_eq]
        rw [hSeqEmpty]
        simp [__smtx_model_eval_eq, native_veq]
      rw [hEvalFalse] at hEval
      cases hEval

private theorem premise_to_int_neg_one
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hPrem : eo_interprets M (toIntNegOnePrem s) true) :
    native_str_to_int (native_unpack_string ss) = (-1 : native_Int) := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq (SmtTerm.str_to_int (__eo_to_smt s))
            (SmtTerm.Numeral (-1 : native_Int))) =
        SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq, smtx_eval_str_to_int_term_eq, hSEval,
        smtx_eval_numeral_term_eq] at hEval
      simpa [__smtx_model_eval_str_to_int, __smtx_model_eval_eq,
        native_veq] using hEval

private theorem facts
    (M : SmtModel) (hM : model_wf M) (n s : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTy : __eo_typeof n = Term.Int)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (hPremNonempty : eo_interprets M (nonemptyPrem s) true)
    (hPremToInt : eo_interprets M (toIntNegOnePrem s) true) :
    eo_interprets M (concl n s) true := by
  have hBool := typed_concl n s hNTrans hSTrans hNTy hSTy
  have hNSmtTy :=
    StrInReFromIntDigRangeProof.smtx_typeof_of_eo_int n hNTrans hNTy
  have hSSmtTy := smtx_typeof_of_eo_seq s Term.Char hSTrans hSTy
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  rcases int_value_canonical hNEvalTy with ⟨z, hNEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hSeqNe : native_unpack_seq ss ≠ [] :=
    premise_nonempty_seq M hM s hSTrans hSTy ss hSEval hPremNonempty
  have hStrNe : native_unpack_string ss ≠ [] :=
    string_nonempty_of_seq_nonempty ss hSeqNe
  have hToInt :
      native_str_to_int (native_unpack_string ss) = (-1 : native_Int) :=
    premise_to_int_neg_one M s ss hSEval hPremToInt
  have hNotDigits :
      (native_unpack_string ss).all impl_native_char_is_digit ≠ true :=
    native_str_to_int_neg_one_nonempty_not_all_digits
      (native_unpack_string ss) hStrNe hToInt
  have hFromEval :
      __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt n)) =
        SmtValue.Seq (native_pack_string (native_str_from_int z)) := by
    rw [StrInReFromIntDigRangeProof.smtx_eval_str_from_int_term_eq, hNEval]
    rfl
  have hNoContains :
      native_seq_contains
          (native_unpack_seq (native_pack_string (native_str_from_int z)))
          (native_unpack_seq ss) =
        false := by
    cases hContains :
        native_seq_contains
          (native_unpack_seq (native_pack_string (native_str_from_int z)))
          (native_unpack_seq ss)
    · rfl
    · have hNeedleDigits :
          (native_unpack_string ss).all impl_native_char_is_digit = true :=
        contained_string_all_digits (native_str_from_int z) ss
          (StrInReFromIntDigRangeProof.native_str_from_int_all_digits z)
          hContains
      exact False.elim (hNotDigits hNeedleDigits)
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs n s)) =
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains
          (SmtTerm.str_from_int (__eo_to_smt n)) (__eo_to_smt s)) =
      __smtx_model_eval M (SmtTerm.Boolean false)
    rw [smtx_eval_str_contains_term_eq, hFromEval, hSEval,
      smtx_eval_boolean_term_eq]
    rw [RuleProofs.native_unpack_seq_pack_string] at hNoContains
    simpa [__smtx_model_eval_str_contains] using
      congrArg SmtValue.Boolean hNoContains
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs n s) (Term.Boolean false)
    hBool <| by
      rw [hEvalEq]
      exact RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (__eo_to_smt (Term.Boolean false)))

end StrFromIntNoCtnNondigitProof

public theorem cmd_step_str_from_int_no_ctn_nondigit_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_from_int_no_ctn_nondigit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_from_int_no_ctn_nondigit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_from_int_no_ctn_nondigit args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_from_int_no_ctn_nondigit args
      premises ≠ Term.Stuck :=
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
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n2 premises =>
                      cases premises with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.1
                          show StepRuleProperties M
                            [__eo_state_proven_nth s n1,
                              __eo_state_proven_nth s n2]
                            (__eo_prog_str_from_int_no_ctn_nondigit a1 a2
                              (Proof.pf (__eo_state_proven_nth s n1))
                              (Proof.pf (__eo_state_proven_nth s n2)))
                          generalize hP1 : __eo_state_proven_nth s n1 = P1
                          generalize hP2 : __eo_state_proven_nth s n2 = P2
                          have hProgRule :
                              __eo_prog_str_from_int_no_ctn_nondigit a1 a2
                                  (Proof.pf P1) (Proof.pf P2) ≠
                                Term.Stuck := by
                            rw [← hP1, ← hP2]
                            change __eo_cmd_step_proven s
                                CRule.str_from_int_no_ctn_nondigit
                                (CArgList.cons a1
                                  (CArgList.cons a2 CArgList.nil))
                                (CIndexList.cons n1
                                  (CIndexList.cons n2 CIndexList.nil)) ≠
                              Term.Stuck
                            exact hProg
                          rcases StrFromIntNoCtnNondigitProof.prog_form
                              a1 a2 P1 P2 hProgRule with
                            ⟨hPrem1Shape, hPrem2Shape, hProgEq⟩
                          have hResultTyProg :
                              __eo_typeof
                                  (__eo_prog_str_from_int_no_ctn_nondigit a1 a2
                                    (Proof.pf P1) (Proof.pf P2)) =
                                Term.Bool := by
                            rw [← hP1, ← hP2]
                            change __eo_typeof
                                (__eo_cmd_step_proven s
                                  CRule.str_from_int_no_ctn_nondigit
                                  (CArgList.cons a1
                                    (CArgList.cons a2 CArgList.nil))
                                  (CIndexList.cons n1
                                    (CIndexList.cons n2 CIndexList.nil))) =
                              Term.Bool
                            exact hResultTy
                          have hConclTy :
                              __eo_typeof
                                  (StrFromIntNoCtnNondigitProof.concl a1 a2) =
                                Term.Bool := by
                            rw [hProgEq] at hResultTyProg
                            exact hResultTyProg
                          rcases
                              StrFromIntNoCtnNondigitProof.typeof_args_of_concl_bool
                                a1 a2 hConclTy with
                            ⟨hA1Ty, hA2Ty⟩
                          rw [hProgEq]
                          refine ⟨?_,
                            RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (StrFromIntNoCtnNondigitProof.typed_concl a1 a2
                                hA1Trans hA2Trans hA1Ty hA2Ty)⟩
                          intro hTrue
                          have hPrem1Raw : eo_interprets M P1 true := by
                            have h := hTrue.true_here P1 (by simp)
                            exact h
                          have hPrem2Raw : eo_interprets M P2 true := by
                            have h := hTrue.true_here P2 (by simp)
                            exact h
                          have hPrem1 :
                              eo_interprets M
                                (StrFromIntNoCtnNondigitProof.nonemptyPrem a2)
                                true := by
                            simpa [hPrem1Shape] using hPrem1Raw
                          have hPrem2 :
                              eo_interprets M
                                (StrFromIntNoCtnNondigitProof.toIntNegOnePrem a2)
                                true := by
                            simpa [hPrem2Shape] using hPrem2Raw
                          exact StrFromIntNoCtnNondigitProof.facts M hM a1 a2
                            hA1Trans hA2Trans hA1Ty hA2Ty hPrem1 hPrem2
