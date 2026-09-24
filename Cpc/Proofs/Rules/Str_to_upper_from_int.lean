module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
import all Init.Data.Repr

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem prog_str_to_upper_from_int_eq_of_ne_stuck (n1 : Term) :
    n1 ≠ Term.Stuck ->
    __eo_prog_str_to_upper_from_int n1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.UOp UserOp.str_to_upper)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1)))
        (Term.Apply (Term.UOp UserOp.str_from_int) n1) := by
  intro hN1
  cases n1 <;> simp [__eo_prog_str_to_upper_from_int] at hN1 ⊢

private theorem eo_typeof_str_to_upper_str_from_int_arg_int_of_ne_stuck
    (T : Term)
    (h : __eo_typeof_str_to_lower (__eo_typeof_str_from_code T) ≠ Term.Stuck) :
    T = Term.UOp UserOp.Int := by
  cases T <;> simp [__eo_typeof_str_to_lower, __eo_typeof_str_from_code] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_str_from_code] at h ⊢

private theorem typeof_arg_of_prog_str_to_upper_from_int_bool (n1 : Term) :
    __eo_typeof (__eo_prog_str_to_upper_from_int n1) = Term.Bool ->
    __eo_typeof n1 = Term.UOp UserOp.Int := by
  intro hTy
  by_cases hN1 : n1 = Term.Stuck
  · subst n1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · rw [prog_str_to_upper_from_int_eq_of_ne_stuck n1 hN1] at hTy
    change __eo_typeof_eq
        (__eo_typeof_str_to_lower (__eo_typeof_str_from_code (__eo_typeof n1)))
        (__eo_typeof_str_from_code (__eo_typeof n1)) =
      Term.Bool at hTy
    have hLhsNotStuck :
        __eo_typeof_str_to_lower (__eo_typeof_str_from_code (__eo_typeof n1)) ≠
          Term.Stuck :=
      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof_str_to_lower (__eo_typeof_str_from_code (__eo_typeof n1)))
        (__eo_typeof_str_from_code (__eo_typeof n1)) hTy).1
    exact eo_typeof_str_to_upper_str_from_int_arg_int_of_ne_stuck
      (__eo_typeof n1) hLhsNotStuck

private theorem smtx_typeof_of_eo_int
    (n1 : Term)
    (hTrans : RuleProofs.eo_has_smt_translation n1)
    (hTy : __eo_typeof n1 = Term.UOp UserOp.Int) :
    __smtx_typeof (__eo_to_smt n1) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt n1) = __eo_to_smt_type (__eo_typeof n1) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation n1 hTrans
  rw [hTy] at hTyRaw
  simpa using hTyRaw

private theorem smtx_eval_str_to_upper_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_to_upper x) =
      __smtx_model_eval_str_to_upper (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_from_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_from_int x) =
      __smtx_model_eval_str_from_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem map_native_ssm_char_of_value_char :
    ∀ s : native_String,
      List.map (impl_native_ssm_char_of_value ∘ SmtValue.Char) s = s
  | [] => rfl
  | c :: cs => by
      simp [Function.comp_def, impl_native_ssm_char_of_value]

private theorem native_unpack_string_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp [native_unpack_string, native_pack_string, Smtm.native_unpack_pack_seq,
    map_native_ssm_char_of_value_char]

private theorem native_char_to_upper_digitChar_of_lt_10
    {d : Nat} (hd : d < 10) :
    impl_native_char_to_upper (Char.toNat (Nat.digitChar d)) =
      Char.toNat (Nat.digitChar d) := by
  unfold impl_native_char_to_upper Nat.digitChar
  by_cases h0 : d = 0
  · simp [h0]
  · by_cases h1 : d = 1
    · simp [h1]
    · by_cases h2 : d = 2
      · simp [h2]
      · by_cases h3 : d = 3
        · simp [h3]
        · by_cases h4 : d = 4
          · simp [h4]
          · by_cases h5 : d = 5
            · simp [h5]
            · by_cases h6 : d = 6
              · simp [h6]
              · by_cases h7 : d = 7
                · simp [h7]
                · by_cases h8 : d = 8
                  · simp [h8]
                  · have h9 : d = 9 := by omega
                    simp [h9]

private theorem map_native_char_to_upper_toDigitsCore :
    ∀ fuel n ds,
      List.map impl_native_char_to_upper (ds.map Char.toNat) = ds.map Char.toNat ->
        List.map impl_native_char_to_upper
            ((Nat.toDigitsCore 10 fuel n ds).map Char.toNat) =
          (Nat.toDigitsCore 10 fuel n ds).map Char.toNat
  | 0, _n, ds, hds => by
      simpa [Nat.toDigitsCore.eq_1] using hds
  | fuel + 1, n, ds, hds => by
      rw [Nat.toDigitsCore.eq_2]
      have hDigit :
          impl_native_char_to_upper (Char.toNat (Nat.digitChar (n % 10))) =
            Char.toNat (Nat.digitChar (n % 10)) :=
        native_char_to_upper_digitChar_of_lt_10
          (Nat.mod_lt n (by decide : 0 < 10))
      by_cases hDiv : n / 10 = 0
      · rw [if_pos hDiv]
        simp [hDigit, hds]
      · rw [if_neg hDiv]
        exact map_native_char_to_upper_toDigitsCore fuel (n / 10)
          ((Nat.digitChar (n % 10)) :: ds) (by
            simp [hDigit, hds])

private theorem native_str_to_upper_nat_toString (n : Nat) :
    native_str_to_upper (native_string_lit (toString n)) =
      native_string_lit (toString n) := by
  unfold native_str_to_upper native_string_lit
  rw [show (toString n).toList = Nat.toDigits 10 n by
    rw [show (toString n) = n.repr by rfl]
    unfold Nat.repr
    rw [String.toList_ofList]]
  rw [Nat.toDigits.eq_1]
  exact map_native_char_to_upper_toDigitsCore (n + 1) n [] (by simp)

private theorem native_str_to_upper_from_int (i : native_Int) :
    native_str_to_upper (native_str_from_int i) = native_str_from_int i := by
  cases i with
  | ofNat n =>
      unfold native_str_from_int
      have hNot : ¬ ((Int.ofNat n) < 0) :=
        Int.not_lt_of_ge (Int.natCast_nonneg n)
      rw [if_neg hNot]
      change native_str_to_upper (native_string_lit (toString n)) =
        native_string_lit (toString n)
      exact native_str_to_upper_nat_toString n
  | negSucc n =>
      unfold native_str_from_int
      have hNeg : (Int.negSucc n) < 0 :=
        Int.negSucc_lt_zero n
      rw [if_pos hNeg]
      rfl

private theorem typed___eo_prog_str_to_upper_from_int_impl
    (n1 : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n1)
    (hNTy : __eo_typeof n1 = Term.UOp UserOp.Int) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_to_upper_from_int n1) := by
  let rhs := Term.Apply (Term.UOp UserOp.str_from_int) n1
  let lhs := Term.Apply (Term.UOp UserOp.str_to_upper) rhs
  have hNSmtTy : __smtx_typeof (__eo_to_smt n1) = SmtType.Int :=
    smtx_typeof_of_eo_int n1 hNTrans hNTy
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n1)) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_from_int_eq, hNSmtTy]
    simp [native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq SmtType.Char := by
    have hRhsTy' :
        __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n1)) =
          SmtType.Seq SmtType.Char := by
      simpa [rhs, __eo_to_smt, __smtx_typeof] using hRhsTy
    change __smtx_typeof
        (SmtTerm.str_to_upper (SmtTerm.str_from_int (__eo_to_smt n1))) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_upper_eq, hRhsTy']
    simp [native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hNNotStuck : n1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation n1 hNTrans
  rw [prog_str_to_upper_from_int_eq_of_ne_stuck n1 hNNotStuck]
  exact hBoolEq

private theorem facts___eo_prog_str_to_upper_from_int_impl
    (M : SmtModel) (hM : model_wf M) (n1 : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n1)
    (hNTy : __eo_typeof n1 = Term.UOp UserOp.Int) :
    eo_interprets M (__eo_prog_str_to_upper_from_int n1) true := by
  let rhs := Term.Apply (Term.UOp UserOp.str_from_int) n1
  let lhs := Term.Apply (Term.UOp UserOp.str_to_upper) rhs
  have hNNotStuck : n1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation n1 hNTrans
  have hProg :
      __eo_prog_str_to_upper_from_int n1 =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [lhs, rhs] using
      prog_str_to_upper_from_int_eq_of_ne_stuck n1 hNNotStuck
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_str_to_upper_from_int_impl n1 hNTrans hNTy
  have hNSmtTy : __smtx_typeof (__eo_to_smt n1) = SmtType.Int :=
    smtx_typeof_of_eo_int n1 hNTrans hNTy
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n1)) = SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n1) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases int_value_canonical hNEvalTy with ⟨z, hNEval⟩
  have hFromEval :
      __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt n1)) =
        SmtValue.Seq (native_pack_string (native_str_from_int z)) := by
    rw [smtx_eval_str_from_int_term_eq, hNEval]
    rfl
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_upper (SmtTerm.str_from_int (__eo_to_smt n1))) =
      __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt n1))
    rw [smtx_eval_str_to_upper_term_eq, hFromEval]
    simp [__smtx_model_eval_str_to_upper, native_unpack_string_pack_string,
      native_str_to_upper_from_int]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_to_upper_from_int_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_upper_from_int args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_to_upper_from_int args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_upper_from_int args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_to_upper_from_int args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change __eo_typeof (__eo_prog_str_to_upper_from_int a1) = Term.Bool
                at hResultTy
              have hA1Ty : __eo_typeof a1 = Term.UOp UserOp.Int :=
                typeof_arg_of_prog_str_to_upper_from_int_bool a1 hResultTy
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_str_to_upper_from_int a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_str_to_upper_from_int_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_str_to_upper_from_int_impl M hM a1
                  hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_str_to_upper_from_int a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
