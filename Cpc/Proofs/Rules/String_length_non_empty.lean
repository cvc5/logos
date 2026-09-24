module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Extracts the `__str_is_empty = true` guard from a non-stuck rule instance. -/
private theorem empty_of_prog_string_length_non_empty_not_stuck
    (s t : Term) :
  __eo_prog_string_length_non_empty
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq s) t))) ≠
    Term.Stuck ->
  __str_is_empty t = Term.Boolean true := by
  intro hProg
  cases hE : __str_is_empty t with
  | Boolean b =>
      cases b with
      | false =>
          simp [__eo_prog_string_length_non_empty, hE, __eo_requires,
            native_ite, native_teq] at hProg
      | true =>
          simp
  | _ =>
      simp [__eo_prog_string_length_non_empty, hE, __eo_requires,
        native_ite, native_teq] at hProg

/-- Simplifies EO-to-SMT translation for equality. -/
private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

/-- Computes the SMT type of an EO `str.len` term once its argument is known to be a sequence. -/
private theorem typeof_eo_str_len_of_seq
    (s : Term) (T : SmtType)
    (hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len s)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int
  rw [typeof_str_len_eq, hSTySeq]
  simp [__smtx_typeof_seq_op_1_ret]

/-- Computes the SMT type of the EO numeral `0`. -/
private theorem typeof_eo_zero :
    __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
  rw [__smtx_typeof.eq_2]

/-- Evaluates EO `str.len` once the translated argument has been evaluated to a sequence. -/
private theorem eval_eo_str_len_of_seq
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hEvalS : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_len s)) =
      SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) := by
  change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
    SmtValue.Numeral (native_seq_len (native_unpack_seq ss))
  rw [smtx_eval_str_len_term_eq, hEvalS]
  rfl

/-- Evaluates the translated EO numeral `0`. -/
private theorem eval_eo_zero (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral 0)) = SmtValue.Numeral 0 := by
  change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
  rw [__smtx_model_eval.eq_2]

/-- Characterizes the SMT type and evaluation of syntactically empty string terms. -/
private theorem empty_term_smt_info
    (t : Term)
    (hEmpty : __str_is_empty t = Term.Boolean true)
    (hTrans : RuleProofs.eo_has_smt_translation t) :
  ∃ T,
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ∧
    ∀ M, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq (SmtSeq.empty T) := by
  cases t with
  | String s =>
      by_cases hs : s = native_string_lit ""
      · subst s
        refine ⟨SmtType.Char, ?_, ?_⟩
        · change __smtx_typeof (SmtTerm.String (native_string_lit "")) = SmtType.Seq SmtType.Char
          rw [__smtx_typeof.eq_4]
          simp [native_string_lit, native_string_valid, native_ite]
        · intro M
          change __smtx_model_eval M (SmtTerm.String (native_string_lit "")) =
            SmtValue.Seq (SmtSeq.empty SmtType.Char)
          rw [__smtx_model_eval.eq_4]
          simp [native_pack_string, native_pack_seq, native_string_lit]
      · cases s with
        | nil =>
            exact False.elim (hs (by simp [native_string_lit]))
        | cons c cs =>
            simp [__str_is_empty] at hEmpty
  | UOp1 op x =>
      cases op with
      | seq_empty =>
          cases x with
          | Apply f U =>
              cases f with
              | UOp op =>
                  cases op with
                  | Seq =>
                      have hTrans' :
                          __smtx_typeof
                              (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))) ≠
                            SmtType.None := hTrans
                      by_cases hU : __eo_to_smt_type U = SmtType.None
                      · exfalso
                        have hSeqTyNone :
                            __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) =
                              SmtType.None := by
                          rw [TranslationProofs.eo_to_smt_type_seq]
                          unfold __smtx_typeof_guard
                          simp [hU, native_ite, native_Teq]
                        apply hTrans'
                        change
                          __smtx_typeof
                              (__eo_to_smt_seq_empty
                                (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
                            SmtType.None
                        rw [hSeqTyNone]
                        change __smtx_typeof SmtTerm.None = SmtType.None
                        simp
                      · refine ⟨__eo_to_smt_type U, ?_, ?_⟩
                        · have hGuard :
                              __smtx_typeof_guard (__eo_to_smt_type U)
                                (SmtType.Seq (__eo_to_smt_type U)) =
                                SmtType.Seq (__eo_to_smt_type U) := by
                            unfold __smtx_typeof_guard
                            simp [hU, native_ite, native_Teq]
                          have hSeqTy :
                              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) =
                                SmtType.Seq (__eo_to_smt_type U) := by
                            rw [TranslationProofs.eo_to_smt_type_seq]
                            exact hGuard
                          have hSeqEmptyNonNone :
                              __smtx_typeof (SmtTerm.seq_empty (__eo_to_smt_type U)) ≠
                                SmtType.None := by
                            change
                              __smtx_typeof
                                  (__eo_to_smt_seq_empty
                                    (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) ≠
                                SmtType.None at hTrans'
                            rw [hSeqTy] at hTrans'
                            change __smtx_typeof (SmtTerm.seq_empty (__eo_to_smt_type U)) ≠
                              SmtType.None at hTrans'
                            exact hTrans'
                          have hSeqEmptyTy :
                              __smtx_typeof (SmtTerm.seq_empty (__eo_to_smt_type U)) =
                                SmtType.Seq (__eo_to_smt_type U) :=
                            TranslationProofs.smtx_typeof_seq_empty_of_non_none
                              (__eo_to_smt_type U) hSeqEmptyNonNone
                          change
                            __smtx_typeof
                                (__eo_to_smt_seq_empty
                                  (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
                              SmtType.Seq (__eo_to_smt_type U)
                          rw [hSeqTy]
                          exact hSeqEmptyTy
                        · intro M
                          have hGuard :
                              __smtx_typeof_guard (__eo_to_smt_type U)
                                (SmtType.Seq (__eo_to_smt_type U)) =
                                SmtType.Seq (__eo_to_smt_type U) := by
                            unfold __smtx_typeof_guard
                            simp [hU, native_ite, native_Teq]
                          have hSeqTy :
                              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) =
                                SmtType.Seq (__eo_to_smt_type U) := by
                            rw [TranslationProofs.eo_to_smt_type_seq]
                            exact hGuard
                          change
                            __smtx_model_eval M
                                (__eo_to_smt_seq_empty
                                  (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
                              SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U))
                          rw [hSeqTy]
                          change __smtx_model_eval M (SmtTerm.seq_empty (__eo_to_smt_type U)) =
                            SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U))
                          rw [__smtx_model_eval.eq_79]
                  | _ =>
                      simp [__str_is_empty] at hEmpty
              | _ =>
                  simp [__str_is_empty] at hEmpty
          | _ =>
              simp [__str_is_empty] at hEmpty
      | _ =>
          simp [__str_is_empty] at hEmpty
  | _ =>
      simp [__str_is_empty] at hEmpty

/-- Shows that the EO program for `string_length_non_empty` is well typed. -/
private theorem typed___eo_prog_string_length_non_empty_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_string_length_non_empty (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_string_length_non_empty (Proof.pf x1)) := by
  intro hXBool hProg
  cases x1 with
  | Apply f prem =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases prem with
              | Apply f2 t =>
                  cases f2 with
                  | Apply f1 s =>
                      cases f1 with
                      | UOp op' =>
                          cases op' with
                          | eq =>
                              have hEqBool :
                                  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hXBool
                              have hEmpty : __str_is_empty t = Term.Boolean true :=
                                empty_of_prog_string_length_non_empty_not_stuck s t hProg
                              rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
                                  hEqBool with
                                ⟨hSTy, hSNonNone⟩
                              have hTTrans : RuleProofs.eo_has_smt_translation t := by
                                unfold RuleProofs.eo_has_smt_translation
                                intro hNone
                                apply hSNonNone
                                rw [hSTy]
                                exact hNone
                              rcases empty_term_smt_info t hEmpty hTTrans with ⟨T, hTTy, _⟩
                              have hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
                                rw [hSTy, hTTy]
                              have hLenTy :
                                  __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len s)) =
                                    SmtType.Int := by
                                exact typeof_eo_str_len_of_seq s T hSTySeq
                              have hNumTy :
                                  __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
                                exact typeof_eo_zero
                              have hEqLenBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                      (Term.Numeral 0)) := by
                                exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                  (Term.Apply Term.str_len s) (Term.Numeral 0)
                                  (by rw [hLenTy, hNumTy])
                                  (by rw [hLenTy]; simp)
                              have hNotLenBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply Term.not
                                      (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                        (Term.Numeral 0))) :=
                                RuleProofs.eo_has_bool_type_not_of_bool_arg _ hEqLenBool
                              change RuleProofs.eo_has_bool_type
                                (__eo_requires (__str_is_empty t) (Term.Boolean true)
                                  (Term.Apply Term.not
                                    (Term.Apply
                                      (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                      (Term.Numeral 0))))
                              rw [hEmpty]
                              simpa [__eo_requires, native_ite, native_teq, native_not] using
                                hNotLenBool
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

/-- Shows that the EO program for `string_length_non_empty` is semantically valid. -/
private theorem facts___eo_prog_string_length_non_empty_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_string_length_non_empty (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_string_length_non_empty (Proof.pf x1)) true := by
  intro hXTrue hProg
  cases x1 with
  | Apply f prem =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases prem with
              | Apply f2 t =>
                  cases f2 with
                  | Apply f1 s =>
                      cases f1 with
                      | UOp op' =>
                          cases op' with
                          | eq =>
                              have hEqFalse :
                                  eo_interprets M (Term.Apply (Term.Apply Term.eq s) t) false :=
                                RuleProofs.eo_interprets_not_true_implies_false M _ hXTrue
                              have hEqBool :
                                  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) :=
                                RuleProofs.eo_has_bool_type_of_interprets_false M _ hEqFalse
                              have hEmpty : __str_is_empty t = Term.Boolean true :=
                                empty_of_prog_string_length_non_empty_not_stuck s t hProg
                              rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
                                  hEqBool with
                                ⟨hSTy, hSNonNone⟩
                              have hTTrans : RuleProofs.eo_has_smt_translation t := by
                                unfold RuleProofs.eo_has_smt_translation
                                intro hNone
                                apply hSNonNone
                                rw [hSTy]
                                exact hNone
                              rcases empty_term_smt_info t hEmpty hTTrans with ⟨T, hTTy, hEvalT⟩
                              have hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
                                rw [hSTy, hTTy]
                              have hEvalSTy :
                                  __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
                                    SmtType.Seq T :=
                                smt_model_eval_preserves_type M hM (__eo_to_smt s) (SmtType.Seq T)
                                  hSTySeq (by simp) (type_inhabited_seq T)
                              rcases seq_value_canonical hEvalSTy with ⟨ss, hEvalS⟩
                              cases ss with
                              | empty T0 =>
                                  have hSeqTy : SmtType.Seq T0 = SmtType.Seq T := by
                                    simpa [__smtx_typeof_value, __smtx_typeof_seq_value, hEvalS]
                                      using hEvalSTy
                                  have hT0 : T0 = T := by
                                    injection hSeqTy
                                  have hEvalT' :
                                      __smtx_model_eval M (__eo_to_smt t) =
                                        SmtValue.Seq (SmtSeq.empty T0) := by
                                    rw [hT0]
                                    exact hEvalT M
                                  have hEqTrue :
                                      eo_interprets M (Term.Apply (Term.Apply Term.eq s) t) true := by
                                    exact RuleProofs.eo_interprets_eq_of_rel M s t hEqBool <| by
                                      rw [hEvalS, hEvalT']
                                      exact RuleProofs.smt_value_rel_refl
                                        (SmtValue.Seq (SmtSeq.empty T0))
                                  have hEqEvalFalse :
                                      __smtx_model_eval M
                                          (__eo_to_smt (Term.Apply (Term.Apply Term.eq s) t)) =
                                        SmtValue.Boolean false := by
                                    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hEqFalse
                                    cases hEqFalse with
                                    | intro_false _ hEval =>
                                        exact hEval
                                  have hEqEvalTrue :
                                      __smtx_model_eval M
                                          (__eo_to_smt (Term.Apply (Term.Apply Term.eq s) t)) =
                                        SmtValue.Boolean true := by
                                    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hEqTrue
                                    cases hEqTrue with
                                    | intro_true _ hEval =>
                                        exact hEval
                                  rw [hEqEvalTrue] at hEqEvalFalse
                                  cases hEqEvalFalse
                              | cons v vs =>
                                  have hLenTy :
                                      __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len s)) =
                                        SmtType.Int := by
                                    exact typeof_eo_str_len_of_seq s T hSTySeq
                                  have hNumTy :
                                      __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
                                    exact typeof_eo_zero
                                  have hEqLenBool :
                                      RuleProofs.eo_has_bool_type
                                        (Term.Apply
                                          (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                          (Term.Numeral 0)) := by
                                    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                      (Term.Apply Term.str_len s) (Term.Numeral 0)
                                      (by rw [hLenTy, hNumTy])
                                      (by rw [hLenTy]; simp)
                                  have hEvalLen :
                                      __smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_len s)) =
                                        SmtValue.Numeral
                                          (native_seq_len (native_unpack_seq (SmtSeq.cons v vs))) := by
                                    exact eval_eo_str_len_of_seq M s (SmtSeq.cons v vs) hEvalS
                                  have hEqLenEval :
                                      __smtx_model_eval M
                                          (__eo_to_smt
                                            (Term.Apply
                                              (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                              (Term.Numeral 0))) =
                                        SmtValue.Boolean false := by
                                    rw [eo_to_smt_eq_eq, smtx_eval_eq_term_eq]
                                    rw [hEvalLen]
                                    rw [eval_eo_zero M]
                                    unfold __smtx_model_eval_eq native_veq
                                    change
                                      SmtValue.Boolean
                                          (decide
                                            (SmtValue.Numeral
                                                (native_seq_len
                                                  (native_unpack_seq (SmtSeq.cons v vs))) =
                                              SmtValue.Numeral 0)) =
                                        SmtValue.Boolean false
                                    congr
                                  have hEqLenFalse :
                                      eo_interprets M
                                        (Term.Apply
                                          (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                          (Term.Numeral 0))
                                        false :=
                                    RuleProofs.eo_interprets_of_bool_eval M _ false hEqLenBool hEqLenEval
                                  have hNotLen :
                                      eo_interprets M
                                        (Term.Apply Term.not
                                          (Term.Apply
                                            (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                            (Term.Numeral 0))) true :=
                                    RuleProofs.eo_interprets_not_of_false M
                                      (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                        (Term.Numeral 0))
                                      hEqLenFalse
                                  change eo_interprets M
                                    (__eo_requires (__str_is_empty t) (Term.Boolean true)
                                      (Term.Apply Term.not
                                        (Term.Apply
                                          (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                          (Term.Numeral 0)))) true
                                  rw [hEmpty]
                                  simpa [__eo_requires, native_ite, native_teq, native_not] using
                                    hNotLen
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

public theorem cmd_step_string_length_non_empty_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_length_non_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_length_non_empty args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_length_non_empty args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.string_length_non_empty args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgNonEmpty' :
                  __eo_prog_string_length_non_empty
                    (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck := by
                change __eo_prog_string_length_non_empty
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                exact hProg
              have hProgNonEmpty :
                  __eo_prog_string_length_non_empty (Proof.pf X1) ≠ Term.Stuck := by
                simpa [X1] using hProgNonEmpty'
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_string_length_non_empty (Proof.pf X1)) true
                exact facts___eo_prog_string_length_non_empty_impl M hM X1
                  (hTrue X1 (by simp [X1, premiseTermList])) hProgNonEmpty
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type
                      (__eo_prog_string_length_non_empty (Proof.pf X1))
                    exact typed___eo_prog_string_length_non_empty_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgNonEmpty)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
