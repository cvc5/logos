module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem prog_bv_ashr_zero_eq_of_ne_stuck (a1 n1 : Term) :
    a1 ≠ Term.Stuck ->
    n1 ≠ Term.Stuck ->
    __eo_prog_bv_ashr_zero a1 n1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0))) a1))
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0)) := by
  intro hA1 hN1
  cases a1 <;> cases n1 <;> simp [__eo_prog_bv_ashr_zero] at hA1 hN1 ⊢

private theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x := by
  intro hProg
  -- v4.33 `simp` unfolds `__eo_eq` under `decide` and desyncs the
  -- `Decidable` instance, so derive the guard by contradiction instead.
  have hEq : __eo_eq x y = Term.Boolean true := by
    apply Classical.byContradiction
    intro hne
    apply hProg
    simp [__eo_requires, native_ite, native_teq, hne]
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at hEq
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at hEq
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using hEq
      simpa [native_teq] using hDec

private theorem eo_requires_cond_eq_of_non_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) :
    x = y := by
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · have hxyFalse : native_teq x y = false := by
      cases hTeq : native_teq x y <;> simp_all
    simp [native_ite, hxyFalse] at h

private theorem typeof_eq_bool_operands_eq (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

private theorem typeof_args_of_prog_bv_ashr_zero_bool (a1 n1 : Term) :
    __eo_typeof (__eo_prog_bv_ashr_zero a1 n1) = Term.Bool ->
    ∃ w, __eo_typeof a1 = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      n1 = w ∧ w ≠ Term.Stuck := by
  intro hTy
  by_cases hA1 : a1 = Term.Stuck
  · subst a1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hN1 : n1 = Term.Stuck
    · subst n1
      cases a1 <;> simp [__eo_prog_bv_ashr_zero] at hA1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_bv_ashr_zero_eq_of_ne_stuck a1 n1 hA1 hN1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_bvand
            (__eo_typeof_int_to_bv (__eo_typeof n1) n1 (Term.UOp UserOp.Int))
            (__eo_typeof a1))
          (__eo_typeof_int_to_bv (__eo_typeof n1) n1 (Term.UOp UserOp.Int)) =
        Term.Bool at hTy
      cases hATy : __eo_typeof a1 with
      | Apply f w =>
          cases f with
          | UOp op =>
              cases op
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hATy] using hTy
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hATy] using hTy
              · cases hNTy : __eo_typeof n1 with
                | UOp nop =>
                    cases nop
                    · have hTy' :
                          __eo_typeof_eq
                              (__eo_typeof_bvand
                                (__eo_requires
                                  (__eo_gt n1 (Term.Numeral (-1 : native_Int)))
                                  (Term.Boolean true)
                                  (Term.Apply (Term.UOp UserOp.BitVec) n1))
                                (Term.Apply (Term.UOp UserOp.BitVec) w))
                              (__eo_requires
                                (__eo_gt n1 (Term.Numeral (-1 : native_Int)))
                                (Term.Boolean true)
                                (Term.Apply (Term.UOp UserOp.BitVec) n1)) =
                            Term.Bool := by
                        simpa [__eo_typeof_bvand, __eo_typeof_int_to_bv, hATy, hNTy] using hTy
                      have hAtReqNN :
                          __eo_requires
                              (__eo_gt n1 (Term.Numeral (-1 : native_Int)))
                              (Term.Boolean true)
                              (Term.Apply (Term.UOp UserOp.BitVec) n1) ≠
                            Term.Stuck := by
                        intro hReq
                        simp [__eo_typeof_eq, __eo_typeof_bvand, hReq] at hTy'
                      have hAtGuard :
                          __eo_gt n1 (Term.Numeral (-1 : native_Int)) =
                            Term.Boolean true :=
                        eo_requires_cond_eq_of_non_stuck hAtReqNN
                      have hAtReqEq :
                          __eo_requires
                              (__eo_gt n1 (Term.Numeral (-1 : native_Int)))
                              (Term.Boolean true)
                              (Term.Apply (Term.UOp UserOp.BitVec) n1) =
                            Term.Apply (Term.UOp UserOp.BitVec) n1 := by
                        simp [__eo_requires, hAtGuard, native_ite, native_teq,
                          native_not]
                      have hTypesEq :=
                        typeof_eq_bool_operands_eq
                          (__eo_typeof_bvand
                            (__eo_requires
                              (__eo_gt n1 (Term.Numeral (-1 : native_Int)))
                              (Term.Boolean true)
                              (Term.Apply (Term.UOp UserOp.BitVec) n1))
                            (Term.Apply (Term.UOp UserOp.BitVec) w))
                          (__eo_requires
                            (__eo_gt n1 (Term.Numeral (-1 : native_Int)))
                            (Term.Boolean true)
                            (Term.Apply (Term.UOp UserOp.BitVec) n1))
                          hTy'
                      have hReqEq :
                          __eo_requires (__eo_eq n1 w) (Term.Boolean true)
                              (Term.Apply (Term.UOp UserOp.BitVec) n1) =
                            Term.Apply (Term.UOp UserOp.BitVec) n1 := by
                        simpa [__eo_typeof_bvand, hAtReqEq] using hTypesEq
                      have hReqNN :
                          __eo_requires (__eo_eq n1 w) (Term.Boolean true)
                              (Term.Apply (Term.UOp UserOp.BitVec) n1) ≠
                            Term.Stuck := by
                        rw [hReqEq]
                        intro h
                        cases h
                      have hEq : w = n1 :=
                        eq_of_requires_eq_true_not_stuck n1 w
                          (Term.Apply (Term.UOp UserOp.BitVec) n1) hReqNN
                      subst w
                      exact ⟨n1, by simpa [hATy], rfl, hN1⟩
                    all_goals
                      exfalso
                      simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                        __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                        hATy, hNTy] using hTy
                | _ =>
                    exfalso
                    simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                      __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                      hATy, hNTy] using hTy
              all_goals
                exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hATy] using hTy
          | _ =>
              simp [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                hATy] at hTy
      | _ =>
          simp [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
            __eo_requires, __eo_eq, native_ite, native_teq, native_not,
            hATy] at hTy

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 w : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat n) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x1) rfl
      hX1Trans hX1Type
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hX1Trans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hX1Trans hSmtType)

private theorem smt_typeof_bv_zero
    (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro hNonneg
  change __smtx_typeof (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral 0)) =
    SmtType.BitVec (native_int_to_nat n)
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary n (native_mod_total 0 (native_int_pow2 n))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total 0 (native_int_pow2 n))
            (native_mod_total
              (native_mod_total 0 (native_int_pow2 n))
              (native_int_pow2 n)) =
          true :=
      native_mod_total_canonical n 0
    simp [SmtEval.native_and, hNonneg, hMod, native_ite]
  simpa [native_ite, hNonneg] using
    TranslationProofs.smtx_typeof_binary_of_non_none n
      (native_mod_total 0 (native_int_pow2 n)) hNN

private theorem smt_typeof_bvashr_zero_eq_zero
    (a1 n1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_bv_ashr_zero a1 n1) = Term.Bool ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0))) a1)) =
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0))) := by
  intro hA1Trans hResultTy
  rcases typeof_args_of_prog_bv_ashr_zero_bool a1 n1 hResultTy with
    ⟨w, hA1Type, hN1, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width a1 w hA1Trans hA1Type with
    ⟨n, hW, hNonneg, hA1SmtTy⟩
  subst w
  subst n1
  have hZeroTy := smt_typeof_bv_zero n hNonneg
  change __smtx_typeof
      (SmtTerm.bvashr
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
        (__eo_to_smt a1)) =
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hA1SmtTy, hZeroTy, native_nateq, native_ite]

private theorem typed___eo_prog_bv_ashr_zero_impl (a1 n1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_bv_ashr_zero a1 n1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_ashr_zero a1 n1) := by
  intro hA1Trans hResultTy
  have hA1NotStuck : a1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
  rcases typeof_args_of_prog_bv_ashr_zero_bool a1 n1 hResultTy with
    ⟨w, _hA1Type, hN1, hW⟩
  subst n1
  rw [prog_bv_ashr_zero_eq_of_ne_stuck a1 w hA1NotStuck hW]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) a1)
    (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))
    (smt_typeof_bvashr_zero_eq_zero a1 w hA1Trans (by simpa using hResultTy))
    (by
      rw [smt_typeof_bvashr_zero_eq_zero a1 w hA1Trans (by simpa using hResultTy)]
      rcases typeof_args_of_prog_bv_ashr_zero_bool a1 w (by simpa using hResultTy) with
        ⟨w', hA1Type, hWEq, _hW'⟩
      subst w'
      rcases smt_bitvec_type_of_eo_bitvec_type_with_width a1 w hA1Trans hA1Type with
        ⟨n, hWidth, hNonneg, _hA1SmtTy⟩
      subst w
      rw [smt_typeof_bv_zero n hNonneg]
      simp)

private theorem eval_bvashr_zero_self
    (M : SmtModel) (hM : model_wf M) (a1 n1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_bv_ashr_zero a1 n1) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0))) a1)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv n1) (Term.Numeral 0))) := by
  intro hA1Trans hResultTy
  rcases typeof_args_of_prog_bv_ashr_zero_bool a1 n1 hResultTy with
    ⟨w, hA1Type, hN1, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width a1 w hA1Trans hA1Type with
    ⟨n, hW, hNonneg, hA1SmtTy⟩
  subst w
  subst n1
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hA1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hA1Trans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalA1⟩
  have hZeroEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))) =
        SmtValue.Binary n (native_mod_total 0 (native_int_pow2 n)) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral 0)) =
      SmtValue.Binary n (native_mod_total 0 (native_int_pow2 n))
    simp [native_ite, hNonneg]
  change __smtx_model_eval M
      (SmtTerm.bvashr
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
        (__eo_to_smt a1)) =
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
  rw [show __smtx_model_eval M
        (SmtTerm.bvashr
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
          (__eo_to_smt a1)) =
      __smtx_model_eval_bvashr
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))
        (__smtx_model_eval M (__eo_to_smt a1)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [hZeroEval, hEvalA1]
  have hExtractWidth : n + -1 + 1 + -(n + -1) = (1 : native_Int) := by
    calc
      n + -1 + 1 + -(n + -1) = n + (-n + 1) := by
        simp [Int.neg_add, Int.add_assoc, Int.add_comm, Int.add_left_comm]
      _ = (n + -n) + 1 := by rw [← Int.add_assoc]
      _ = 0 + 1 := by rw [Int.add_right_neg]
      _ = 1 := rfl
  simp [__smtx_model_eval_bvashr, __smtx_model_eval_ite, __smtx_model_eval_eq,
    __smtx_model_eval_extract, __smtx_model_eval__, __smtx_bv_sizeof_value,
    __smtx_model_eval_bvlshr, __smtx_model_eval_bvnot, native_binary_extract,
    SmtEval.native_div_total, SmtEval.native_mod_total, SmtEval.native_zplus,
    SmtEval.native_zneg, native_veq, hExtractWidth]

private theorem facts___eo_prog_bv_ashr_zero_impl
    (M : SmtModel) (hM : model_wf M) (a1 n1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_bv_ashr_zero a1 n1) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_ashr_zero a1 n1) true := by
  intro hA1Trans hResultTy
  have hA1NotStuck : a1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
  rcases typeof_args_of_prog_bv_ashr_zero_bool a1 n1 hResultTy with
    ⟨w, _hA1Type, hN1, hW⟩
  subst n1
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bv_ashr_zero a1 w) :=
    typed___eo_prog_bv_ashr_zero_impl a1 w hA1Trans (by simpa using hResultTy)
  rw [prog_bv_ashr_zero_eq_of_ne_stuck a1 w hA1NotStuck hW]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_ashr_zero_eq_of_ne_stuck a1 w hA1NotStuck hW] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) a1)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
    rw [eval_bvashr_zero_self M hM a1 w hA1Trans (by simpa using hResultTy)]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))

public theorem cmd_step_bv_ashr_zero_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ashr_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ashr_zero args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ashr_zero args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ashr_zero args premises ≠ Term.Stuck :=
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
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  change __eo_typeof (__eo_prog_bv_ashr_zero a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_ashr_zero a1 a2) true
                    exact facts___eo_prog_bv_ashr_zero_impl M hM a1 a2
                      hA1Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bv_ashr_zero_impl a1 a2 hA1Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
