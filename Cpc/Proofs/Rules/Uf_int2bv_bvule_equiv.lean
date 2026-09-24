module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private abbrev bvuleTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvule) t) s

private abbrev ubvToIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.ubv_to_int) t

private abbrev ubvLeqTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.leq) (ubvToIntTerm t)) (ubvToIntTerm s)

private abbrev ufInt2bvBvuleConclusion (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvuleTerm t s)) (ubvLeqTerm t s)

private theorem smtx_eval_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem prog_uf_int2bv_bvule_equiv_eq_of_ne_stuck (t1 s1 : Term) :
    t1 ≠ Term.Stuck ->
    s1 ≠ Term.Stuck ->
    __eo_prog_uf_int2bv_bvule_equiv t1 s1 =
      ufInt2bvBvuleConclusion t1 s1 := by
  intro hT1 hS1
  cases t1 <;> cases s1 <;>
    simp [__eo_prog_uf_int2bv_bvule_equiv, ufInt2bvBvuleConclusion,
      bvuleTerm, ubvLeqTerm, ubvToIntTerm] at hT1 hS1 ⊢

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

private theorem requires_eq_true_stuck_of_ne (x y B : Term) :
    x ≠ y ->
    __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck := by
  intro hNe
  by_cases hReq :
      __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck
  · exact hReq
  · have hEq : y = x := eq_of_requires_eq_true_not_stuck x y B hReq
    exact False.elim (hNe hEq.symm)

private theorem typeof_args_of_prog_uf_int2bv_bvule_equiv_bool (t1 s1 : Term) :
    __eo_typeof (__eo_prog_uf_int2bv_bvule_equiv t1 s1) = Term.Bool ->
    ∃ w, __eo_typeof t1 = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof s1 = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  by_cases hT1 : t1 = Term.Stuck
  · subst t1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hS1 : s1 = Term.Stuck
    · subst s1
      cases t1 <;> simp [__eo_prog_uf_int2bv_bvule_equiv] at hT1 hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · rw [prog_uf_int2bv_bvule_equiv_eq_of_ne_stuck t1 s1 hT1 hS1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_bvult (__eo_typeof t1) (__eo_typeof s1))
          (__eo_typeof_lt (__eo_typeof__at_bvsize (__eo_typeof t1))
            (__eo_typeof__at_bvsize (__eo_typeof s1))) =
        Term.Bool at hTy
      cases hTTy : __eo_typeof t1 with
      | Apply ft wt =>
          cases ft with
          | UOp opt =>
              cases opt
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult,
                  __eo_typeof_lt, __eo_typeof__at_bvsize, __eo_requires,
                  __eo_eq, __is_arith_type, native_ite, native_teq,
                  native_not, hTTy] using hTy
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult,
                  __eo_typeof_lt, __eo_typeof__at_bvsize, __eo_requires,
                  __eo_eq, __is_arith_type, native_ite, native_teq,
                  native_not, hTTy] using hTy
              · cases hSTy : __eo_typeof s1 with
                | Apply fs ws =>
                    cases fs with
                    | UOp ops =>
                        cases ops
                        · exfalso
                          simpa [__eo_typeof_eq, __eo_typeof_bvult,
                            __eo_typeof_lt, __eo_typeof__at_bvsize,
                            __eo_requires, __eo_eq, __is_arith_type,
                            native_ite, native_teq, native_not, hTTy,
                            hSTy] using hTy
                        · exfalso
                          simpa [__eo_typeof_eq, __eo_typeof_bvult,
                            __eo_typeof_lt, __eo_typeof__at_bvsize,
                            __eo_requires, __eo_eq, __is_arith_type,
                            native_ite, native_teq, native_not, hTTy,
                            hSTy] using hTy
                        · by_cases hEq : wt = ws
                          · subst ws
                            exact ⟨wt, by simpa [hTTy], by simpa [hSTy], by
                              intro hW
                              subst wt
                              simp [__eo_typeof_eq, __eo_typeof_bvult,
                                __eo_typeof_lt, __eo_typeof__at_bvsize,
                                __eo_requires, __eo_eq, __is_arith_type,
                                native_ite, native_teq, native_not, hTTy,
                                hSTy] at hTy⟩
                          · exfalso
                            have hLeftStuck :
                                __eo_typeof_bvult
                                    (Term.Apply (Term.UOp UserOp.BitVec) wt)
                                    (Term.Apply (Term.UOp UserOp.BitVec) ws) =
                                  Term.Stuck := by
                              simpa [__eo_typeof_bvult] using
                                requires_eq_true_stuck_of_ne wt ws Term.Bool hEq
                            have hOuterBool :
                                __eo_typeof_eq
                                    (__eo_typeof_bvult
                                      (Term.Apply (Term.UOp UserOp.BitVec) wt)
                                      (Term.Apply (Term.UOp UserOp.BitVec) ws))
                                    (__eo_typeof_lt
                                      (__eo_typeof__at_bvsize
                                        (Term.Apply (Term.UOp UserOp.BitVec) wt))
                                      (__eo_typeof__at_bvsize
                                        (Term.Apply (Term.UOp UserOp.BitVec) ws))) =
                                  Term.Bool := by
                              simpa [__eo_typeof_bvult, __eo_typeof_lt,
                                __eo_typeof__at_bvsize, hTTy, hSTy] using hTy
                            rw [hLeftStuck] at hOuterBool
                            simp [__eo_typeof_eq] at hOuterBool
                        all_goals
                          exfalso
                          simpa [__eo_typeof_eq, __eo_typeof_bvult,
                            __eo_typeof_lt, __eo_typeof__at_bvsize,
                            __eo_requires, __eo_eq, __is_arith_type,
                            native_ite, native_teq, native_not, hTTy,
                            hSTy] using hTy
                    | _ =>
                        exfalso
                        simpa [__eo_typeof_eq, __eo_typeof_bvult,
                          __eo_typeof_lt, __eo_typeof__at_bvsize,
                          __eo_requires, __eo_eq, __is_arith_type,
                          native_ite, native_teq, native_not, hTTy,
                          hSTy] using hTy
                | _ =>
                    exfalso
                    simpa [__eo_typeof_eq, __eo_typeof_bvult,
                      __eo_typeof_lt, __eo_typeof__at_bvsize, __eo_requires,
                      __eo_eq, __is_arith_type, native_ite, native_teq,
                      native_not, hTTy, hSTy] using hTy
              all_goals
                exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_lt,
                  __eo_typeof__at_bvsize, __eo_requires, __eo_eq,
                  __is_arith_type, native_ite, native_teq, native_not,
                  hTTy] using hTy
          | _ =>
              simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_lt,
                __eo_typeof__at_bvsize, __eo_requires, __eo_eq,
                __is_arith_type, native_ite, native_teq, native_not,
                hTTy] at hTy
      | _ =>
          simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_lt,
            __eo_typeof__at_bvsize, __eo_requires, __eo_eq,
            __is_arith_type, native_ite, native_teq, native_not, hTTy] at hTy

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

private theorem smt_typeof_bvule_term_eq
    (t1 s1 : Term) :
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation s1 ->
    __eo_typeof (__eo_prog_uf_int2bv_bvule_equiv t1 s1) = Term.Bool ->
    __smtx_typeof (__eo_to_smt (bvuleTerm t1 s1)) = SmtType.Bool := by
  intro hT1Trans hS1Trans hResultTy
  rcases typeof_args_of_prog_uf_int2bv_bvule_equiv_bool t1 s1 hResultTy with
    ⟨w, hT1Type, hS1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t1 w hT1Trans hT1Type with
    ⟨n, hW, _hNonneg, hT1SmtTy⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width s1 (Term.Numeral n) hS1Trans
      (by simpa using hS1Type) with
    ⟨m, hM, _hMNonneg, hS1SmtTy⟩
  cases hM
  change __smtx_typeof (SmtTerm.bvule (__eo_to_smt t1) (__eo_to_smt s1)) =
    SmtType.Bool
  rw [__smtx_typeof.eq_57]
  simp [__smtx_typeof_bv_op_2_ret, hT1SmtTy, hS1SmtTy, native_nateq,
    native_ite]

private theorem smt_typeof_ubv_leq_term_eq
    (t1 s1 : Term) :
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation s1 ->
    __eo_typeof (__eo_prog_uf_int2bv_bvule_equiv t1 s1) = Term.Bool ->
    __smtx_typeof (__eo_to_smt (ubvLeqTerm t1 s1)) = SmtType.Bool := by
  intro hT1Trans hS1Trans hResultTy
  rcases typeof_args_of_prog_uf_int2bv_bvule_equiv_bool t1 s1 hResultTy with
    ⟨w, hT1Type, hS1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t1 w hT1Trans hT1Type with
    ⟨n, hW, _hNonneg, hT1SmtTy⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width s1 (Term.Numeral n) hS1Trans
      (by simpa using hS1Type) with
    ⟨m, hM, _hMNonneg, hS1SmtTy⟩
  cases hM
  change __smtx_typeof
      (SmtTerm.leq (SmtTerm.ubv_to_int (__eo_to_smt t1))
        (SmtTerm.ubv_to_int (__eo_to_smt s1))) =
    SmtType.Bool
  rw [typeof_leq_eq, smtx_typeof_ubv_to_int_term_eq,
    smtx_typeof_ubv_to_int_term_eq]
  simp [__smtx_typeof_bv_op_1_ret, __smtx_typeof_arith_overload_op_2_ret,
    hT1SmtTy, hS1SmtTy]

private theorem typed___eo_prog_uf_int2bv_bvule_equiv_impl
    (t1 s1 : Term) :
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation s1 ->
    __eo_typeof (__eo_prog_uf_int2bv_bvule_equiv t1 s1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_uf_int2bv_bvule_equiv t1 s1) := by
  intro hT1Trans hS1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hBvuleTy :
      __smtx_typeof (__eo_to_smt (bvuleTerm t1 s1)) = SmtType.Bool :=
    smt_typeof_bvule_term_eq t1 s1 hT1Trans hS1Trans hResultTy
  have hUbvLeqTy :
      __smtx_typeof (__eo_to_smt (ubvLeqTerm t1 s1)) = SmtType.Bool :=
    smt_typeof_ubv_leq_term_eq t1 s1 hT1Trans hS1Trans hResultTy
  rw [prog_uf_int2bv_bvule_equiv_eq_of_ne_stuck t1 s1 hT1NotStuck hS1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvuleTerm t1 s1) (ubvLeqTerm t1 s1)
    (by rw [hBvuleTy, hUbvLeqTy])
    (by rw [hBvuleTy]; decide)

private theorem eval_bvule_matches_ubv_leq
    (M : SmtModel) (hM : model_wf M) (t1 s1 : Term) :
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation s1 ->
    __eo_typeof (__eo_prog_uf_int2bv_bvule_equiv t1 s1) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvuleTerm t1 s1)) =
      __smtx_model_eval M (__eo_to_smt (ubvLeqTerm t1 s1)) := by
  intro hT1Trans hS1Trans hResultTy
  rcases typeof_args_of_prog_uf_int2bv_bvule_equiv_bool t1 s1 hResultTy with
    ⟨w, hT1Type, hS1Type, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t1 w hT1Trans hT1Type with
    ⟨n, hW, _hNonneg, hT1SmtTy⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width s1 (Term.Numeral n) hS1Trans
      (by simpa using hS1Type) with
    ⟨m, hMWidth, _hMNonneg, hS1SmtTy⟩
  cases hMWidth
  have hEvalTTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hT1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hT1Trans)
  have hEvalSTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s1)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hS1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s1)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hS1Trans)
  rcases bitvec_value_canonical hEvalTTy with ⟨tPayload, hEvalT⟩
  rcases bitvec_value_canonical hEvalSTy with ⟨sPayload, hEvalS⟩
  change __smtx_model_eval M (SmtTerm.bvule (__eo_to_smt t1) (__eo_to_smt s1)) =
    __smtx_model_eval M
      (SmtTerm.leq (SmtTerm.ubv_to_int (__eo_to_smt t1))
        (SmtTerm.ubv_to_int (__eo_to_smt s1)))
  rw [__smtx_model_eval.eq_57, smtx_eval_leq_term_eq,
    smtx_eval_ubv_to_int_term_eq, smtx_eval_ubv_to_int_term_eq, hEvalT,
    hEvalS]
  by_cases hLe : tPayload <= sPayload
  · rcases Int.lt_or_eq_of_le hLe with hLt | hEq
    · have hNotGt : ¬ sPayload < tPayload :=
        Int.not_lt_of_ge (Int.le_of_lt hLt)
      have hNeTS : tPayload ≠ sPayload := Int.ne_of_lt hLt
      have hNeST : sPayload ≠ tPayload := hNeTS.symm
      simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
        __smtx_model_eval_bvugt, __smtx_model_eval_eq,
        __smtx_model_eval_or, __smtx_model_eval_ubv_to_int,
        __smtx_model_eval_leq, native_zlt, SmtEval.native_zlt,
        native_zleq, SmtEval.native_zleq, native_veq, native_or,
        hLt, hNotGt, hNeTS, hNeST, hLe]
    · subst sPayload
      simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
        __smtx_model_eval_bvugt, __smtx_model_eval_eq,
        __smtx_model_eval_or, __smtx_model_eval_ubv_to_int,
        __smtx_model_eval_leq, native_zlt, SmtEval.native_zlt,
        native_zleq, SmtEval.native_zleq, native_veq, native_or]
  · have hGt : sPayload < tPayload := Int.lt_of_not_ge hLe
    have hNotLt : ¬ tPayload < sPayload :=
      Int.not_lt_of_ge (Int.le_of_lt hGt)
    have hNeST : sPayload ≠ tPayload := Int.ne_of_lt hGt
    have hNeTS : tPayload ≠ sPayload := hNeST.symm
    simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
      __smtx_model_eval_bvugt, __smtx_model_eval_eq,
      __smtx_model_eval_or, __smtx_model_eval_ubv_to_int,
      __smtx_model_eval_leq, native_zlt, SmtEval.native_zlt,
      native_zleq, SmtEval.native_zleq, native_veq, native_or,
      hGt, hNotLt, hNeTS, hNeST, hLe]

private theorem facts___eo_prog_uf_int2bv_bvule_equiv_impl
    (M : SmtModel) (hM : model_wf M) (t1 s1 : Term) :
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation s1 ->
    __eo_typeof (__eo_prog_uf_int2bv_bvule_equiv t1 s1) = Term.Bool ->
    eo_interprets M (__eo_prog_uf_int2bv_bvule_equiv t1 s1) true := by
  intro hT1Trans hS1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_uf_int2bv_bvule_equiv t1 s1) :=
    typed___eo_prog_uf_int2bv_bvule_equiv_impl t1 s1 hT1Trans hS1Trans hResultTy
  rw [prog_uf_int2bv_bvule_equiv_eq_of_ne_stuck t1 s1 hT1NotStuck hS1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_uf_int2bv_bvule_equiv_eq_of_ne_stuck t1 s1 hT1NotStuck
      hS1NotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvuleTerm t1 s1)))
      (__smtx_model_eval M (__eo_to_smt (ubvLeqTerm t1 s1)))
    rw [eval_bvule_matches_ubv_leq M hM t1 s1 hT1Trans hS1Trans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_uf_int2bv_bvule_equiv_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_int2bv_bvule_equiv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_int2bv_bvule_equiv args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_int2bv_bvule_equiv args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.uf_int2bv_bvule_equiv args premises ≠ Term.Stuck :=
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
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  change __eo_typeof (__eo_prog_uf_int2bv_bvule_equiv a1 a2) =
                    Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_uf_int2bv_bvule_equiv a1 a2) true
                    exact facts___eo_prog_uf_int2bv_bvule_equiv_impl M hM a1 a2
                      hA1Trans hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_uf_int2bv_bvule_equiv_impl a1 a2 hA1Trans
                        hA2Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
