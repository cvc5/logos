module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_eq_true_eq {x y : Term} :
    __eo_eq x y = Term.Boolean true ->
    y = x := by
  intro h
  exact RuleProofs.eq_of_eo_eq_true x y h

private theorem eo_and_eq_true_left {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true := by
  intro h
  exact (RuleProofs.eo_and_eq_true_args x y h).1

private theorem eo_and_eq_true_right {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    y = Term.Boolean true := by
  intro h
  exact (RuleProofs.eo_and_eq_true_args x y h).2

private theorem bv_urem_self_shape_of_ne_stuck (x w P : Term) :
    __eo_prog_bv_urem_self x w (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
    ∃ pw px,
      P = Term.Apply (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px) := by
  intro hProg
  have hx : x ≠ Term.Stuck := by
    intro hx
    subst x
    exact hProg (__eo_prog_bv_urem_self.eq_1 w (Proof.pf P))
  have hw : w ≠ Term.Stuck := by
    intro hw
    subst w
    exact hProg (__eo_prog_bv_urem_self.eq_2 x (Proof.pf P) hx)
  refine ⟨hx, hw, ?_⟩
  by_cases hShape : ∃ pw px,
      P = Term.Apply (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px)
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_urem_self.eq_4 x w (Proof.pf P) hx hw (by
        intro pw px hP
        cases hP
        exact hShape ⟨pw, px, rfl⟩)))

private theorem bv_urem_self_guard_eqs_of_ne_stuck
    {x w pw px body : Term} :
    __eo_requires (__eo_and (__eo_eq w pw) (__eo_eq x px))
        (Term.Boolean true) body ≠ Term.Stuck ->
    pw = w ∧ px = x := by
  intro hReq
  have hGuard :
      __eo_and (__eo_eq w pw) (__eo_eq x px) = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReq
  exact ⟨eo_eq_true_eq (eo_and_eq_true_left hGuard),
    eo_eq_true_eq (eo_and_eq_true_right hGuard)⟩

private theorem prog_bv_urem_self_canonical_eq_of_ne_stuck (x w : Term) :
    x ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    __eo_prog_bv_urem_self x w
        (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x))) =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x))
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0)) := by
  intro hx hw
  rw [__eo_prog_bv_urem_self.eq_3 x w w x hx hw]
  rw [RuleProofs.eo_eq_self_of_ne_stuck w hw,
    RuleProofs.eo_eq_self_of_ne_stuck x hx]
  simp [__eo_and, __eo_requires, native_ite, native_teq, native_and,
    native_not, SmtEval.native_not]

private theorem typeof_args_of_urem_self_body_bool (x w : Term) :
    w ≠ Term.Stuck ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x))
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) = Term.Bool ->
    ∃ u, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) u ∧ w = u := by
  intro hW hTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x) (__eo_typeof x))
      (__eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int)) =
    Term.Bool at hTy
  cases hXTy : __eo_typeof x with
  | Apply f u =>
      cases f with
      | UOp op =>
          cases op
          · exfalso
            simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
              __eo_requires, __eo_eq, native_ite, native_teq, native_not,
              hXTy] using hTy
          · exfalso
            simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
              __eo_requires, __eo_eq, native_ite, native_teq, native_not,
              hXTy] using hTy
          · -- BitVec case
            by_cases hu : u = Term.Stuck
            · exfalso
              subst u
              simp [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                hXTy] at hTy
            · cases hWTy : __eo_typeof w with
              | UOp nop =>
                  cases nop
                  · -- Int width type
                    have hTy' :
                        __eo_typeof_eq
                            (Term.Apply (Term.UOp UserOp.BitVec) u)
                            (__eo_requires
                              (__eo_gt w (Term.Numeral (-1 : native_Int)))
                              (Term.Boolean true)
                              (Term.Apply (Term.UOp UserOp.BitVec) w)) =
                          Term.Bool := by
                      simpa [__eo_typeof_bvand, __eo_typeof_int_to_bv, hXTy, hWTy,
                        hW, RuleProofs.eo_eq_self_of_ne_stuck u hu,
                        __eo_requires,
                        native_ite, native_teq, native_not,
                        SmtEval.native_not] using hTy
                    have hOpEq :=
                      support_eo_typeof_eq_bool_operands_eq _ _ hTy'
                    have hReqNN :
                        __eo_requires
                            (__eo_gt w (Term.Numeral (-1 : native_Int)))
                            (Term.Boolean true)
                            (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
                          Term.Stuck := by
                      rw [← hOpEq]
                      intro h
                      cases h
                    have hGuard :=
                      support_eo_requires_cond_eq_of_non_stuck hReqNN
                    have hReqEq :
                        __eo_requires
                            (__eo_gt w (Term.Numeral (-1 : native_Int)))
                            (Term.Boolean true)
                            (Term.Apply (Term.UOp UserOp.BitVec) w) =
                          Term.Apply (Term.UOp UserOp.BitVec) w := by
                      simp [__eo_requires, hGuard, native_ite, native_teq,
                        native_not]
                    have hBv :
                        Term.Apply (Term.UOp UserOp.BitVec) u =
                          Term.Apply (Term.UOp UserOp.BitVec) w :=
                      hOpEq.trans hReqEq
                    injection hBv with _ hUW
                    exact ⟨u, rfl, hUW.symm⟩
                  all_goals
                    exfalso
                    simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                      __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                      hXTy, hWTy, hu,
                      RuleProofs.eo_eq_self_of_ne_stuck u hu] using hTy
              | _ =>
                  exfalso
                  simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
                    __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                    hXTy, hWTy, hu,
                    RuleProofs.eo_eq_self_of_ne_stuck u hu] using hTy
          all_goals
            exfalso
            simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
              __eo_requires, __eo_eq, native_ite, native_teq, native_not,
              hXTy] using hTy
      | _ =>
          exfalso
          simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
            __eo_requires, __eo_eq, native_ite, native_teq, native_not,
            hXTy] using hTy
  | _ =>
      exfalso
      simpa [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_int_to_bv,
        __eo_requires, __eo_eq, native_ite, native_teq, native_not,
        hXTy] using hTy

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

private theorem smt_typeof_bv_const
    (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro hNonneg
  change __smtx_typeof (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral k)) =
    SmtType.BitVec (native_int_to_nat n)
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary n (native_mod_total k (native_int_pow2 n))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total k (native_int_pow2 n))
            (native_mod_total
              (native_mod_total k (native_int_pow2 n))
              (native_int_pow2 n)) =
          true :=
      native_mod_total_canonical n k
    simp [SmtEval.native_and, hNonneg, hMod, native_ite]
  simpa [native_ite, hNonneg] using
    TranslationProofs.smtx_typeof_binary_of_non_none n
      (native_mod_total k (native_int_pow2 n)) hNN

private theorem eval_bv_const
    (M : SmtModel) (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
      SmtValue.Binary n (native_mod_total k (native_int_pow2 n)) := by
  intro hNonneg
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral k)) =
    SmtValue.Binary n (native_mod_total k (native_int_pow2 n))
  simp [native_ite, hNonneg]

private theorem smt_typeof_bvurem_self_eq_zero (x : Term) (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x)) =
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))) := by
  intro hNonneg hXSmtTy
  have hZeroTy := smt_typeof_bv_const 0 n hNonneg
  change __smtx_typeof (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt x)) =
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
  have hLhsTy :
      __smtx_typeof (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat n) := by
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_2, hXSmtTy, native_nateq, native_ite]
  rw [hLhsTy, hZeroTy]

private theorem eval_bvurem_self_eq_zero
    (M : SmtModel) (hM : model_wf M) (x : Term) (n : native_Int) :
    RuleProofs.eo_has_smt_translation x ->
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))) := by
  intro hXTrans hNonneg hXSmtTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hXTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX⟩
  have hWidthEq : native_nat_to_int (native_int_to_nat n) = n := by
    have hnNonneg : 0 <= n := by
      simpa [SmtEval.native_zleq] using hNonneg
    have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
      Int.toNat_of_nonneg hnNonneg
    simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  rw [hWidthEq] at hEvalX
  have hZeroEval := eval_bv_const M 0 n hNonneg
  change __smtx_model_eval M
      (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt x)) =
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))
  rw [show __smtx_model_eval M
        (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt x)) =
      __smtx_model_eval_bvurem
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt x)) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  rw [hEvalX, hZeroEval]
  by_cases hp : payload = 0
  · subst hp
    simp [__smtx_model_eval_bvurem, SmtEval.native_mod_total,
      SmtEval.native_zeq, native_ite]
  · simp [__smtx_model_eval_bvurem, SmtEval.native_mod_total,
      SmtEval.native_zeq, native_ite, hp, Int.emod_self]

private theorem typed_bv_urem_self_body (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    w ≠ Term.Stuck ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x))
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x))
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) := by
  intro hXTrans hW hTy
  rcases typeof_args_of_urem_self_body_bool x w hW hTy with ⟨u, hXType, hWU⟩
  subst hWU
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x w hXTrans hXType with
    ⟨n, hU, hNonneg, hXSmtTy⟩
  subst hU
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (smt_typeof_bvurem_self_eq_zero x n hNonneg hXSmtTy)
    (by
      rw [smt_typeof_bvurem_self_eq_zero x n hNonneg hXSmtTy,
        smt_typeof_bv_const 0 n hNonneg]
      simp)

private theorem facts_bv_urem_self_body
    (M : SmtModel) (hM : model_wf M) (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    w ≠ Term.Stuck ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x))
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) = Term.Bool ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x))
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) true := by
  intro hXTrans hW hTy
  rcases typeof_args_of_urem_self_body_bool x w hW hTy with ⟨u, hXType, hWU⟩
  subst hWU
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x w hXTrans hXType with
    ⟨n, hU, hNonneg, hXSmtTy⟩
  subst hU
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact typed_bv_urem_self_body x (Term.Numeral n) hXTrans (by
      intro h
      cases h) hTy
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))
    rw [eval_bvurem_self_eq_zero M hM x n hXTrans hNonneg hXSmtTy]
    exact RuleProofs.smt_value_rel_refl _

private theorem trusted_bv_urem_self_canonical_properties
    (M : SmtModel) (hM : model_wf M) (x w : Term) :
    cArgListTranslationOk (CArgList.cons x (CArgList.cons w CArgList.nil)) ->
    __eo_typeof
        (__eo_prog_bv_urem_self x w
          (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
            (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) = Term.Bool ->
    StepRuleProperties M
      [Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)]
      (__eo_prog_bv_urem_self x w
        (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) := by
  intro hArgsTrans hResultTy
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [cArgListTranslationOk, eoHasSmtTranslation,
      RuleProofs.eo_has_smt_translation] using hArgsTrans.1
  have hWTrans : RuleProofs.eo_has_smt_translation w := by
    simpa [cArgListTranslationOk, eoHasSmtTranslation,
      RuleProofs.eo_has_smt_translation] using hArgsTrans.2.1
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hwNe : w ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  have hProgEq := prog_bv_urem_self_canonical_eq_of_ne_stuck x w hxNe hwNe
  have hBodyTy :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) x))
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  refine ⟨?_, ?_⟩
  · intro _hPrem
    exact facts_bv_urem_self_body M hM x w hXTrans hwNe hBodyTy
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (typed_bv_urem_self_body x w hXTrans hwNe hBodyTy)

public theorem cmd_step_bv_urem_self_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_urem_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_urem_self args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_urem_self args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_urem_self args premises ≠ Term.Stuck :=
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
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      let P1 := __eo_state_proven_nth s n1
                      change StepRuleProperties M [P1]
                        (__eo_prog_bv_urem_self a1 a2 (Proof.pf P1))
                      have hProgLocal :
                          __eo_prog_bv_urem_self a1 a2 (Proof.pf P1) ≠
                            Term.Stuck := by
                        exact hProg
                      rcases bv_urem_self_shape_of_ne_stuck a1 a2 P1 hProgLocal with
                        ⟨ha1, ha2, pw, px, hP1⟩
                      subst P1
                      have hReqNe := by
                        have h := hProgLocal
                        rw [hP1] at h
                        rw [__eo_prog_bv_urem_self.eq_3 a1 a2 pw px ha1 ha2] at h
                        exact h
                      rcases bv_urem_self_guard_eqs_of_ne_stuck hReqNe with
                        ⟨hpw, hpx⟩
                      subst pw
                      subst px
                      have hArgsTrans :
                          cArgListTranslationOk
                            (CArgList.cons a1 (CArgList.cons a2 CArgList.nil)) := by
                        simpa [cmdTranslationOk] using hCmdTrans
                      have hResultTyCanonical :
                          __eo_typeof
                              (__eo_prog_bv_urem_self a1 a2
                                (Proof.pf
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a2)
                                    (Term.Apply (Term.UOp UserOp._at_bvsize) a1)))) =
                            Term.Bool := by
                        have h := hResultTy
                        change __eo_typeof
                            (__eo_prog_bv_urem_self a1 a2
                              (Proof.pf (__eo_state_proven_nth s n1))) =
                          Term.Bool at h
                        simpa [hP1] using h
                      simpa [hP1] using
                        trusted_bv_urem_self_canonical_properties M hM a1 a2
                          hArgsTrans hResultTyCanonical
