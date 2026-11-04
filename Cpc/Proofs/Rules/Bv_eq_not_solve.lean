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
  cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢
  all_goals simpa using h

private theorem prog_bv_eq_not_solve_eq_of_ne_stuck (x y : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_prog_bv_eq_not_solve x y =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.Apply (Term.UOp UserOp.bvnot) y))))
        (Term.Boolean true) := by
  intro hx hy
  exact __eo_prog_bv_eq_not_solve.eq_3 x y hx hy

private theorem typeof_eq_operands_eq_of_ne_stuck {P Q : Term}
    (hP : P ≠ Term.Stuck) (hQ : Q ≠ Term.Stuck) :
    __eo_typeof_eq P Q ≠ Term.Stuck ->
    Q = P := by
  intro hNe
  rw [__eo_typeof_eq.eq_3 P Q hP hQ] at hNe
  exact eo_eq_true_eq (eo_requires_arg_eq_of_ne_stuck hNe)

private theorem typeof_bvnot_ne_stuck_inv :
    (A : Term) ->
    __eo_typeof_bvnot A ≠ Term.Stuck ->
    ∃ m, A = Term.Apply (Term.UOp UserOp.BitVec) m
  | A, hNe => by
      cases A <;> try simp [__eo_typeof_bvnot] at hNe
      case Apply f a =>
        cases f <;> try simp [__eo_typeof_bvnot] at hNe
        case UOp op =>
          cases op <;> try simp [__eo_typeof_bvnot] at hNe
          case BitVec =>
            exact ⟨a, rfl⟩

private theorem typeof_args_of_eq_not_solve_body_bool (x y : Term) :
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp UserOp.bvnot) y))))
          (Term.Boolean true)) = Term.Bool ->
    ∃ u, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) u ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) u := by
  intro hTy
  change __eo_typeof_eq
      (__eo_typeof_eq
        (__eo_typeof_eq (__eo_typeof_bvnot (__eo_typeof x)) (__eo_typeof y))
        (__eo_typeof_eq (__eo_typeof x) (__eo_typeof_bvnot (__eo_typeof y))))
      Term.Bool =
    Term.Bool at hTy
  have hInner :
      __eo_typeof_eq
          (__eo_typeof_eq (__eo_typeof_bvnot (__eo_typeof x)) (__eo_typeof y))
          (__eo_typeof_eq (__eo_typeof x) (__eo_typeof_bvnot (__eo_typeof y))) =
        Term.Bool :=
    support_eo_typeof_eq_bool_operands_eq _ _ hTy
  have hANe :
      __eo_typeof_eq (__eo_typeof_bvnot (__eo_typeof x)) (__eo_typeof y) ≠
        Term.Stuck := by
    intro h
    rw [h] at hInner
    simp [__eo_typeof_eq] at hInner
  have hPNe : __eo_typeof_bvnot (__eo_typeof x) ≠ Term.Stuck := by
    intro h
    apply hANe
    rw [h]
    simp [__eo_typeof_eq]
  have hQNe : __eo_typeof y ≠ Term.Stuck := by
    intro h
    apply hANe
    rw [h]
    cases hP : __eo_typeof_bvnot (__eo_typeof x) <;>
      simp [__eo_typeof_eq]
  rcases typeof_bvnot_ne_stuck_inv _ hPNe with ⟨u, hXTy⟩
  have hPVal :
      __eo_typeof_bvnot (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec) u := by
    rw [hXTy]
    simp [__eo_typeof_bvnot]
  have hYP : __eo_typeof y = __eo_typeof_bvnot (__eo_typeof x) :=
    typeof_eq_operands_eq_of_ne_stuck hPNe hQNe hANe
  exact ⟨u, hXTy, hYP.trans hPVal⟩

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

private theorem eo_to_smt_eq_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
      SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_bvnot_term (a : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) a) =
      SmtTerm.bvnot (__eo_to_smt a) := by
  rfl

private theorem smt_typeof_eq_same_non_none
    (a b : SmtTerm) (T : SmtType) :
    __smtx_typeof a = T ->
    __smtx_typeof b = T ->
    T ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.eq a b) = SmtType.Bool := by
  intro ha hb hT
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [ha, hb]
  cases T <;>
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_Teq,
      native_ite] at hT ⊢

private theorem smt_typeof_boolean (b : Bool) :
    __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smt_typeof_bvnot
    (a : SmtTerm) (n : native_Int) :
    __smtx_typeof a = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (SmtTerm.bvnot a) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro ha
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_1, ha]

private theorem smt_typeof_eq_not_solve_lhs_bool (x y : Term) (n : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp UserOp.bvnot) y)))) =
      SmtType.Bool := by
  intro hX hY
  rw [eo_to_smt_eq_term, eo_to_smt_eq_term, eo_to_smt_eq_term,
    eo_to_smt_bvnot_term, eo_to_smt_bvnot_term]
  apply smt_typeof_eq_same_non_none _ _ SmtType.Bool
  · exact smt_typeof_eq_same_non_none _ _
      (SmtType.BitVec (native_int_to_nat n))
      (smt_typeof_bvnot _ n hX) hY (by intro h; cases h)
  · exact smt_typeof_eq_same_non_none _ _
      (SmtType.BitVec (native_int_to_nat n))
      hX (smt_typeof_bvnot _ n hY) (by intro h; cases h)
  · intro h
    cases h

private theorem eval_smt_eq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) =
      __smtx_model_eval_eq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_bvnot (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvnot a) =
      __smtx_model_eval_bvnot (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_boolean (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem int_not_eq (P a : Int) : P + -(a + 1) = P - 1 - a := by
  omega

private theorem int_sub_lo (P a : Int) (h : a < P) : 0 <= P - 1 - a := by
  omega

private theorem int_sub_hi (P a : Int) (h : 0 <= a) : P - 1 - a < P := by
  omega

private theorem int_flip {P a b : Int} (h : P - 1 - a = b) :
    P - 1 - b = a := by
  omega

private theorem int_flip_neg {P a b : Int} (h : ¬ P - 1 - a = b) :
    ¬ a = P - 1 - b := by
  omega

private theorem eval_bv_eq_not_solve_lhs
    (M : SmtModel) (hM : model_wf M) (x y : Term) (n : native_Int) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp UserOp.bvnot) y)))) =
      SmtValue.Boolean true := by
  intro hXTrans hYTrans hNonneg hXSmtTy hYSmtTy
  have hWidthEq : native_nat_to_int (native_int_to_nat n) = n := by
    have hnNonneg : 0 <= n := by
      simpa [SmtEval.native_zleq] using hNonneg
    have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
      Int.toNat_of_nonneg hnNonneg
    simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  have hEvalTyX :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hXTrans)
  have hEvalTyY :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hYTrans)
  rcases bitvec_value_canonical hEvalTyX with ⟨px, hEvalX⟩
  rcases bitvec_value_canonical hEvalTyY with ⟨py, hEvalY⟩
  rw [hWidthEq] at hEvalX hEvalY
  have hEvalTyXN :
      __smtx_typeof_value (SmtValue.Binary n px) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hEvalX] using hEvalTyX
  have hEvalTyYN :
      __smtx_typeof_value (SmtValue.Binary n py) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hEvalY] using hEvalTyY
  have hPxCanon :
      native_zeq px (native_mod_total px (native_int_pow2 n)) = true :=
    bitvec_payload_canonical hEvalTyXN
  have hPyCanon :
      native_zeq py (native_mod_total py (native_int_pow2 n)) = true :=
    bitvec_payload_canonical hEvalTyYN
  have hPxRange := bitvec_payload_range_of_canonical hNonneg hPxCanon
  have hPyRange := bitvec_payload_range_of_canonical hNonneg hPyCanon
  have hNotPx :
      native_mod_total (native_binary_not n px) (native_int_pow2 n) =
        native_int_pow2 n - 1 - px := by
    have h1 : native_binary_not n px = native_int_pow2 n - 1 - px := by
      show native_int_pow2 n + -(px + 1) = native_int_pow2 n - 1 - px
      exact int_not_eq _ _
    rw [h1]
    have hLo : 0 <= native_int_pow2 n - 1 - px :=
      int_sub_lo _ _ hPxRange.2
    have hHi : native_int_pow2 n - 1 - px < native_int_pow2 n :=
      int_sub_hi _ _ hPxRange.1
    simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hLo hHi
  have hNotPy :
      native_mod_total (native_binary_not n py) (native_int_pow2 n) =
        native_int_pow2 n - 1 - py := by
    have h1 : native_binary_not n py = native_int_pow2 n - 1 - py := by
      show native_int_pow2 n + -(py + 1) = native_int_pow2 n - 1 - py
      exact int_not_eq _ _
    rw [h1]
    have hLo : 0 <= native_int_pow2 n - 1 - py :=
      int_sub_lo _ _ hPyRange.2
    have hHi : native_int_pow2 n - 1 - py < native_int_pow2 n :=
      int_sub_hi _ _ hPyRange.1
    simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hLo hHi
  rw [eo_to_smt_eq_term, eo_to_smt_eq_term, eo_to_smt_eq_term,
    eo_to_smt_bvnot_term, eo_to_smt_bvnot_term]
  rw [eval_smt_eq, eval_smt_eq, eval_smt_eq, eval_smt_bvnot,
    eval_smt_bvnot, hEvalX, hEvalY]
  simp only [__smtx_model_eval_bvnot]
  rw [hNotPx, hNotPy]
  by_cases hp : native_int_pow2 n - 1 - px = py
  · have hq : native_int_pow2 n - 1 - py = px := int_flip hp
    simp [__smtx_model_eval_eq, native_veq, hp, hq]
  · have hq : ¬ px = native_int_pow2 n - 1 - py := int_flip_neg hp
    simp [__smtx_model_eval_eq, native_veq, hp, hq]

private theorem typed_bv_eq_not_solve_body (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp UserOp.bvnot) y))))
          (Term.Boolean true)) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.Apply (Term.UOp UserOp.bvnot) y))))
        (Term.Boolean true)) := by
  intro hXTrans hYTrans hTy
  rcases typeof_args_of_eq_not_solve_body_bool x y hTy with ⟨u, hXType, hYType⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x u hXTrans hXType with
    ⟨n, hU, hNonneg, hXSmtTy⟩
  subst hU
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y (Term.Numeral n)
      hYTrans hYType with
    ⟨ny, hNy, _hYNonneg, hYSmtTy⟩
  cases hNy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by
      rw [smt_typeof_eq_not_solve_lhs_bool x y n hXSmtTy hYSmtTy]
      rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true from rfl]
      rw [smt_typeof_boolean true])
    (by
      rw [smt_typeof_eq_not_solve_lhs_bool x y n hXSmtTy hYSmtTy]
      intro h
      cases h)

private theorem facts_bv_eq_not_solve_body
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp UserOp.bvnot) y))))
          (Term.Boolean true)) = Term.Bool ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.Apply (Term.UOp UserOp.bvnot) y))))
        (Term.Boolean true)) true := by
  intro hXTrans hYTrans hTy
  have hTyped := typed_bv_eq_not_solve_body x y hXTrans hYTrans hTy
  rcases typeof_args_of_eq_not_solve_body_bool x y hTy with ⟨u, hXType, hYType⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x u hXTrans hXType with
    ⟨n, hU, hNonneg, hXSmtTy⟩
  subst hU
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y (Term.Numeral n)
      hYTrans hYType with
    ⟨ny, hNy, _hYNonneg, hYSmtTy⟩
  cases hNy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hTyped
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) x)) y))
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp UserOp.bvnot) y)))))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean true)))
    rw [eval_bv_eq_not_solve_lhs M hM x y n hXTrans hYTrans hNonneg
      hXSmtTy hYSmtTy]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true from rfl]
    rw [eval_smt_boolean]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_eq_not_solve_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_eq_not_solve args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_eq_not_solve args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_eq_not_solve args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_eq_not_solve args premises ≠ Term.Stuck :=
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
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  have hA1Ne : a1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                  have hA2Ne : a2 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                  have hProgEq := prog_bv_eq_not_solve_eq_of_ne_stuck a1 a2 hA1Ne hA2Ne
                  change __eo_typeof (__eo_prog_bv_eq_not_solve a1 a2) = Term.Bool
                    at hResultTy
                  have hBodyTy :
                      __eo_typeof
                          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                              (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                                (Term.Apply (Term.UOp UserOp.bvnot) a1)) a2))
                              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a1)
                                (Term.Apply (Term.UOp UserOp.bvnot) a2))))
                            (Term.Boolean true)) = Term.Bool := by
                    simpa [hProgEq] using hResultTy
                  change StepRuleProperties M []
                    (__eo_prog_bv_eq_not_solve a1 a2)
                  rw [hProgEq]
                  refine ⟨?_, ?_⟩
                  · intro _hPrem
                    exact facts_bv_eq_not_solve_body M hM a1 a2
                      hA1Trans hA2Trans hBodyTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed_bv_eq_not_solve_body a1 a2 hA1Trans hA2Trans hBodyTy)
