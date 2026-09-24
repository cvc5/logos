module

public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def smtValuePos : SmtValue -> Prop
  | SmtValue.Numeral n => 0 < n
  | SmtValue.Rational q => 0 < q
  | _ => False

private def smtValueNeg : SmtValue -> Prop
  | SmtValue.Numeral n => n < 0
  | SmtValue.Rational q => q < 0
  | _ => False

private def smtValueNonzero : SmtValue -> Prop
  | SmtValue.Numeral n => n ≠ 0
  | SmtValue.Rational q => q ≠ 0
  | _ => False

private theorem rat_mul_pos_of_neg_neg {a b : Rat} (ha : a < 0) (hb : b < 0) :
    0 < a * b := by
  have hna : 0 < -a := (Rat.lt_neg_iff (a := 0) (b := a)).mpr (by simpa using ha)
  have hnb : 0 < -b := (Rat.lt_neg_iff (a := 0) (b := b)).mpr (by simpa using hb)
  have hpos : 0 < (-a) * (-b) := (Rat.mul_pos_iff_of_pos_left hna).mpr hnb
  simpa [Rat.neg_mul, Rat.mul_neg] using hpos

private theorem smtValuePos_mult_pos_pos
    {v1 v2 : SmtValue}
    (h1 : smtValuePos v1) (h2 : smtValuePos v2)
    (hTy : __smtx_typeof_value v1 = __smtx_typeof_value v2) :
    smtValuePos (__smtx_model_eval_mult v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [smtValuePos, __smtx_typeof_value, __smtx_model_eval_mult] at h1 h2 hTy ⊢
  · exact Int.mul_pos h1 h2
  · exact (Rat.mul_pos_iff_of_pos_left h1).mpr h2

private theorem smtValueNeg_mult_pos_neg
    {v1 v2 : SmtValue}
    (h1 : smtValuePos v1) (h2 : smtValueNeg v2)
    (hTy : __smtx_typeof_value v1 = __smtx_typeof_value v2) :
    smtValueNeg (__smtx_model_eval_mult v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [smtValuePos, smtValueNeg, __smtx_typeof_value, __smtx_model_eval_mult] at h1 h2 hTy ⊢
  · exact Int.mul_neg_of_pos_of_neg h1 h2
  · exact (Rat.mul_neg_iff_of_pos_left h1).mpr h2

private theorem smtValueNeg_mult_neg_pos
    {v1 v2 : SmtValue}
    (h1 : smtValueNeg v1) (h2 : smtValuePos v2)
    (hTy : __smtx_typeof_value v1 = __smtx_typeof_value v2) :
    smtValueNeg (__smtx_model_eval_mult v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [smtValuePos, smtValueNeg, __smtx_typeof_value, __smtx_model_eval_mult] at h1 h2 hTy ⊢
  · exact Int.mul_neg_of_neg_of_pos h1 h2
  · exact (Rat.mul_neg_iff_of_pos_right h2).mpr h1

private theorem smtValuePos_mult_neg_neg
    {v1 v2 : SmtValue}
    (h1 : smtValueNeg v1) (h2 : smtValueNeg v2)
    (hTy : __smtx_typeof_value v1 = __smtx_typeof_value v2) :
    smtValuePos (__smtx_model_eval_mult v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [smtValuePos, smtValueNeg, __smtx_typeof_value, __smtx_model_eval_mult] at h1 h2 hTy ⊢
  · exact Int.mul_pos_of_neg_of_neg h1 h2
  · exact rat_mul_pos_of_neg_neg h1 h2

private theorem smtValueNonzero_of_pos {v : SmtValue} :
    smtValuePos v -> smtValueNonzero v := by
  cases v with
  | Numeral n =>
      simp [smtValuePos, smtValueNonzero]
      intro h
      exact Int.ne_of_gt h
  | Rational q =>
      simp [smtValuePos, smtValueNonzero]
      intro h hz
      exact Rat.ne_of_gt h hz
  | _ => simp [smtValuePos]

private theorem smtValueNonzero_of_neg {v : SmtValue} :
    smtValueNeg v -> smtValueNonzero v := by
  cases v with
  | Numeral n =>
      simp [smtValueNeg, smtValueNonzero]
      intro h
      exact Int.ne_of_lt h
  | Rational q =>
      simp [smtValueNeg, smtValueNonzero]
      intro h hz
      exact Rat.ne_of_lt h hz
  | _ => simp [smtValueNeg]

private theorem smtValue_pos_or_neg_of_nonzero {v : SmtValue} :
    smtValueNonzero v -> smtValuePos v ∨ smtValueNeg v := by
  cases v with
  | Numeral n =>
      simp [smtValueNonzero, smtValuePos, smtValueNeg]
      intro hn
      rcases Int.lt_or_gt_of_ne hn with hneg | hpos
      · exact Or.inr hneg
      · exact Or.inl hpos
  | Rational q =>
      simp [smtValueNonzero, smtValuePos, smtValueNeg]
      intro hq
      by_cases hpos : 0 < q
      · exact Or.inl hpos
      · have hle : q ≤ 0 := (Rat.not_lt (a := (0 : Rat)) (b := q)).mp hpos
        rcases Rat.le_iff_lt_or_eq.mp hle with hneg | hzero
        · exact Or.inr hneg
        · exact False.elim (hq hzero)
  | _ => simp [smtValueNonzero]

private theorem numeral_zero_of_to_real_zero {n : native_Int} :
    native_to_real n = native_mk_rational 0 1 -> n = 0 := by
  intro h
  have h' : ((n : Rat) / (1 : Rat)) = ((0 : Rat) / (1 : Rat)) := by
    simpa [native_to_real, native_mk_rational] using h
  rw [rat_div_one_intCast n, rat_zero_div_one] at h'
  exact Rat.intCast_inj.mp h'

private theorem term_zero_shape_of_to_q_zero (z : Term) :
    __eo_to_q z = Term.Rational (native_mk_rational 0 1) ->
    z = Term.Numeral 0 ∨ z = Term.Rational (native_mk_rational 0 1) := by
  intro h
  cases z <;> simp [__eo_to_q] at h
  case Numeral n =>
    left
    have hn : n = 0 := numeral_zero_of_to_real_zero h
    simp [hn]
  case Rational q =>
    right
    simp [h]

private theorem numeral_one_of_to_real_one {n : native_Int} :
    native_to_real n = native_mk_rational 1 1 -> n = 1 := by
  intro h
  have h' : ((n : Rat) / (1 : Rat)) = ((1 : Rat) / (1 : Rat)) := by
    simpa [native_to_real, native_mk_rational] using h
  rw [rat_div_one_intCast n] at h'
  have hOneDiv : ((1 : Rat) / (1 : Rat)) = (1 : Rat) := by
    change (((1 : Int) : Rat) / ((1 : Int) : Rat)) = ((1 : Int) : Rat)
    exact rat_div_one_intCast 1
  rw [hOneDiv] at h'
  exact Rat.intCast_inj.mp h'

private theorem term_one_shape_of_to_q_one (one : Term) :
    __eo_to_q one = Term.Rational (native_mk_rational 1 1) ->
    one = Term.Numeral 1 ∨ one = Term.Rational (native_mk_rational 1 1) := by
  intro h
  cases one <;> simp [__eo_to_q] at h
  case Numeral n =>
    left
    have hn : n = 1 := numeral_one_of_to_real_one h
    simp [hn]
  case Rational q =>
    right
    simp [h]

private theorem smtValuePos_of_one_term
    (M : SmtModel) (one : Term)
    (hOne : __eo_to_q one = Term.Rational (native_mk_rational 1 1)) :
    smtValuePos (__smtx_model_eval M (__eo_to_smt one)) := by
  rcases term_one_shape_of_to_q_one one hOne with h | h
  · subst one
    change smtValuePos (__smtx_model_eval M (SmtTerm.Numeral 1))
    rw [__smtx_model_eval.eq_2]
    simp [smtValuePos]
  · subst one
    change smtValuePos (__smtx_model_eval M (SmtTerm.Rational (native_mk_rational 1 1)))
    rw [__smtx_model_eval.eq_3]
    simp [smtValuePos, native_mk_rational_one]
    native_decide

private theorem requires_rational_bool_result {x r : Term} {q : Rat} {out : Bool} :
    __eo_requires x (Term.Rational q) r = Term.Boolean out ->
      x = Term.Rational q ∧ r = Term.Boolean out := by
  intro h
  cases x <;> simp [__eo_requires, native_ite, native_teq, native_not] at h ⊢
  case Rational q' =>
    by_cases hq : q' = q
    · subst q'
      simp at h
      exact ⟨rfl, h⟩
    · simp [hq] at h

private theorem smtValuePos_of_gt_zero
    (M : SmtModel) (t z : Term)
    (hZ : __eo_to_q z = Term.Rational (native_mk_rational 0 1))
    (hGt : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) z) true) :
    smtValuePos (__smtx_model_eval M (__eo_to_smt t)) := by
  rcases term_zero_shape_of_to_q_zero z hZ with hz | hz
  · subst z
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hGt
    change smt_interprets M (SmtTerm.gt (__eo_to_smt t) (SmtTerm.Numeral 0)) true at hGt
    cases hGt with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_19, __smtx_model_eval.eq_2] at hEval
        cases hv : __smtx_model_eval M (__eo_to_smt t) <;>
          simp [smtValuePos, hv, __smtx_model_eval_gt, __smtx_model_eval_lt,
            native_zlt, SmtEval.native_zlt] at hEval ⊢
        exact hEval
  · subst z
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hGt
    change smt_interprets M
      (SmtTerm.gt (__eo_to_smt t) (SmtTerm.Rational (native_mk_rational 0 1))) true at hGt
    cases hGt with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_19, __smtx_model_eval.eq_3] at hEval
        cases hv : __smtx_model_eval M (__eo_to_smt t) <;>
          simp [smtValuePos, hv, __smtx_model_eval_gt, __smtx_model_eval_lt,
            native_qlt, SmtEval.native_qlt, native_mk_rational_zero] at hEval ⊢
        exact hEval

private theorem smtValueNeg_of_lt_zero
    (M : SmtModel) (t z : Term)
    (hZ : __eo_to_q z = Term.Rational (native_mk_rational 0 1))
    (hLt : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) z) true) :
    smtValueNeg (__smtx_model_eval M (__eo_to_smt t)) := by
  rcases term_zero_shape_of_to_q_zero z hZ with hz | hz
  · subst z
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hLt
    change smt_interprets M (SmtTerm.lt (__eo_to_smt t) (SmtTerm.Numeral 0)) true at hLt
    cases hLt with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_17, __smtx_model_eval.eq_2] at hEval
        cases hv : __smtx_model_eval M (__eo_to_smt t) <;>
          simp [smtValueNeg, hv, __smtx_model_eval_lt,
            native_zlt, SmtEval.native_zlt] at hEval ⊢
        exact hEval
  · subst z
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hLt
    change smt_interprets M
      (SmtTerm.lt (__eo_to_smt t) (SmtTerm.Rational (native_mk_rational 0 1))) true at hLt
    cases hLt with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_17, __smtx_model_eval.eq_3] at hEval
        cases hv : __smtx_model_eval M (__eo_to_smt t) <;>
          simp [smtValueNeg, hv, __smtx_model_eval_lt,
            native_qlt, SmtEval.native_qlt, native_mk_rational_zero] at hEval ⊢
        exact hEval

private theorem smtValueNonzero_of_not_eq_zero
    (M : SmtModel) (hM : model_wf M) (t z : Term)
    (hZ : __eo_to_q z = Term.Rational (native_mk_rational 0 1))
    (hNe : eo_interprets M
      (Term.Apply (Term.UOp UserOp.not) (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) z))
      true) :
    smtValueNonzero (__smtx_model_eval M (__eo_to_smt t)) := by
  rcases term_zero_shape_of_to_q_zero z hZ with hz | hz
  · subst z
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hNe
    change smt_interprets M
      (SmtTerm.not (SmtTerm.eq (__eo_to_smt t) (SmtTerm.Numeral 0))) true at hNe
    cases hNe with
    | intro_true hTyNot hEval =>
        have hEqBool : __smtx_typeof (SmtTerm.eq (__eo_to_smt t) (SmtTerm.Numeral 0)) =
            SmtType.Bool := by
          rw [typeof_not_eq] at hTyNot
          by_cases hEqTy :
              __smtx_typeof (SmtTerm.eq (__eo_to_smt t) (SmtTerm.Numeral 0)) =
                SmtType.Bool
          · exact hEqTy
          · simp [hEqTy, native_ite, native_Teq] at hTyNot
        have hEqBool' : __smtx_typeof_eq (__smtx_typeof (__eo_to_smt t)) SmtType.Int =
            SmtType.Bool := by
          have h := hEqBool
          rw [typeof_eq_eq] at h
          simpa [__smtx_typeof] using h
        have hTType : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
          (RuleProofs.smtx_typeof_eq_bool_iff
            (__smtx_typeof (__eo_to_smt t)) SmtType.Int).mp hEqBool' |>.1
        have hEvalTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
          simpa [hTType] using Smtm.smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt t) (by simp [term_has_non_none_type, hTType])
        rcases int_value_canonical hEvalTy with ⟨n, hn⟩
        rw [hn]
        rw [__smtx_model_eval.eq_7, smtx_eval_eq_term_eq, __smtx_model_eval.eq_2,
          hn] at hEval
        simp [smtValueNonzero, __smtx_model_eval_not, __smtx_model_eval_eq,
          native_veq, SmtEval.native_not] at hEval ⊢
        exact hEval
  · subst z
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hNe
    change smt_interprets M
      (SmtTerm.not
        (SmtTerm.eq (__eo_to_smt t) (SmtTerm.Rational (native_mk_rational 0 1))))
      true at hNe
    cases hNe with
    | intro_true hTyNot hEval =>
        have hEqBool : __smtx_typeof
            (SmtTerm.eq (__eo_to_smt t) (SmtTerm.Rational (native_mk_rational 0 1))) =
            SmtType.Bool := by
          rw [typeof_not_eq] at hTyNot
          by_cases hEqTy : __smtx_typeof
              (SmtTerm.eq (__eo_to_smt t) (SmtTerm.Rational (native_mk_rational 0 1))) =
              SmtType.Bool
          · exact hEqTy
          · simp [hEqTy, native_ite, native_Teq] at hTyNot
        have hEqBool' : __smtx_typeof_eq (__smtx_typeof (__eo_to_smt t)) SmtType.Real =
            SmtType.Bool := by
          have h := hEqBool
          rw [typeof_eq_eq] at h
          simpa [__smtx_typeof] using h
        have hTType : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
          (RuleProofs.smtx_typeof_eq_bool_iff
            (__smtx_typeof (__eo_to_smt t)) SmtType.Real).mp hEqBool' |>.1
        have hEvalTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
              SmtType.Real := by
          simpa [hTType] using Smtm.smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt t) (by simp [term_has_non_none_type, hTType])
        rcases real_value_canonical hEvalTy with ⟨q, hqv⟩
        rw [hqv]
        rw [__smtx_model_eval.eq_7, smtx_eval_eq_term_eq, __smtx_model_eval.eq_3,
          hqv] at hEval
        simp [smtValueNonzero, __smtx_model_eval_not, __smtx_model_eval_eq,
          native_veq, SmtEval.native_not, native_mk_rational_zero] at hEval ⊢
        exact hEval

private theorem mult_operands_non_none_and_eval_type_eq
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
    __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ∧
    __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) := by
  have hTerm : term_has_non_none_type (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    simpa [eo_to_smt_mult_eq] using hNN
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt x) (__eo_to_smt y)) hTerm with hArgs | hArgs
  · have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by simp [hArgs.1]
    have hyNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by simp [hArgs.2]
    have hxEval := Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hxNN
    have hyEval := Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) hyNN
    exact ⟨hxNN, hyNN, by
      calc
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
            __smtx_typeof (__eo_to_smt x) := hxEval
        _ = __smtx_typeof (__eo_to_smt y) := hArgs.1.trans hArgs.2.symm
        _ = __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) := hyEval.symm⟩
  · have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by simp [hArgs.1]
    have hyNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by simp [hArgs.2]
    have hxEval := Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hxNN
    have hyEval := Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) hyNN
    exact ⟨hxNN, hyNN, by
      calc
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
            __smtx_typeof (__eo_to_smt x) := hxEval
        _ = __smtx_typeof (__eo_to_smt y) := hArgs.1.trans hArgs.2.symm
        _ = __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) := hyEval.symm⟩

private theorem mult_operands_non_none
    (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
  have hTerm : term_has_non_none_type (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    simpa [eo_to_smt_mult_eq] using hNN
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt x) (__eo_to_smt y)) hTerm with hArgs | hArgs
  · exact ⟨by simp [hArgs.1], by simp [hArgs.2]⟩
  · exact ⟨by simp [hArgs.1], by simp [hArgs.2]⟩

private theorem eval_mult_pos_pos
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None)
    (hx : smtValuePos (__smtx_model_eval M (__eo_to_smt x)))
    (hy : smtValuePos (__smtx_model_eval M (__eo_to_smt y))) :
    smtValuePos
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y))) := by
  rcases mult_operands_non_none_and_eval_type_eq M hM x y hNN with ⟨_, _, hTy⟩
  rw [eo_to_smt_mult_eq, __smtx_model_eval.eq_16]
  exact smtValuePos_mult_pos_pos hx hy hTy

private theorem eval_mult_pos_neg
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None)
    (hx : smtValuePos (__smtx_model_eval M (__eo_to_smt x)))
    (hy : smtValueNeg (__smtx_model_eval M (__eo_to_smt y))) :
    smtValueNeg
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y))) := by
  rcases mult_operands_non_none_and_eval_type_eq M hM x y hNN with ⟨_, _, hTy⟩
  rw [eo_to_smt_mult_eq, __smtx_model_eval.eq_16]
  exact smtValueNeg_mult_pos_neg hx hy hTy

private theorem eval_mult_neg_pos
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None)
    (hx : smtValueNeg (__smtx_model_eval M (__eo_to_smt x)))
    (hy : smtValuePos (__smtx_model_eval M (__eo_to_smt y))) :
    smtValueNeg
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y))) := by
  rcases mult_operands_non_none_and_eval_type_eq M hM x y hNN with ⟨_, _, hTy⟩
  rw [eo_to_smt_mult_eq, __smtx_model_eval.eq_16]
  exact smtValueNeg_mult_neg_pos hx hy hTy

private theorem eval_mult_neg_neg
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None)
    (hx : smtValueNeg (__smtx_model_eval M (__eo_to_smt x)))
    (hy : smtValueNeg (__smtx_model_eval M (__eo_to_smt y))) :
    smtValuePos
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y))) := by
  rcases mult_operands_non_none_and_eval_type_eq M hM x y hNN with ⟨_, _, hTy⟩
  rw [eo_to_smt_mult_eq, __smtx_model_eval.eq_16]
  exact smtValuePos_mult_neg_neg hx hy hTy

private def signMatches (M : SmtModel) (acc out : Bool) (m : Term) : Prop :=
  if acc = out then
    smtValuePos (__smtx_model_eval M (__eo_to_smt m))
  else
    smtValueNeg (__smtx_model_eval M (__eo_to_smt m))

private theorem not_signMatches_stuck (M : SmtModel) (acc out : Bool) :
    ¬ signMatches M acc out Term.Stuck := by
  have hEval :
      __smtx_model_eval M (__eo_to_smt Term.Stuck) = SmtValue.NotValue := by
    change __smtx_model_eval M SmtTerm.None = SmtValue.NotValue
    unfold __smtx_model_eval
    rfl
  unfold signMatches
  rw [hEval]
  cases acc <;> cases out <;>
    simp [smtValuePos, smtValueNeg]

private theorem term_eq_of_eo_eq_true {a b : Term} :
    __eo_eq a b = Term.Boolean true -> a = b := by
  intro h
  have hba : b = a := by
    cases a <;> cases b <;> simpa [__eo_eq, native_teq] using h
  exact hba.symm

private theorem eo_eq_pair_true_eq
    {t a b : Term}
    (ht : t ≠ Term.Stuck) (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_and (__eo_eq t a) (__eo_eq t b) = Term.Boolean true -> t = a ∧ t = b := by
  intro h
  unfold __eo_eq at h
  unfold __eo_and at h
  simp [native_teq, native_and] at h
  exact ⟨h.1.symm, h.2.symm⟩

private theorem eo_eq_pair_bool
    {t a b : Term}
    (ht : t ≠ Term.Stuck) (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    ∃ c, __eo_and (__eo_eq t a) (__eo_eq t b) = Term.Boolean c := by
  unfold __eo_eq
  simp [native_teq, __eo_and, native_and]

private theorem signMatches_pos_factor
    (M : SmtModel) (hM : model_wf M) (acc out : Bool) (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None)
    (hx : smtValuePos (__smtx_model_eval M (__eo_to_smt x)))
    (hy : signMatches M acc out y) :
    signMatches M acc out (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) := by
  unfold signMatches at hy ⊢
  by_cases h : acc = out
  · simp [h] at hy ⊢
    exact eval_mult_pos_pos M hM x y hNN hx hy
  · simp [h] at hy ⊢
    exact eval_mult_pos_neg M hM x y hNN hx hy

private theorem signMatches_neg_factor
    (M : SmtModel) (hM : model_wf M) (acc out : Bool) (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None)
    (hx : smtValueNeg (__smtx_model_eval M (__eo_to_smt x)))
    (hy : signMatches M (not acc) out y) :
    signMatches M acc out (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) := by
  unfold signMatches at hy ⊢
  cases acc <;> cases out <;> simp at hy ⊢
  · exact eval_mult_neg_neg M hM x y hNN hx hy
  · exact eval_mult_neg_pos M hM x y hNN hx hy
  · exact eval_mult_neg_pos M hM x y hNN hx hy
  · exact eval_mult_neg_neg M hM x y hNN hx hy

private theorem signMatches_square_factor
    (M : SmtModel) (hM : model_wf M) (acc out : Bool) (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y))) ≠ SmtType.None)
    (hx : smtValueNonzero (__smtx_model_eval M (__eo_to_smt x)))
    (hy : signMatches M acc out y) :
    signMatches M acc out
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) := by
  rcases mult_operands_non_none_and_eval_type_eq M hM x
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) hNN with
    ⟨_, hInnerNN, _⟩
  rcases smtValue_pos_or_neg_of_nonzero hx with hxPos | hxNeg
  · have hInner : signMatches M acc out
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) :=
      signMatches_pos_factor M hM acc out x y hInnerNN hxPos hy
    exact signMatches_pos_factor M hM acc out x
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) hNN hxPos hInner
  · have hFlipInner : signMatches M (not acc) out
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) := by
      unfold signMatches at hy ⊢
      cases acc <;> cases out <;> simp at hy ⊢
      · exact eval_mult_neg_pos M hM x y hInnerNN hxNeg hy
      · exact eval_mult_neg_neg M hM x y hInnerNN hxNeg hy
      · exact eval_mult_neg_neg M hM x y hInnerNN hxNeg hy
      · exact eval_mult_neg_pos M hM x y hInnerNN hxNeg hy
    exact signMatches_neg_factor M hM acc out x
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) hNN hxNeg hFlipInner

private theorem strip_even_exponent_signMatches
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    ∀ (m : Term) (acc out : Bool),
      __smtx_typeof (__eo_to_smt m) ≠ SmtType.None ->
      smtValueNonzero (__smtx_model_eval M (__eo_to_smt t)) ->
      signMatches M acc out (__strip_even_exponent t m) ->
      signMatches M acc out m
  | Term.Stuck, _acc, _out, hNN, _htNZ, _hSign => by
      exfalso
      apply hNN
      change __smtx_typeof SmtTerm.None = SmtType.None
      unfold __smtx_typeof
      rfl
  | Term.Apply (Term.Apply (Term.UOp UserOp.mult) t2)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t3) m), acc, out, hNN, htNZ, hSign => by
      by_cases htStuck : t = Term.Stuck
      · subst t
        have hSt : signMatches M acc out Term.Stuck := by
          simpa [__strip_even_exponent] using hSign
        exfalso
        exact not_signMatches_stuck M acc out hSt
      · rcases mult_operands_non_none_and_eval_type_eq M hM t2
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t3) m) hNN with
          ⟨ht2NN, hTailNN, _⟩
        rcases mult_operands_non_none_and_eval_type_eq M hM t3 m hTailNN with
          ⟨ht3NN, hmNN, _⟩
        have ht2Ne : t2 ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_smt_translation t2 ht2NN
        have ht3Ne : t3 ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_smt_translation t3 ht3NN
        cases hCond : __eo_and (__eo_eq t t2) (__eo_eq t t3) with
        | Boolean b =>
            cases b with
            | true =>
                rcases eo_eq_pair_true_eq htStuck ht2Ne ht3Ne hCond with ⟨rfl, rfl⟩
                have hSub : signMatches M acc out (__strip_even_exponent t m) := by
                  simpa [__strip_even_exponent, __eo_ite, hCond, htStuck, __eo_l_1___strip_even_exponent, native_ite, native_teq] using hSign
                have hmSign : signMatches M acc out m :=
                  strip_even_exponent_signMatches M hM t m acc out hmNN htNZ hSub
                exact signMatches_square_factor M hM acc out t m hNN htNZ hmSign
            | false =>
                simpa [__strip_even_exponent, __eo_ite, __eo_l_1___strip_even_exponent,
                  hCond, htStuck, native_ite, native_teq] using hSign
        | Stuck =>
            have hSt : signMatches M acc out Term.Stuck := by
              simpa [__strip_even_exponent, __eo_ite, hCond, htStuck, __eo_l_1___strip_even_exponent, native_ite, native_teq] using hSign
            exfalso
            exact not_signMatches_stuck M acc out hSt
        | _ =>
            have hSt : signMatches M acc out Term.Stuck := by
              simpa [__strip_even_exponent, __eo_ite, hCond, htStuck, __eo_l_1___strip_even_exponent, native_ite, native_teq] using hSign
            exfalso
            exact not_signMatches_stuck M acc out hSt
  | m, acc, out, _hNN, _htNZ, hSign => by
      cases m <;>
        try
          (by_cases htStuck : t = Term.Stuck
           · subst t
             have hSt : signMatches M acc out Term.Stuck := by
               simpa [__strip_even_exponent] using hSign
             exfalso
             exact not_signMatches_stuck M acc out hSt
           · simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htStuck]
               using hSign)
      case Apply f a =>
        cases f <;>
          try
            (by_cases htStuck : t = Term.Stuck
             · subst t
               have hSt : signMatches M acc out Term.Stuck := by
                 simpa [__strip_even_exponent] using hSign
               exfalso
               exact not_signMatches_stuck M acc out hSt
             · simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htStuck]
                 using hSign)
        case Apply f1 t2 =>
          cases f1 <;>
            try
              (by_cases htStuck : t = Term.Stuck
               · subst t
                 have hSt : signMatches M acc out Term.Stuck := by
                   simpa [__strip_even_exponent] using hSign
                 exfalso
                 exact not_signMatches_stuck M acc out hSt
               · simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htStuck]
                   using hSign)
          case UOp op =>
            cases op <;>
              try
                (by_cases htStuck : t = Term.Stuck
                 · subst t
                   have hSt : signMatches M acc out Term.Stuck := by
                     simpa [__strip_even_exponent] using hSign
                   exfalso
                   exact not_signMatches_stuck M acc out hSt
                 · simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htStuck]
                     using hSign)
            case mult =>
              cases a <;>
                try
                  (by_cases htStuck : t = Term.Stuck
                   · subst t
                     have hSt : signMatches M acc out Term.Stuck := by
                       simpa [__strip_even_exponent] using hSign
                     exfalso
                     exact not_signMatches_stuck M acc out hSt
                   · simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htStuck]
                       using hSign)
              case Apply g m =>
                cases g <;>
                  try
                    (by_cases htStuck : t = Term.Stuck
                     · subst t
                       have hSt : signMatches M acc out Term.Stuck := by
                         simpa [__strip_even_exponent] using hSign
                       exfalso
                       exact not_signMatches_stuck M acc out hSt
                     · simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htStuck]
                         using hSign)
                case Apply g1 t3 =>
                  cases g1 <;>
                    try
                      (by_cases htStuck : t = Term.Stuck
                       · subst t
                         have hSt : signMatches M acc out Term.Stuck := by
                           simpa [__strip_even_exponent] using hSign
                         exfalso
                         exact not_signMatches_stuck M acc out hSt
                       · simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent,
                           htStuck] using hSign)
                  case UOp op2 =>
                    cases op2 <;>
                      try
                        (by_cases htStuck : t = Term.Stuck
                         · subst t
                           have hSt : signMatches M acc out Term.Stuck := by
                             simpa [__strip_even_exponent] using hSign
                           exfalso
                           exact not_signMatches_stuck M acc out hSt
                         · simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent,
                             htStuck] using hSign)
                    case mult =>
                      by_cases htStuck : t = Term.Stuck
                      · subst t
                        have hSt : signMatches M acc out Term.Stuck := by
                          simpa [__strip_even_exponent] using hSign
                        exfalso
                        exact not_signMatches_stuck M acc out hSt
                      · rcases mult_operands_non_none_and_eval_type_eq M hM t2
                          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t3) m) _hNN with
                          ⟨ht2NN, hTailNN, _⟩
                        rcases mult_operands_non_none_and_eval_type_eq M hM t3 m hTailNN with
                          ⟨ht3NN, hmNN, _⟩
                        have ht2Ne : t2 ≠ Term.Stuck :=
                          RuleProofs.term_ne_stuck_of_has_smt_translation t2 ht2NN
                        have ht3Ne : t3 ≠ Term.Stuck :=
                          RuleProofs.term_ne_stuck_of_has_smt_translation t3 ht3NN
                        cases hCond : __eo_and (__eo_eq t t2) (__eo_eq t t3) with
                        | Boolean b =>
                            cases b with
                            | true =>
                                rcases eo_eq_pair_true_eq htStuck ht2Ne ht3Ne hCond with
                                  ⟨rfl, rfl⟩
                                have hSub : signMatches M acc out
                                    (__strip_even_exponent t m) := by
                                  simpa [__strip_even_exponent, __eo_ite, hCond, htStuck, __eo_l_1___strip_even_exponent, hSign, native_ite, native_teq]
                                    using hSign
                                have hmSign : signMatches M acc out m :=
                                  strip_even_exponent_signMatches M hM t m acc out hmNN
                                    _htNZ hSub
                                exact signMatches_square_factor M hM acc out t m _hNN
                                  _htNZ hmSign
                            | false =>
                                simpa [__strip_even_exponent, __eo_ite,
                                  __eo_l_1___strip_even_exponent, hCond, htStuck, hSign, native_ite, native_teq]
                                  using hSign
                        | Stuck =>
                            have hSt : signMatches M acc out Term.Stuck := by
                              simpa [__strip_even_exponent, __eo_ite, hCond, htStuck, __eo_l_1___strip_even_exponent, hSign, native_ite, native_teq]
                                using hSign
                            exfalso
                            exact not_signMatches_stuck M acc out hSt
                        | _ =>
                            have hSt : signMatches M acc out Term.Stuck := by
                              simpa [__strip_even_exponent, __eo_ite, hCond, htStuck, __eo_l_1___strip_even_exponent, hSign, native_ite, native_teq]
                                using hSign
                            exfalso
                            exact not_signMatches_stuck M acc out hSt
termination_by m _ _ _ _ _ => m

private theorem strip_even_exponent_has_smt_translation (t : Term) :
    ∀ (m : Term),
      t ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt m) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (__strip_even_exponent t m)) ≠ SmtType.None
  | Term.Stuck, _htNe, hNN => by
      exfalso
      apply hNN
      change __smtx_typeof SmtTerm.None = SmtType.None
      unfold __smtx_typeof
      rfl
  | Term.Apply (Term.Apply (Term.UOp UserOp.mult) t2)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t3) m), htNe, hNN => by
      rcases mult_operands_non_none t2
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t3) m) hNN with
        ⟨ht2NN, hTailNN⟩
      rcases mult_operands_non_none t3 m hTailNN with
        ⟨ht3NN, hmNN⟩
      have ht2Ne : t2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation t2 ht2NN
      have ht3Ne : t3 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation t3 ht3NN
      rcases eo_eq_pair_bool htNe ht2Ne ht3Ne with ⟨b, hCond⟩
      cases b with
      | true =>
          rcases eo_eq_pair_true_eq htNe ht2Ne ht3Ne hCond with ⟨rfl, rfl⟩
          have hRec := strip_even_exponent_has_smt_translation t m htNe hmNN
          simpa [__strip_even_exponent, __eo_ite, hCond, htNe, __eo_l_1___strip_even_exponent, native_ite, native_teq] using hRec
      | false =>
          simpa [__strip_even_exponent, __eo_ite, __eo_l_1___strip_even_exponent,
            hCond, htNe, native_ite, native_teq] using hNN
  | m, htNe, hNN => by
      cases m <;>
        try simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htNe] using hNN
      case Apply f a =>
        cases f <;>
          try simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htNe] using hNN
        case Apply f1 t2 =>
          cases f1 <;>
            try simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htNe] using hNN
          case UOp op =>
            cases op <;>
              try simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htNe] using hNN
            case mult =>
              cases a <;>
                try simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htNe] using hNN
              case Apply g m =>
                cases g <;>
                  try simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htNe] using hNN
                case Apply g1 t3 =>
                  cases g1 <;>
                    try simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htNe] using hNN
                  case UOp op2 =>
                    cases op2 <;>
                      try simpa [__strip_even_exponent, __eo_l_1___strip_even_exponent, htNe] using hNN
                    case mult =>
                      rcases mult_operands_non_none t2
                          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t3) m) hNN with
                        ⟨ht2NN, hTailNN⟩
                      rcases mult_operands_non_none t3 m hTailNN with
                        ⟨ht3NN, hmNN⟩
                      have ht2Ne : t2 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation t2 ht2NN
                      have ht3Ne : t3 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation t3 ht3NN
                      rcases eo_eq_pair_bool htNe ht2Ne ht3Ne with ⟨b, hCond⟩
                      cases b with
                      | true =>
                          rcases eo_eq_pair_true_eq htNe ht2Ne ht3Ne hCond with ⟨rfl, rfl⟩
                          have hRec := strip_even_exponent_has_smt_translation t m htNe hmNN
                          simpa [__strip_even_exponent, __eo_ite, hCond, htNe, __eo_l_1___strip_even_exponent, native_ite, native_teq] using hRec
                      | false =>
                          simpa [__strip_even_exponent, __eo_ite,
                            __eo_l_1___strip_even_exponent, hCond, htNe, native_ite, native_teq] using hNN
termination_by m _ _ => m

private inductive MultSignStage where
  | top
  | l1
  | l2
  | l3

private def multSignStageRank : MultSignStage -> Nat
  | MultSignStage.top => 3
  | MultSignStage.l1 => 2
  | MultSignStage.l2 => 1
  | MultSignStage.l3 => 0

private def run_arith_mult_sign_sgn_stage :
    MultSignStage -> Term -> Term -> Term -> Term
  | MultSignStage.top, sgn, cube, m => __mk_arith_mult_sign_sgn sgn cube m
  | MultSignStage.l1, sgn, cube, m => __eo_l_1___mk_arith_mult_sign_sgn sgn cube m
  | MultSignStage.l2, sgn, cube, m => __eo_l_2___mk_arith_mult_sign_sgn sgn cube m
  | MultSignStage.l3, sgn, cube, m => __eo_l_3___mk_arith_mult_sign_sgn sgn cube m

private theorem mk_arith_mult_sign_sgn_stage_signMatches
    (M : SmtModel) (hM : model_wf M) :
    ∀ (stage : MultSignStage) (sgn cube m : Term) (acc out : Bool),
      sgn = Term.Boolean acc ->
      eo_interprets M cube true ->
      __smtx_typeof (__eo_to_smt m) ≠ SmtType.None ->
      run_arith_mult_sign_sgn_stage stage sgn cube m = Term.Boolean out ->
      signMatches M acc out m := by
  intro stage sgn cube m acc out hSgn hCube hNN hOut
  have hmNe : m ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation m hNN
  have hCubeBool : RuleProofs.eo_has_bool_type cube :=
    RuleProofs.eo_has_bool_type_of_interprets_true M cube hCube
  have hCubeNN : RuleProofs.eo_has_smt_translation cube :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type cube hCubeBool
  have hCubeNe : cube ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation cube hCubeNN
  cases stage with
  | l3 =>
      subst sgn
      cases cube with
      | Boolean b =>
          cases b with
          | true =>
              have hReq :
                  __eo_requires (__eo_to_q m) (Term.Rational (native_mk_rational 1 1))
                    (Term.Boolean acc) = Term.Boolean out := by
                simpa [run_arith_mult_sign_sgn_stage,
                  __eo_l_3___mk_arith_mult_sign_sgn, hmNe] using hOut
              rcases requires_rational_bool_result hReq with ⟨hOne, hAcc⟩
              have hPos := smtValuePos_of_one_term M m hOne
              unfold signMatches
              cases acc <;> cases out <;> simp at hAcc ⊢
              · exact hPos
              · exact hPos
          | false =>
              exfalso
              simpa [run_arith_mult_sign_sgn_stage,
                __eo_l_3___mk_arith_mult_sign_sgn, hmNe] using hOut
      | _ =>
          exfalso
          simpa [run_arith_mult_sign_sgn_stage,
            __eo_l_3___mk_arith_mult_sign_sgn, hmNe] using hOut
  | l2 =>
      fun_cases __eo_l_2___mk_arith_mult_sign_sgn sgn cube m
      case case1 =>
          cases hSgn
      case case2 =>
          simp [run_arith_mult_sign_sgn_stage,
            __eo_l_2___mk_arith_mult_sign_sgn] at hOut
      case case3 =>
          simp [run_arith_mult_sign_sgn_stage,
            __eo_l_2___mk_arith_mult_sign_sgn] at hOut
      case case5 =>
          exact mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.l3
            sgn cube m acc out hSgn hCube hNN
            (by simpa [run_arith_mult_sign_sgn_stage,
              __eo_l_2___mk_arith_mult_sign_sgn] using hOut)
      case case4 t z F t2 m' _hSgnNe =>
      have hAtom := RuleProofs.eo_interprets_and_left M
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) z) F hCube
      have hF := RuleProofs.eo_interprets_and_right M
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) z) F hCube
      rcases mult_operands_non_none t2 m' hNN with ⟨ht2NN, hmNN⟩
      have ht2Ne : t2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation t2 ht2NN
      cases hCond : __eo_eq t t2 with
      | Boolean b =>
          cases b with
          | true =>
              have hEq := term_eq_of_eo_eq_true hCond
              have htNe : t ≠ Term.Stuck := by
                intro ht
                exact ht2Ne (hEq ▸ ht)
              subst t2
              have hThen :
                  __eo_requires (__eo_to_q z) (Term.Rational (native_mk_rational 0 1))
                    (__mk_arith_mult_sign_sgn (__eo_not sgn) F
                      (__strip_even_exponent t m')) = Term.Boolean out := by
                simpa [run_arith_mult_sign_sgn_stage,
                  __eo_l_2___mk_arith_mult_sign_sgn, __eo_ite, hCond, htNe,
                  __eo_not, __eo_l_3___mk_arith_mult_sign_sgn, native_ite, native_teq] using hOut
              rcases requires_rational_bool_result hThen with ⟨hZ, hRecOut⟩
              have htNeg := smtValueNeg_of_lt_zero M t z hZ hAtom
              have htNZ := smtValueNonzero_of_neg htNeg
              have hStripNN := strip_even_exponent_has_smt_translation t m' htNe hmNN
              have hNotSgn : __eo_not sgn = Term.Boolean (not acc) := by
                simpa [hSgn, __eo_not, SmtEval.native_not]
              have hRecSign :=
                mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.top
                  (__eo_not sgn) F (__strip_even_exponent t m') (not acc) out
                  hNotSgn hF hStripNN hRecOut
              have hmSign :=
                strip_even_exponent_signMatches M hM t m' (not acc) out hmNN htNZ hRecSign
              exact signMatches_neg_factor M hM acc out t m' hNN htNeg hmSign
          | false =>
              exact mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.l3
                sgn
                (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) z)) F)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t2) m')
                acc out hSgn hCube hNN
                (by simpa [run_arith_mult_sign_sgn_stage,
                  __eo_l_2___mk_arith_mult_sign_sgn, __eo_ite, hCond,
                  native_ite, native_teq] using hOut)
      | Stuck =>
          exfalso
          simpa [run_arith_mult_sign_sgn_stage,
            __eo_l_2___mk_arith_mult_sign_sgn, __eo_ite, hCond,
            native_ite, native_teq] using hOut
      | _ =>
          exfalso
          simpa [run_arith_mult_sign_sgn_stage,
            __eo_l_2___mk_arith_mult_sign_sgn, __eo_ite, hCond,
            native_ite, native_teq] using hOut
  | l1 =>
      fun_cases __eo_l_1___mk_arith_mult_sign_sgn sgn cube m
      case case1 =>
          cases hSgn
      case case2 =>
          simp [run_arith_mult_sign_sgn_stage,
            __eo_l_1___mk_arith_mult_sign_sgn] at hOut
      case case3 =>
          simp [run_arith_mult_sign_sgn_stage,
            __eo_l_1___mk_arith_mult_sign_sgn] at hOut
      case case5 =>
          exact mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.l2
            sgn cube m acc out hSgn hCube hNN
            (by simpa [run_arith_mult_sign_sgn_stage,
              __eo_l_1___mk_arith_mult_sign_sgn] using hOut)
      case case4 t z F t2 m' _hSgnNe =>
      have hAtom := RuleProofs.eo_interprets_and_left M
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) z) F hCube
      have hF := RuleProofs.eo_interprets_and_right M
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) z) F hCube
      rcases mult_operands_non_none t2 m' hNN with ⟨ht2NN, hmNN⟩
      have ht2Ne : t2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation t2 ht2NN
      cases hCond : __eo_eq t t2 with
      | Boolean b =>
          cases b with
          | true =>
              have hEq := term_eq_of_eo_eq_true hCond
              have htNe : t ≠ Term.Stuck := by
                intro ht
                exact ht2Ne (hEq ▸ ht)
              subst t2
              have hThen :
                  __eo_requires (__eo_to_q z) (Term.Rational (native_mk_rational 0 1))
                    (__mk_arith_mult_sign_sgn sgn F
                      (__strip_even_exponent t m')) = Term.Boolean out := by
                simpa [run_arith_mult_sign_sgn_stage,
                  __eo_l_1___mk_arith_mult_sign_sgn, __eo_ite, hCond, htNe, __eo_l_2___mk_arith_mult_sign_sgn, native_ite, native_teq] using hOut
              rcases requires_rational_bool_result hThen with ⟨hZ, hRecOut⟩
              have htPos := smtValuePos_of_gt_zero M t z hZ hAtom
              have htNZ := smtValueNonzero_of_pos htPos
              have hStripNN := strip_even_exponent_has_smt_translation t m' htNe hmNN
              have hRecSign :=
                mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.top
                  sgn F (__strip_even_exponent t m') acc out hSgn hF hStripNN hRecOut
              have hmSign :=
                strip_even_exponent_signMatches M hM t m' acc out hmNN htNZ hRecSign
              exact signMatches_pos_factor M hM acc out t m' hNN htPos hmSign
          | false =>
              exact mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.l2
                sgn
                (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) z)) F)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t2) m')
                acc out hSgn hCube hNN
                (by simpa [run_arith_mult_sign_sgn_stage,
                  __eo_l_1___mk_arith_mult_sign_sgn, __eo_ite, hCond,
                  native_ite, native_teq] using hOut)
      | Stuck =>
          exfalso
          simpa [run_arith_mult_sign_sgn_stage,
            __eo_l_1___mk_arith_mult_sign_sgn, __eo_ite, hCond,
            native_ite, native_teq] using hOut
      | _ =>
          exfalso
          simpa [run_arith_mult_sign_sgn_stage,
            __eo_l_1___mk_arith_mult_sign_sgn, __eo_ite, hCond,
            native_ite, native_teq] using hOut
  | top =>
      fun_cases __mk_arith_mult_sign_sgn sgn cube m
      case case1 =>
          cases hSgn
      case case2 =>
          simp [run_arith_mult_sign_sgn_stage,
            __mk_arith_mult_sign_sgn] at hOut
      case case3 =>
          simp [run_arith_mult_sign_sgn_stage,
            __mk_arith_mult_sign_sgn] at hOut
      case case5 =>
          exact mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.l1
            sgn cube m acc out hSgn hCube hNN
            (by simpa [run_arith_mult_sign_sgn_stage,
              __mk_arith_mult_sign_sgn] using hOut)
      case case4 t z F t2 t3 m' _hSgnNe =>
      have hAtom := RuleProofs.eo_interprets_and_left M
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) z)) F hCube
      have hF := RuleProofs.eo_interprets_and_right M
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) z)) F hCube
      rcases mult_operands_non_none t2
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t3) m') hNN with
        ⟨ht2NN, hTailNN⟩
      rcases mult_operands_non_none t3 m' hTailNN with ⟨ht3NN, hmNN⟩
      have ht2Ne : t2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation t2 ht2NN
      have ht3Ne : t3 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation t3 ht3NN
      cases hCond : __eo_and (__eo_eq t t2) (__eo_eq t t3) with
      | Boolean b =>
          cases b with
          | true =>
              have htNe : t ≠ Term.Stuck := by
                intro ht
                subst t
                simp [__eo_eq, __eo_and] at hCond
              rcases eo_eq_pair_true_eq htNe ht2Ne ht3Ne hCond with ⟨rfl, rfl⟩
              have hThen :
                  __eo_requires (__eo_to_q z) (Term.Rational (native_mk_rational 0 1))
                    (__mk_arith_mult_sign_sgn sgn F
                      (__strip_even_exponent t m')) = Term.Boolean out := by
                simpa [run_arith_mult_sign_sgn_stage,
                  __mk_arith_mult_sign_sgn, __eo_ite, hCond, htNe, __eo_l_1___mk_arith_mult_sign_sgn, native_ite, native_teq] using hOut
              rcases requires_rational_bool_result hThen with ⟨hZ, hRecOut⟩
              have htNZ := smtValueNonzero_of_not_eq_zero M hM t z hZ hAtom
              have hStripNN := strip_even_exponent_has_smt_translation t m' htNe hmNN
              have hRecSign :=
                mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.top
                  sgn F (__strip_even_exponent t m') acc out hSgn hF hStripNN hRecOut
              have hmSign :=
                strip_even_exponent_signMatches M hM t m' acc out hmNN htNZ hRecSign
              exact signMatches_square_factor M hM acc out t m' hNN htNZ hmSign
          | false =>
              exact mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.l1
                sgn
                (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                  (Term.Apply (Term.UOp UserOp.not)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) z))) F)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t2)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t3) m'))
                acc out hSgn hCube hNN
                (by simpa [run_arith_mult_sign_sgn_stage,
                  __mk_arith_mult_sign_sgn, __eo_ite, hCond,
                  native_ite, native_teq] using hOut)
      | Stuck =>
          exfalso
          simpa [run_arith_mult_sign_sgn_stage,
            __mk_arith_mult_sign_sgn, __eo_ite, hCond,
            native_ite, native_teq] using hOut
      | _ =>
          exfalso
          simpa [run_arith_mult_sign_sgn_stage,
            __mk_arith_mult_sign_sgn, __eo_ite, hCond,
            native_ite, native_teq] using hOut
termination_by stage _sgn cube _m _acc _out _ _ _ _ => (sizeOf cube, multSignStageRank stage)
decreasing_by
  all_goals
    subst_vars
    simp_wf
    simp [multSignStageRank]
    omega

private theorem mk_arith_mult_sign_sgn_signMatches
    (M : SmtModel) (hM : model_wf M)
    (cube m : Term) (acc out : Bool)
    (hCube : eo_interprets M cube true)
    (hNN : __smtx_typeof (__eo_to_smt m) ≠ SmtType.None)
    (hOut : __mk_arith_mult_sign_sgn (Term.Boolean acc) cube m = Term.Boolean out) :
    signMatches M acc out m :=
  mk_arith_mult_sign_sgn_stage_signMatches M hM MultSignStage.top
    (Term.Boolean acc) cube m acc out rfl hCube hNN
    (by simpa [run_arith_mult_sign_sgn_stage] using hOut)

private theorem to_cube_interprets_true
    (M : SmtModel) (F : Term) :
    eo_interprets M F true ->
    eo_interprets M (__to_cube F) true := by
  intro hF
  fun_cases __to_cube F
  case case1 =>
      simpa [__to_cube] using hF
  case case2 F1 F2 =>
      simpa [__to_cube] using hF
  case case3 =>
      simpa [__to_cube] using hF
  case case4 F1 =>
      simpa [__to_cube] using
        RuleProofs.eo_interprets_and_intro M F (Term.Boolean true)
          hF (RuleProofs.eo_interprets_true M)

private theorem eo_interprets_gt_zero_of_smtValuePos
    (M : SmtModel) (hM : model_wf M) (m : Term)
    (hNN : __smtx_typeof (__eo_to_smt m) ≠ SmtType.None)
    (hPos : smtValuePos (__smtx_model_eval M (__eo_to_smt m))) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) m)
        (__arith_mk_zero (__eo_typeof m))) true := by
  cases hEval : __smtx_model_eval M (__eo_to_smt m) with
  | Numeral n =>
      rw [hEval] at hPos
      simp [smtValuePos] at hPos
      have hPres :=
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m) hNN
      have hTy : __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
        rw [hEval] at hPres
        simpa [__smtx_typeof_value] using hPres.symm
      have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation m hNN
      have hEoSmt : __eo_to_smt_type (__eo_typeof m) = SmtType.Int :=
        hMatch.symm.trans hTy
      have hEoTy : __eo_typeof m = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int hEoSmt
      rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_gt_eq]
      refine smt_interprets.intro_true M
        (SmtTerm.gt (__eo_to_smt m) (__eo_to_smt (__arith_mk_zero (__eo_typeof m)))) ?_ ?_
      · rw [typeof_gt_eq]
        rw [hEoTy]
        rw [hTy]
        change __smtx_typeof_arith_overload_op_2_ret SmtType.Int
          (__smtx_typeof (SmtTerm.Numeral 0)) SmtType.Bool = SmtType.Bool
        rw [__smtx_typeof.eq_2]
        rfl
      · rw [hEoTy, __smtx_model_eval.eq_19]
        change __smtx_model_eval_gt (__smtx_model_eval M (__eo_to_smt m))
          (__smtx_model_eval M (SmtTerm.Numeral 0)) = SmtValue.Boolean true
        rw [__smtx_model_eval.eq_2, hEval]
        simpa [__smtx_model_eval_gt, __smtx_model_eval_lt, native_zlt,
          SmtEval.native_zlt] using hPos
  | Rational q =>
      rw [hEval] at hPos
      simp [smtValuePos] at hPos
      have hPres :=
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m) hNN
      have hTy : __smtx_typeof (__eo_to_smt m) = SmtType.Real := by
        rw [hEval] at hPres
        simpa [__smtx_typeof_value] using hPres.symm
      have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation m hNN
      have hEoSmt : __eo_to_smt_type (__eo_typeof m) = SmtType.Real :=
        hMatch.symm.trans hTy
      have hEoTy : __eo_typeof m = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real hEoSmt
      rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_gt_eq]
      refine smt_interprets.intro_true M
        (SmtTerm.gt (__eo_to_smt m) (__eo_to_smt (__arith_mk_zero (__eo_typeof m)))) ?_ ?_
      · rw [typeof_gt_eq]
        rw [hEoTy]
        rw [hTy]
        change __smtx_typeof_arith_overload_op_2_ret SmtType.Real
          (__smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1))) SmtType.Bool =
            SmtType.Bool
        rw [__smtx_typeof.eq_3]
        rfl
      · rw [hEoTy, __smtx_model_eval.eq_19]
        change __smtx_model_eval_gt (__smtx_model_eval M (__eo_to_smt m))
          (__smtx_model_eval M (SmtTerm.Rational (native_mk_rational 0 1))) =
            SmtValue.Boolean true
        rw [__smtx_model_eval.eq_3, hEval]
        simpa [__smtx_model_eval_gt, __smtx_model_eval_lt, native_qlt,
          SmtEval.native_qlt, native_mk_rational_zero] using hPos
  | _ =>
      rw [hEval] at hPos
      simp [smtValuePos] at hPos

private theorem eo_interprets_lt_zero_of_smtValueNeg
    (M : SmtModel) (hM : model_wf M) (m : Term)
    (hNN : __smtx_typeof (__eo_to_smt m) ≠ SmtType.None)
    (hNeg : smtValueNeg (__smtx_model_eval M (__eo_to_smt m))) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) m)
        (__arith_mk_zero (__eo_typeof m))) true := by
  cases hEval : __smtx_model_eval M (__eo_to_smt m) with
  | Numeral n =>
      rw [hEval] at hNeg
      simp [smtValueNeg] at hNeg
      have hPres :=
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m) hNN
      have hTy : __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
        rw [hEval] at hPres
        simpa [__smtx_typeof_value] using hPres.symm
      have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation m hNN
      have hEoSmt : __eo_to_smt_type (__eo_typeof m) = SmtType.Int :=
        hMatch.symm.trans hTy
      have hEoTy : __eo_typeof m = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int hEoSmt
      rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_lt_eq]
      refine smt_interprets.intro_true M
        (SmtTerm.lt (__eo_to_smt m) (__eo_to_smt (__arith_mk_zero (__eo_typeof m)))) ?_ ?_
      · rw [typeof_lt_eq]
        rw [hEoTy]
        rw [hTy]
        change __smtx_typeof_arith_overload_op_2_ret SmtType.Int
          (__smtx_typeof (SmtTerm.Numeral 0)) SmtType.Bool = SmtType.Bool
        rw [__smtx_typeof.eq_2]
        rfl
      · rw [hEoTy, __smtx_model_eval.eq_17]
        change __smtx_model_eval_lt (__smtx_model_eval M (__eo_to_smt m))
          (__smtx_model_eval M (SmtTerm.Numeral 0)) = SmtValue.Boolean true
        rw [__smtx_model_eval.eq_2, hEval]
        simpa [__smtx_model_eval_lt, native_zlt, SmtEval.native_zlt] using hNeg
  | Rational q =>
      rw [hEval] at hNeg
      simp [smtValueNeg] at hNeg
      have hPres :=
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m) hNN
      have hTy : __smtx_typeof (__eo_to_smt m) = SmtType.Real := by
        rw [hEval] at hPres
        simpa [__smtx_typeof_value] using hPres.symm
      have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation m hNN
      have hEoSmt : __eo_to_smt_type (__eo_typeof m) = SmtType.Real :=
        hMatch.symm.trans hTy
      have hEoTy : __eo_typeof m = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real hEoSmt
      rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_lt_eq]
      refine smt_interprets.intro_true M
        (SmtTerm.lt (__eo_to_smt m) (__eo_to_smt (__arith_mk_zero (__eo_typeof m)))) ?_ ?_
      · rw [typeof_lt_eq]
        rw [hEoTy]
        rw [hTy]
        change __smtx_typeof_arith_overload_op_2_ret SmtType.Real
          (__smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1))) SmtType.Bool =
            SmtType.Bool
        rw [__smtx_typeof.eq_3]
        rfl
      · rw [hEoTy, __smtx_model_eval.eq_17]
        change __smtx_model_eval_lt (__smtx_model_eval M (__eo_to_smt m))
          (__smtx_model_eval M (SmtTerm.Rational (native_mk_rational 0 1))) =
            SmtValue.Boolean true
        rw [__smtx_model_eval.eq_3, hEval]
        simpa [__smtx_model_eval_lt, native_qlt, SmtEval.native_qlt,
          native_mk_rational_zero] using hNeg
  | _ =>
      rw [hEval] at hNeg
      simp [smtValueNeg] at hNeg

private theorem signMatches_true_relation
    (M : SmtModel) (hM : model_wf M) (m : Term) (out : Bool)
    (hNN : __smtx_typeof (__eo_to_smt m) ≠ SmtType.None)
    (hSign : signMatches M true out m) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (if out then Term.UOp UserOp.gt else Term.UOp UserOp.lt) m)
        (__arith_mk_zero (__eo_typeof m))) true := by
  cases out <;> simp [signMatches] at hSign ⊢
  · exact eo_interprets_lt_zero_of_smtValueNeg M hM m hNN hSign
  · exact eo_interprets_gt_zero_of_smtValuePos M hM m hNN hSign

private theorem eo_typeof_imp_left_eq_bool {A B : Term} :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) = Term.Bool ->
    __eo_typeof A = Term.Bool := by
  intro hTy
  change __eo_typeof_or (__eo_typeof A) (__eo_typeof B) = Term.Bool at hTy
  exact CnfSupport.typeof_or_eq_bool_left hTy

private theorem eo_typeof_imp_right_eq_bool {A B : Term} :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) = Term.Bool ->
    __eo_typeof B = Term.Bool := by
  intro hTy
  change __eo_typeof_or (__eo_typeof A) (__eo_typeof B) = Term.Bool at hTy
  exact CnfSupport.typeof_or_eq_bool_right hTy

private theorem arith_mk_zero_typeof (T : Term) :
    __eo_typeof (__arith_mk_zero T) =
      match T with
      | Term.UOp UserOp.Int => Term.UOp UserOp.Int
      | Term.UOp UserOp.Real => Term.UOp UserOp.Real
      | _ => Term.Stuck := by
  cases T <;> try rfl
  case UOp op =>
    cases op <;> rfl

private theorem arith_zero_rel_arg_type_of_typeof_bool
    (m : Term)
    (hTy :
      __eo_typeof_lt (__eo_typeof m)
        (__eo_typeof (__arith_mk_zero (__eo_typeof m))) = Term.Bool) :
    __eo_typeof m = Term.UOp UserOp.Int ∨
      __eo_typeof m = Term.UOp UserOp.Real := by
  generalize hMT : __eo_typeof m = mt at hTy
  rw [arith_mk_zero_typeof mt] at hTy
  cases mt <;>
    simp [__eo_typeof_lt, __eo_requires, __is_arith_type, __eo_eq, native_ite,
      native_teq, native_not, SmtEval.native_not] at hTy
  case UOp op =>
    cases op <;>
      simp at hTy
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem gt_zero_has_bool_type_of_typeof_bool
    (m : Term)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hTy : __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) m)
        (__arith_mk_zero (__eo_typeof m))) = Term.Bool) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) m)
        (__arith_mk_zero (__eo_typeof m))) := by
  have hArgTy : __eo_typeof m = Term.UOp UserOp.Int ∨
      __eo_typeof m = Term.UOp UserOp.Real :=
    arith_zero_rel_arg_type_of_typeof_bool m (by
      change __eo_typeof_lt (__eo_typeof m)
        (__eo_typeof (__arith_mk_zero (__eo_typeof m))) = Term.Bool at hTy
      exact hTy)
  rcases hArgTy with hInt | hReal
  · have hmTy : __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
      simpa [hInt] using TranslationProofs.eo_to_smt_typeof_matches_translation m hMTrans
    unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_gt_eq, typeof_gt_eq, hInt]
    rw [hmTy]
    change __smtx_typeof_arith_overload_op_2_ret SmtType.Int
      (__smtx_typeof (SmtTerm.Numeral 0)) SmtType.Bool = SmtType.Bool
    rw [__smtx_typeof.eq_2]
    rfl
  · have hmTy : __smtx_typeof (__eo_to_smt m) = SmtType.Real := by
      simpa [hReal] using TranslationProofs.eo_to_smt_typeof_matches_translation m hMTrans
    unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_gt_eq, typeof_gt_eq, hReal]
    rw [hmTy]
    change __smtx_typeof_arith_overload_op_2_ret SmtType.Real
      (__smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1))) SmtType.Bool =
        SmtType.Bool
    rw [__smtx_typeof.eq_3]
    rfl

private theorem lt_zero_has_bool_type_of_typeof_bool
    (m : Term)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hTy : __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) m)
        (__arith_mk_zero (__eo_typeof m))) = Term.Bool) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) m)
        (__arith_mk_zero (__eo_typeof m))) := by
  have hArgTy : __eo_typeof m = Term.UOp UserOp.Int ∨
      __eo_typeof m = Term.UOp UserOp.Real :=
    arith_zero_rel_arg_type_of_typeof_bool m (by
      change __eo_typeof_lt (__eo_typeof m)
        (__eo_typeof (__arith_mk_zero (__eo_typeof m))) = Term.Bool at hTy
      exact hTy)
  rcases hArgTy with hInt | hReal
  · have hmTy : __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
      simpa [hInt] using TranslationProofs.eo_to_smt_typeof_matches_translation m hMTrans
    unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq, hInt]
    rw [hmTy]
    change __smtx_typeof_arith_overload_op_2_ret SmtType.Int
      (__smtx_typeof (SmtTerm.Numeral 0)) SmtType.Bool = SmtType.Bool
    rw [__smtx_typeof.eq_2]
    rfl
  · have hmTy : __smtx_typeof (__eo_to_smt m) = SmtType.Real := by
      simpa [hReal] using TranslationProofs.eo_to_smt_typeof_matches_translation m hMTrans
    unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq, hReal]
    rw [hmTy]
    change __smtx_typeof_arith_overload_op_2_ret SmtType.Real
      (__smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1))) SmtType.Bool =
        SmtType.Bool
    rw [__smtx_typeof.eq_3]
    rfl
public theorem cmd_step_arith_mult_sign_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_sign args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_mult_sign args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_sign args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_mult_sign args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons F args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons m args =>
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
                  change __eo_typeof (__eo_prog_arith_mult_sign F m) = Term.Bool at hResultTy
                  change __eo_prog_arith_mult_sign F m ≠ Term.Stuck at hProg
                  have hArgsTrans :
                      cArgListTranslationOk (CArgList.cons F (CArgList.cons m CArgList.nil)) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  have hFTrans : RuleProofs.eo_has_smt_translation F := by
                    simpa [cArgListTranslationOk, RuleProofs.eo_has_smt_translation,
                      eoHasSmtTranslation] using hArgsTrans.1
                  have hMTrans : RuleProofs.eo_has_smt_translation m := by
                    simpa [cArgListTranslationOk, RuleProofs.eo_has_smt_translation,
                      eoHasSmtTranslation] using hArgsTrans.2.1
                  have hFNe : F ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation F hFTrans
                  have hMNe : m ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
                  cases hSgn : __mk_arith_mult_sign_sgn (Term.Boolean true) (__to_cube F) m with
                  | Boolean out =>
                      let rel : Term :=
                        Term.Apply
                          (Term.Apply
                            (if out then Term.UOp UserOp.gt else Term.UOp UserOp.lt) m)
                          (__arith_mk_zero (__eo_typeof m))
                      have hZeroNe : __arith_mk_zero (__eo_typeof m) ≠ Term.Stuck := by
                        intro hZero
                        apply hProg
                        cases out <;>
                          simp [__eo_prog_arith_mult_sign,__eo_ite,
                            __eo_mk_apply, hSgn, hZero, native_ite, native_teq]
                      have hTypeImp :
                          __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F) rel) =
                            Term.Bool := by
                        cases out <;>
                          simpa [rel, __eo_prog_arith_mult_sign, hFNe, hMNe, __eo_ite,
                            __eo_mk_apply, hSgn, hZeroNe, native_ite, native_teq] using hResultTy
                      have hFTypeof : __eo_typeof F = Term.Bool :=
                        eo_typeof_imp_left_eq_bool hTypeImp
                      have hFBool : RuleProofs.eo_has_bool_type F :=
                        RuleProofs.eo_typeof_bool_implies_has_bool_type F hFTrans hFTypeof
                      have hRelTypeof : __eo_typeof rel = Term.Bool :=
                        eo_typeof_imp_right_eq_bool hTypeImp
                      have hRelBool : RuleProofs.eo_has_bool_type rel := by
                        cases out with
                        | false =>
                            exact lt_zero_has_bool_type_of_typeof_bool m hMTrans
                              (by simpa [rel] using hRelTypeof)
                        | true =>
                            exact gt_zero_has_bool_type_of_typeof_bool m hMTrans
                              (by simpa [rel] using hRelTypeof)
                      have hImpTrue :
                          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F) rel)
                            true := by
                        rcases CnfSupport.eo_interprets_bool_cases M hM F hFBool with
                          hFTrue | hFFalse
                        · have hCube : eo_interprets M (__to_cube F) true :=
                            to_cube_interprets_true M F hFTrue
                          have hSign : signMatches M true out m :=
                            mk_arith_mult_sign_sgn_signMatches M hM (__to_cube F) m true out
                              hCube hMTrans hSgn
                          have hRelTrue : eo_interprets M rel true := by
                            simpa [rel] using
                              signMatches_true_relation M hM m out hMTrans hSign
                          exact CnfSupport.eo_interprets_imp_true_of_right_true M hM F rel
                            hFBool hRelTrue
                        · exact CnfSupport.eo_interprets_imp_true_of_left_false M hM F rel
                            hFFalse hRelBool
                      have hProgTrue : eo_interprets M (__eo_prog_arith_mult_sign F m) true := by
                        cases out <;>
                          simpa [rel, __eo_prog_arith_mult_sign, hFNe, hMNe, __eo_ite,
                            __eo_mk_apply, hSgn, hZeroNe, native_ite, native_teq] using hImpTrue
                      have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_arith_mult_sign F m) := by
                        have hImpBool :
                            RuleProofs.eo_has_bool_type
                              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) F) rel) :=
                          CnfSupport.eo_has_bool_type_imp_of_bool_args F rel hFBool hRelBool
                        cases out <;>
                          simpa [rel, __eo_prog_arith_mult_sign, hFNe, hMNe, __eo_ite,
                            __eo_mk_apply, hSgn, hZeroNe, native_ite, native_teq] using hImpBool
                      refine ⟨?_, ?_⟩
                      · intro _hPremisesTrue
                        exact hProgTrue
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          hProgBool
                  | _ =>
                      exact False.elim (hProg (by
                        simp [__eo_prog_arith_mult_sign,__eo_ite,
                          __eo_mk_apply, hSgn, native_ite, native_teq]))
