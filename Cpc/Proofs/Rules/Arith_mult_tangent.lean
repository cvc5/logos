module

public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def mtRel (op : UserOp) (u v : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp op) u) v

private def mtMul (u v : Term) : Term :=
  mtRel UserOp.mult u v

private def mtPlus (u v : Term) : Term :=
  mtRel UserOp.plus u v

private def mtSub (u v : Term) : Term :=
  mtRel UserOp.neg u v

private def mtAnd (u v : Term) : Term :=
  mtRel UserOp.and u v

private def mtOr (u v : Term) : Term :=
  mtRel UserOp.or u v

private def mtTangentFormula
    (prodRel firstYRel secondYRel : UserOp)
    (one zero x y a b : Term) : Term :=
  mtRel UserOp.eq
    (mtRel prodRel
      (mtMul x (mtMul y one))
      (mtSub
        (mtPlus
          (mtMul b (mtMul x one))
          (mtPlus (mtMul a (mtMul y one)) zero))
        (mtMul a (mtMul b one))))
    (mtOr
      (mtAnd (mtRel UserOp.leq x a)
        (mtAnd (mtRel firstYRel y b) (Term.Boolean true)))
      (mtOr
        (mtAnd (mtRel UserOp.geq x a)
          (mtAnd (mtRel secondYRel y b) (Term.Boolean true)))
        (Term.Boolean false)))

private def smtTangentFormula
    (prodRel firstYRel secondYRel : SmtTerm -> SmtTerm -> SmtTerm)
    (one zero x y a b : SmtTerm) : SmtTerm :=
  SmtTerm.eq
    (prodRel
      (SmtTerm.mult x (SmtTerm.mult y one))
      (SmtTerm.neg
        (SmtTerm.plus
          (SmtTerm.mult b (SmtTerm.mult x one))
          (SmtTerm.plus (SmtTerm.mult a (SmtTerm.mult y one)) zero))
        (SmtTerm.mult a (SmtTerm.mult b one))))
    (SmtTerm.or
      (SmtTerm.and (SmtTerm.leq x a)
        (SmtTerm.and (firstYRel y b) (SmtTerm.Boolean true)))
      (SmtTerm.or
        (SmtTerm.and (SmtTerm.geq x a)
          (SmtTerm.and (secondYRel y b) (SmtTerm.Boolean true)))
        (SmtTerm.Boolean false)))

private theorem eo_to_smt_mtTangent_true
    (one zero x y a b : Term) :
    __eo_to_smt
      (mtTangentFormula UserOp.geq UserOp.leq UserOp.geq one zero x y a b) =
    smtTangentFormula SmtTerm.geq SmtTerm.leq SmtTerm.geq
      (__eo_to_smt one) (__eo_to_smt zero)
      (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_mtTangent_false
    (one zero x y a b : Term) :
    __eo_to_smt
      (mtTangentFormula UserOp.leq UserOp.geq UserOp.leq one zero x y a b) =
    smtTangentFormula SmtTerm.leq SmtTerm.geq SmtTerm.leq
      (__eo_to_smt one) (__eo_to_smt zero)
      (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_mtTangent_true_int
    (x y a b : Term) :
    __eo_to_smt
      (mtTangentFormula UserOp.geq UserOp.leq UserOp.geq
        (Term.Numeral 1) (Term.Numeral 0) x y a b) =
    smtTangentFormula SmtTerm.geq SmtTerm.leq SmtTerm.geq
      (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)
      (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_mtTangent_false_int
    (x y a b : Term) :
    __eo_to_smt
      (mtTangentFormula UserOp.leq UserOp.geq UserOp.leq
        (Term.Numeral 1) (Term.Numeral 0) x y a b) =
    smtTangentFormula SmtTerm.leq SmtTerm.geq SmtTerm.leq
      (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)
      (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_mtTangent_true_real
    (x y a b : Term) :
    __eo_to_smt
      (mtTangentFormula UserOp.geq UserOp.leq UserOp.geq
        (Term.Rational (native_mk_rational 1 1))
        (Term.Rational (native_mk_rational 0 1)) x y a b) =
    smtTangentFormula SmtTerm.geq SmtTerm.leq SmtTerm.geq
      (SmtTerm.Rational (native_mk_rational 1 1))
      (SmtTerm.Rational (native_mk_rational 0 1))
      (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_mtTangent_false_real
    (x y a b : Term) :
    __eo_to_smt
      (mtTangentFormula UserOp.leq UserOp.geq UserOp.leq
        (Term.Rational (native_mk_rational 1 1))
        (Term.Rational (native_mk_rational 0 1)) x y a b) =
    smtTangentFormula SmtTerm.leq SmtTerm.geq SmtTerm.leq
      (SmtTerm.Rational (native_mk_rational 1 1))
      (SmtTerm.Rational (native_mk_rational 0 1))
      (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem smt_eval_int_of_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    ∃ n : native_Int, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral n := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact int_value_canonical (by simpa [hTy] using hPres)

private theorem smt_eval_real_of_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    ∃ q : native_Rat, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Rational q := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact real_value_canonical (by simpa [hTy] using hPres)

private theorem smt_type_int_of_eo_type
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof t = Term.UOp UserOp.Int) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  simpa [hTy, __eo_to_smt_type] using hMatch

private theorem smt_type_real_of_eo_type
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof t = Term.UOp UserOp.Real) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  simpa [hTy, __eo_to_smt_type] using hMatch

private theorem int_tangent_geq_prop (x y a b : Int) :
    (b*x + a*y + -(a*b) <= x*y) ↔
      ((x <= a ∧ y <= b) ∨ (a <= x ∧ b <= y)) := by
  constructor
  · intro hrel
    by_cases hx : x <= a
    · by_cases hy : y <= b
      · exact Or.inl ⟨hx, hy⟩
      · have hby : b <= y := by omega
        by_cases hax : a <= x
        · exact Or.inr ⟨hax, hby⟩
        · have hposx : 0 < a - x := by omega
          have hposy : 0 < y - b := by omega
          have hprod : 0 < (a - x) * (y - b) := Int.mul_pos hposx hposy
          have hlt : x*y < b*x + a*y + -(a*b) := by grind
          omega
    · have hax : a <= x := by omega
      by_cases hby : b <= y
      · exact Or.inr ⟨hax, hby⟩
      · have hy : y <= b := by omega
        by_cases hx' : x <= a
        · exact Or.inl ⟨hx', hy⟩
        · have hposx : 0 < x - a := by omega
          have hposy : 0 < b - y := by omega
          have hprod : 0 < (x - a) * (b - y) := Int.mul_pos hposx hposy
          have hlt : x*y < b*x + a*y + -(a*b) := by grind
          omega
  · intro h
    rcases h with h | h
    · have hax : 0 <= a - x := by omega
      have hby : 0 <= b - y := by omega
      have hprod : 0 <= (a - x) * (b - y) := Int.mul_nonneg hax hby
      grind
    · have hxa : 0 <= x - a := by omega
      have hyb : 0 <= y - b := by omega
      have hprod : 0 <= (x - a) * (y - b) := Int.mul_nonneg hxa hyb
      grind

private theorem int_tangent_leq_prop (x y a b : Int) :
    (x*y <= b*x + a*y + -(a*b)) ↔
      ((x <= a ∧ b <= y) ∨ (a <= x ∧ y <= b)) := by
  constructor
  · intro hrel
    by_cases hx : x <= a
    · by_cases hby : b <= y
      · exact Or.inl ⟨hx, hby⟩
      · have hyb : y < b := by omega
        by_cases hax : a <= x
        · have hy : y <= b := by omega
          exact Or.inr ⟨hax, hy⟩
        · have hposx : 0 < a - x := by omega
          have hposy : 0 < b - y := by omega
          have hprod : 0 < (a - x) * (b - y) := Int.mul_pos hposx hposy
          have hlt : b*x + a*y + -(a*b) < x*y := by grind
          omega
    · have hax : a <= x := by omega
      by_cases hy : y <= b
      · exact Or.inr ⟨hax, hy⟩
      · have hposx : 0 < x - a := by omega
        have hposy : 0 < y - b := by omega
        have hprod : 0 < (x - a) * (y - b) := Int.mul_pos hposx hposy
        have hlt : b*x + a*y + -(a*b) < x*y := by grind
        omega
  · intro h
    rcases h with h | h
    · have hax : 0 <= a - x := by omega
      have hyb : 0 <= y - b := by omega
      have hprod : 0 <= (a - x) * (y - b) := Int.mul_nonneg hax hyb
      grind
    · have hxa : 0 <= x - a := by omega
      have hby : 0 <= b - y := by omega
      have hprod : 0 <= (x - a) * (b - y) := Int.mul_nonneg hxa hby
      grind

private theorem rat_tangent_geq_prop (x y a b : Rat) :
    (b*x + a*y + -(a*b) <= x*y) ↔
      ((x <= a ∧ y <= b) ∨ (a <= x ∧ b <= y)) := by
  constructor
  · intro hrel
    by_cases hx : x <= a
    · by_cases hy : y <= b
      · exact Or.inl ⟨hx, hy⟩
      · have hby : b <= y := by grind
        by_cases hax : a <= x
        · exact Or.inr ⟨hax, hby⟩
        · have hposx : 0 < a - x := by grind
          have hposy : 0 < y - b := by grind
          have hprod : 0 < (a - x) * (y - b) := Rat.mul_pos hposx hposy
          have hlt : x*y < b*x + a*y + -(a*b) := by grind
          grind
    · have hax : a <= x := by grind
      by_cases hby : b <= y
      · exact Or.inr ⟨hax, hby⟩
      · have hy : y <= b := by grind
        by_cases hx' : x <= a
        · exact Or.inl ⟨hx', hy⟩
        · have hposx : 0 < x - a := by grind
          have hposy : 0 < b - y := by grind
          have hprod : 0 < (x - a) * (b - y) := Rat.mul_pos hposx hposy
          have hlt : x*y < b*x + a*y + -(a*b) := by grind
          grind
  · intro h
    rcases h with h | h
    · have hax : 0 <= a - x := by grind
      have hby : 0 <= b - y := by grind
      have hprod : 0 <= (a - x) * (b - y) := Rat.mul_nonneg hax hby
      grind
    · have hxa : 0 <= x - a := by grind
      have hyb : 0 <= y - b := by grind
      have hprod : 0 <= (x - a) * (y - b) := Rat.mul_nonneg hxa hyb
      grind

private theorem rat_tangent_leq_prop (x y a b : Rat) :
    (x*y <= b*x + a*y + -(a*b)) ↔
      ((x <= a ∧ b <= y) ∨ (a <= x ∧ y <= b)) := by
  constructor
  · intro hrel
    by_cases hx : x <= a
    · by_cases hby : b <= y
      · exact Or.inl ⟨hx, hby⟩
      · by_cases hax : a <= x
        · have hy : y <= b := by grind
          exact Or.inr ⟨hax, hy⟩
        · have hposx : 0 < a - x := by grind
          have hposy : 0 < b - y := by grind
          have hprod : 0 < (a - x) * (b - y) := Rat.mul_pos hposx hposy
          have hlt : b*x + a*y + -(a*b) < x*y := by grind
          grind
    · have hax : a <= x := by grind
      by_cases hy : y <= b
      · exact Or.inr ⟨hax, hy⟩
      · have hposx : 0 < x - a := by grind
        have hposy : 0 < y - b := by grind
        have hprod : 0 < (x - a) * (y - b) := Rat.mul_pos hposx hposy
        have hlt : b*x + a*y + -(a*b) < x*y := by grind
        grind
  · intro h
    rcases h with h | h
    · have hax : 0 <= a - x := by grind
      have hyb : 0 <= y - b := by grind
      have hprod : 0 <= (a - x) * (y - b) := Rat.mul_nonneg hax hyb
      grind
    · have hxa : 0 <= x - a := by grind
      have hby : 0 <= b - y := by grind
      have hprod : 0 <= (x - a) * (b - y) := Rat.mul_nonneg hxa hby
      grind

private theorem native_z_tangent_geq (x y a b : native_Int) :
    native_zleq (native_zplus (native_zplus (native_zmult b x) (native_zmult a y))
      (native_zneg (native_zmult a b))) (native_zmult x y) =
      native_or (native_and (native_zleq x a) (native_zleq y b))
        (native_and (native_zleq a x) (native_zleq b y)) := by
  have hiff := int_tangent_geq_prop x y a b
  simp [native_zleq, SmtEval.native_zleq, native_zplus, SmtEval.native_zplus,
    native_zmult, SmtEval.native_zmult, native_zneg, SmtEval.native_zneg,
    native_and, SmtEval.native_and, native_or, SmtEval.native_or]
  -- v4.33 keeps the goal's `decide _ = true` shape (stale `Decidable`
  -- instance), so bridge it explicitly rather than via `simpa`.
  exact Bool.eq_iff_iff.mpr
    (Iff.trans (Iff.trans decide_eq_true_iff hiff) (by simp))

private theorem native_z_tangent_leq (x y a b : native_Int) :
    native_zleq (native_zmult x y)
      (native_zplus (native_zplus (native_zmult b x) (native_zmult a y))
        (native_zneg (native_zmult a b))) =
      native_or (native_and (native_zleq x a) (native_zleq b y))
        (native_and (native_zleq a x) (native_zleq y b)) := by
  have hiff := int_tangent_leq_prop x y a b
  simp [native_zleq, SmtEval.native_zleq, native_zplus, SmtEval.native_zplus,
    native_zmult, SmtEval.native_zmult, native_zneg, SmtEval.native_zneg,
    native_and, SmtEval.native_and, native_or, SmtEval.native_or]
  -- v4.33 keeps the goal's `decide _ = true` shape (stale `Decidable`
  -- instance), so bridge it explicitly rather than via `simpa`.
  exact Bool.eq_iff_iff.mpr
    (Iff.trans (Iff.trans decide_eq_true_iff hiff) (by simp))

private theorem native_q_tangent_geq (x y a b : native_Rat) :
    native_qleq (native_qplus (native_qplus (native_qmult b x) (native_qmult a y))
      (native_qneg (native_qmult a b))) (native_qmult x y) =
      native_or (native_and (native_qleq x a) (native_qleq y b))
        (native_and (native_qleq a x) (native_qleq b y)) := by
  have hiff := rat_tangent_geq_prop x y a b
  simp [native_qleq, Smtm.native_qleq, native_qplus, SmtEval.native_qplus,
    native_qmult, SmtEval.native_qmult, native_qneg, SmtEval.native_qneg,
    native_and, SmtEval.native_and, native_or, SmtEval.native_or]
  -- v4.33 keeps the goal's `decide _ = true` shape (stale `Decidable`
  -- instance), so bridge it explicitly rather than via `simpa`.
  exact Bool.eq_iff_iff.mpr
    (Iff.trans (Iff.trans decide_eq_true_iff hiff) (by simp))

private theorem native_q_tangent_leq (x y a b : native_Rat) :
    native_qleq (native_qmult x y)
      (native_qplus (native_qplus (native_qmult b x) (native_qmult a y))
        (native_qneg (native_qmult a b))) =
      native_or (native_and (native_qleq x a) (native_qleq b y))
        (native_and (native_qleq a x) (native_qleq y b)) := by
  have hiff := rat_tangent_leq_prop x y a b
  simp [native_qleq, Smtm.native_qleq, native_qplus, SmtEval.native_qplus,
    native_qmult, SmtEval.native_qmult, native_qneg, SmtEval.native_qneg,
    native_and, SmtEval.native_and, native_or, SmtEval.native_or]
  -- v4.33 keeps the goal's `decide _ = true` shape (stale `Decidable`
  -- instance), so bridge it explicitly rather than via `simpa`.
  exact Bool.eq_iff_iff.mpr
    (Iff.trans (Iff.trans decide_eq_true_iff hiff) (by simp))

private theorem native_mk_rational_zero :
    native_mk_rational 0 1 = (0 : Rat) := by
  native_decide

private theorem native_mk_rational_one :
    native_mk_rational 1 1 = (1 : Rat) := by
  native_decide

private theorem mtTangent_true_has_bool_type_of_smt_type
    (one zero x y a b : Term) (T : SmtType)
    (hOne : __smtx_typeof (__eo_to_smt one) = T)
    (hZero : __smtx_typeof (__eo_to_smt zero) = T)
    (hX : __smtx_typeof (__eo_to_smt x) = T)
    (hY : __smtx_typeof (__eo_to_smt y) = T)
    (hA : __smtx_typeof (__eo_to_smt a) = T)
    (hB : __smtx_typeof (__eo_to_smt b) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    RuleProofs.eo_has_bool_type
      (mtTangentFormula UserOp.geq UserOp.leq UserOp.geq one zero x y a b) := by
  unfold RuleProofs.eo_has_bool_type
  rw [eo_to_smt_mtTangent_true]
  rcases hT with rfl | rfl
  · simp [smtTangentFormula, __smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
      typeof_eq_eq,
      __smtx_typeof_arith_overload_op_2, __smtx_typeof_arith_overload_op_2_ret,
      hOne, hZero, hX, hY, hA, hB, native_ite, native_Teq]
  · simp [smtTangentFormula, __smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
      typeof_eq_eq,
      __smtx_typeof_arith_overload_op_2, __smtx_typeof_arith_overload_op_2_ret,
      hOne, hZero, hX, hY, hA, hB, native_ite, native_Teq]

private theorem mtTangent_false_has_bool_type_of_smt_type
    (one zero x y a b : Term) (T : SmtType)
    (hOne : __smtx_typeof (__eo_to_smt one) = T)
    (hZero : __smtx_typeof (__eo_to_smt zero) = T)
    (hX : __smtx_typeof (__eo_to_smt x) = T)
    (hY : __smtx_typeof (__eo_to_smt y) = T)
    (hA : __smtx_typeof (__eo_to_smt a) = T)
    (hB : __smtx_typeof (__eo_to_smt b) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    RuleProofs.eo_has_bool_type
      (mtTangentFormula UserOp.leq UserOp.geq UserOp.leq one zero x y a b) := by
  unfold RuleProofs.eo_has_bool_type
  rw [eo_to_smt_mtTangent_false]
  rcases hT with rfl | rfl
  · simp [smtTangentFormula, __smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
      typeof_eq_eq,
      __smtx_typeof_arith_overload_op_2, __smtx_typeof_arith_overload_op_2_ret,
      hOne, hZero, hX, hY, hA, hB, native_ite, native_Teq]
  · simp [smtTangentFormula, __smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
      typeof_eq_eq,
      __smtx_typeof_arith_overload_op_2, __smtx_typeof_arith_overload_op_2_ret,
      hOne, hZero, hX, hY, hA, hB, native_ite, native_Teq]

private theorem mtTangent_true_int_eval
    (M : SmtModel) (hM : model_wf M) (x y a b : Term)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Int)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Int) :
    __smtx_model_eval M
      (__eo_to_smt
        (mtTangentFormula UserOp.geq UserOp.leq UserOp.geq
          (Term.Numeral 1) (Term.Numeral 0) x y a b)) =
      SmtValue.Boolean true := by
  rcases smt_eval_int_of_type M hM x hX with ⟨xv, hxv⟩
  rcases smt_eval_int_of_type M hM y hY with ⟨yv, hyv⟩
  rcases smt_eval_int_of_type M hM a hA with ⟨av, hav⟩
  rcases smt_eval_int_of_type M hM b hB with ⟨bv, hbv⟩
  rw [eo_to_smt_mtTangent_true_int]
  simpa [smtTangentFormula, __smtx_model_eval, __smtx_model_eval_eq,
    __smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_mult,
    __smtx_model_eval_plus, __smtx_model_eval__, __smtx_model_eval_and,
    __smtx_model_eval_or, native_veq, hxv, hyv, hav, hbv,
    native_zplus, SmtEval.native_zplus, native_zmult, SmtEval.native_zmult,
    native_zneg, SmtEval.native_zneg, native_and, SmtEval.native_and,
    native_or, SmtEval.native_or] using native_z_tangent_geq xv yv av bv

private theorem mtTangent_false_int_eval
    (M : SmtModel) (hM : model_wf M) (x y a b : Term)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Int)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Int) :
    __smtx_model_eval M
      (__eo_to_smt
        (mtTangentFormula UserOp.leq UserOp.geq UserOp.leq
          (Term.Numeral 1) (Term.Numeral 0) x y a b)) =
      SmtValue.Boolean true := by
  rcases smt_eval_int_of_type M hM x hX with ⟨xv, hxv⟩
  rcases smt_eval_int_of_type M hM y hY with ⟨yv, hyv⟩
  rcases smt_eval_int_of_type M hM a hA with ⟨av, hav⟩
  rcases smt_eval_int_of_type M hM b hB with ⟨bv, hbv⟩
  rw [eo_to_smt_mtTangent_false_int]
  simpa [smtTangentFormula, __smtx_model_eval, __smtx_model_eval_eq,
    __smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_mult,
    __smtx_model_eval_plus, __smtx_model_eval__, __smtx_model_eval_and,
    __smtx_model_eval_or, native_veq, hxv, hyv, hav, hbv,
    native_zplus, SmtEval.native_zplus, native_zmult, SmtEval.native_zmult,
    native_zneg, SmtEval.native_zneg, native_and, SmtEval.native_and,
    native_or, SmtEval.native_or] using native_z_tangent_leq xv yv av bv

private theorem mtTangent_true_real_eval
    (M : SmtModel) (hM : model_wf M) (x y a b : Term)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Real)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Real)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Real)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Real) :
    __smtx_model_eval M
      (__eo_to_smt
        (mtTangentFormula UserOp.geq UserOp.leq UserOp.geq
          (Term.Rational (native_mk_rational 1 1))
          (Term.Rational (native_mk_rational 0 1)) x y a b)) =
      SmtValue.Boolean true := by
  rcases smt_eval_real_of_type M hM x hX with ⟨xv, hxv⟩
  rcases smt_eval_real_of_type M hM y hY with ⟨yv, hyv⟩
  rcases smt_eval_real_of_type M hM a hA with ⟨av, hav⟩
  rcases smt_eval_real_of_type M hM b hB with ⟨bv, hbv⟩
  rw [eo_to_smt_mtTangent_true_real]
  simpa [smtTangentFormula, __smtx_model_eval, __smtx_model_eval_eq,
    __smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_mult,
    __smtx_model_eval_plus, __smtx_model_eval__, __smtx_model_eval_and,
    __smtx_model_eval_or, native_veq, hxv, hyv, hav, hbv,
    native_mk_rational_zero, native_mk_rational_one,
    Rat.one_mul, Rat.mul_one, Rat.add_zero,
    native_qplus, SmtEval.native_qplus, native_qmult, SmtEval.native_qmult,
    native_qneg, SmtEval.native_qneg, native_and, SmtEval.native_and,
    native_or, SmtEval.native_or] using native_q_tangent_geq xv yv av bv

private theorem mtTangent_false_real_eval
    (M : SmtModel) (hM : model_wf M) (x y a b : Term)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Real)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Real)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Real)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Real) :
    __smtx_model_eval M
      (__eo_to_smt
        (mtTangentFormula UserOp.leq UserOp.geq UserOp.leq
          (Term.Rational (native_mk_rational 1 1))
          (Term.Rational (native_mk_rational 0 1)) x y a b)) =
      SmtValue.Boolean true := by
  rcases smt_eval_real_of_type M hM x hX with ⟨xv, hxv⟩
  rcases smt_eval_real_of_type M hM y hY with ⟨yv, hyv⟩
  rcases smt_eval_real_of_type M hM a hA with ⟨av, hav⟩
  rcases smt_eval_real_of_type M hM b hB with ⟨bv, hbv⟩
  rw [eo_to_smt_mtTangent_false_real]
  simpa [smtTangentFormula, __smtx_model_eval, __smtx_model_eval_eq,
    __smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_mult,
    __smtx_model_eval_plus, __smtx_model_eval__, __smtx_model_eval_and,
    __smtx_model_eval_or, native_veq, hxv, hyv, hav, hbv,
    native_mk_rational_zero, native_mk_rational_one,
    Rat.one_mul, Rat.mul_one, Rat.add_zero,
    native_qplus, SmtEval.native_qplus, native_qmult, SmtEval.native_qmult,
    native_qneg, SmtEval.native_qneg, native_and, SmtEval.native_and,
    native_or, SmtEval.native_or] using native_q_tangent_leq xv yv av bv

private def mtMkRel (op : UserOp) (u v : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp op) u) v

private def mtTangentMkLeft
    (prodRel : UserOp)
    (oneX oneA oneB zero x y a b : Term) : Term :=
  mtMkRel prodRel
    (mtMkRel UserOp.mult x (mtMkRel UserOp.mult y oneX))
    (mtMkRel UserOp.neg
      (mtMkRel UserOp.plus
        (mtMkRel UserOp.mult b (mtMkRel UserOp.mult x oneB))
        (mtMkRel UserOp.plus
          (mtMkRel UserOp.mult a (mtMkRel UserOp.mult y oneA))
          zero))
      (mtMkRel UserOp.mult a (mtMkRel UserOp.mult b oneA)))

private def mtTangentMkRhs
    (firstYRel secondYRel : UserOp) (x y a b : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.or)
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) a))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and) (mtMkRel firstYRel y b))
          (Term.Boolean true))))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.or)
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) a))
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.and) (mtMkRel secondYRel y b))
            (Term.Boolean true))))
      (Term.Boolean false))

private def mtTangentMkFormula
    (prodRel firstYRel secondYRel : UserOp)
    (x y a b : Term) : Term :=
  let oneA := __eo_nil (Term.UOp UserOp.mult) (__eo_typeof a)
  let oneB := __eo_nil (Term.UOp UserOp.mult) (__eo_typeof b)
  let oneX := __eo_nil (Term.UOp UserOp.mult) (__eo_typeof x)
  let v5 := mtMkRel UserOp.mult b (mtMkRel UserOp.mult x oneB)
  let zero := __eo_nil (Term.UOp UserOp.plus) (__eo_typeof v5)
  mtMkRel UserOp.eq
    (mtTangentMkLeft prodRel oneX oneA oneB zero x y a b)
    (mtTangentMkRhs firstYRel secondYRel x y a b)

private theorem eo_mk_apply_ne_stuck_left {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck -> f ≠ Term.Stuck := by
  intro h hf
  subst f
  simp [__eo_mk_apply] at h

private theorem eo_mk_apply_ne_stuck_right {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck -> x ≠ Term.Stuck := by
  intro h hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem eo_mk_apply_eq_apply_of_ne_stuck
    {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at *

private theorem eo_typeof_mk_binary_eq_of_nonstuck_type
    (op : UserOp) (A B T : Term)
    (hT : T ≠ Term.Stuck)
    (h : __eo_typeof (mtMkRel op A B) = T) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) A) B) = T := by
  have hTopNe : mtMkRel op A B ≠ Term.Stuck := by
    intro hs
    rw [hs] at h
    have hEq : T = Term.Stuck := by
      change Term.Stuck = T at h
      exact h.symm
    exact hT hEq
  unfold mtMkRel at hTopNe h
  have hHeadNe :
      __eo_mk_apply (Term.UOp op) A ≠ Term.Stuck :=
    eo_mk_apply_ne_stuck_left hTopNe
  have hBNe : B ≠ Term.Stuck :=
    eo_mk_apply_ne_stuck_right hTopNe
  have hOpNe : Term.UOp op ≠ Term.Stuck := by
    intro hOp
    cases hOp
  have hANe : A ≠ Term.Stuck :=
    eo_mk_apply_ne_stuck_right hHeadNe
  have hHeadEq :
      __eo_mk_apply (Term.UOp op) A =
        Term.Apply (Term.UOp op) A :=
    eo_mk_apply_eq_apply_of_ne_stuck hOpNe hANe
  have hTopEq :
      __eo_mk_apply (__eo_mk_apply (Term.UOp op) A) B =
        Term.Apply (__eo_mk_apply (Term.UOp op) A) B :=
    eo_mk_apply_eq_apply_of_ne_stuck hHeadNe hBNe
  rw [hTopEq, hHeadEq] at h
  exact h

private theorem eo_typeof_eq_bool_operands_not_stuck_local
    (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · exact ⟨hA, hB⟩

private theorem eo_typeof_mk_eq_left_type_ne_stuck
    (L R : Term)
    (h : __eo_typeof (mtMkRel UserOp.eq L R) = Term.Bool) :
    __eo_typeof L ≠ Term.Stuck := by
  have hDirect :=
    eo_typeof_mk_binary_eq_of_nonstuck_type UserOp.eq L R Term.Bool
      (by native_decide) h
  change __eo_typeof_eq (__eo_typeof L) (__eo_typeof R) = Term.Bool at hDirect
  exact (eo_typeof_eq_bool_operands_not_stuck_local _ _ hDirect).1

private theorem eo_typeof_lt_eq_bool_of_nonstuck
    (A B : Term) :
    __eo_typeof_lt A B ≠ Term.Stuck ->
    __eo_typeof_lt A B = Term.Bool := by
  intro h
  exact RuleProofs.eo_typeof_lt_eq_bool_of_ne_stuck A B h

private theorem eo_typeof_lt_bool_args (A B : Term) :
    __eo_typeof_lt A B = Term.Bool ->
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  intro h
  exact RuleProofs.eo_typeof_lt_bool_cases A B h

private theorem eo_typeof_lt_args_of_nonstuck (A B : Term) :
    __eo_typeof_lt A B ≠ Term.Stuck ->
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  intro h
  exact eo_typeof_lt_bool_args A B (eo_typeof_lt_eq_bool_of_nonstuck A B h)

private theorem eo_typeof_plus_eq_int_args (A B : Term) :
    __eo_typeof_plus A B = Term.UOp UserOp.Int ->
    A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int := by
  intro h
  exact RuleProofs.eo_typeof_plus_int_args A B h

private theorem eo_typeof_plus_eq_real_args (A B : Term) :
    __eo_typeof_plus A B = Term.UOp UserOp.Real ->
    A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real := by
  intro h
  exact RuleProofs.eo_typeof_plus_real_args A B h

private theorem eo_typeof_mk_rel_geq_args_of_nonstuck
    (A B : Term) :
    __eo_typeof (mtMkRel UserOp.geq A B) ≠ Term.Stuck ->
    (__eo_typeof A = Term.UOp UserOp.Int ∧
      __eo_typeof B = Term.UOp UserOp.Int) ∨
    (__eo_typeof A = Term.UOp UserOp.Real ∧
      __eo_typeof B = Term.UOp UserOp.Real) := by
  intro h
  have hDirect :=
    eo_typeof_mk_binary_eq_of_nonstuck_type UserOp.geq A B
      (__eo_typeof (mtMkRel UserOp.geq A B)) h rfl
  have hDirectNN :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) A) B) ≠
        Term.Stuck := by
    rw [hDirect]
    exact h
  change __eo_typeof_lt (__eo_typeof A) (__eo_typeof B) ≠ Term.Stuck at hDirectNN
  exact eo_typeof_lt_args_of_nonstuck (__eo_typeof A) (__eo_typeof B) hDirectNN

private theorem eo_typeof_mk_rel_leq_args_of_nonstuck
    (A B : Term) :
    __eo_typeof (mtMkRel UserOp.leq A B) ≠ Term.Stuck ->
    (__eo_typeof A = Term.UOp UserOp.Int ∧
      __eo_typeof B = Term.UOp UserOp.Int) ∨
    (__eo_typeof A = Term.UOp UserOp.Real ∧
      __eo_typeof B = Term.UOp UserOp.Real) := by
  intro h
  have hDirect :=
    eo_typeof_mk_binary_eq_of_nonstuck_type UserOp.leq A B
      (__eo_typeof (mtMkRel UserOp.leq A B)) h rfl
  have hDirectNN :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) A) B) ≠
        Term.Stuck := by
    rw [hDirect]
    exact h
  change __eo_typeof_lt (__eo_typeof A) (__eo_typeof B) ≠ Term.Stuck at hDirectNN
  exact eo_typeof_lt_args_of_nonstuck (__eo_typeof A) (__eo_typeof B) hDirectNN

private theorem eo_typeof_mk_mult_int_args (A B : Term) :
    __eo_typeof (mtMkRel UserOp.mult A B) = Term.UOp UserOp.Int ->
    __eo_typeof A = Term.UOp UserOp.Int ∧
      __eo_typeof B = Term.UOp UserOp.Int := by
  intro h
  have hDirect :=
    eo_typeof_mk_binary_eq_of_nonstuck_type UserOp.mult A B
      (Term.UOp UserOp.Int) (by native_decide) h
  change __eo_typeof_plus (__eo_typeof A) (__eo_typeof B) =
    Term.UOp UserOp.Int at hDirect
  exact eo_typeof_plus_eq_int_args _ _ hDirect

private theorem eo_typeof_mk_mult_real_args (A B : Term) :
    __eo_typeof (mtMkRel UserOp.mult A B) = Term.UOp UserOp.Real ->
    __eo_typeof A = Term.UOp UserOp.Real ∧
      __eo_typeof B = Term.UOp UserOp.Real := by
  intro h
  have hDirect :=
    eo_typeof_mk_binary_eq_of_nonstuck_type UserOp.mult A B
      (Term.UOp UserOp.Real) (by native_decide) h
  change __eo_typeof_plus (__eo_typeof A) (__eo_typeof B) =
    Term.UOp UserOp.Real at hDirect
  exact eo_typeof_plus_eq_real_args _ _ hDirect

private theorem eo_typeof_mk_neg_int_args (A B : Term) :
    __eo_typeof (mtMkRel UserOp.neg A B) = Term.UOp UserOp.Int ->
    __eo_typeof A = Term.UOp UserOp.Int ∧
      __eo_typeof B = Term.UOp UserOp.Int := by
  intro h
  have hDirect :=
    eo_typeof_mk_binary_eq_of_nonstuck_type UserOp.neg A B
      (Term.UOp UserOp.Int) (by native_decide) h
  change __eo_typeof_plus (__eo_typeof A) (__eo_typeof B) =
    Term.UOp UserOp.Int at hDirect
  exact eo_typeof_plus_eq_int_args _ _ hDirect

private theorem eo_typeof_mk_neg_real_args (A B : Term) :
    __eo_typeof (mtMkRel UserOp.neg A B) = Term.UOp UserOp.Real ->
    __eo_typeof A = Term.UOp UserOp.Real ∧
      __eo_typeof B = Term.UOp UserOp.Real := by
  intro h
  have hDirect :=
    eo_typeof_mk_binary_eq_of_nonstuck_type UserOp.neg A B
      (Term.UOp UserOp.Real) (by native_decide) h
  change __eo_typeof_plus (__eo_typeof A) (__eo_typeof B) =
    Term.UOp UserOp.Real at hDirect
  exact eo_typeof_plus_eq_real_args _ _ hDirect

private theorem mtTangentMkLeft_arg_types_of_nonstuck_geq
    (oneX oneA oneB zero x y a b : Term) :
    __eo_typeof
      (mtTangentMkLeft UserOp.geq oneX oneA oneB zero x y a b) ≠ Term.Stuck ->
    (__eo_typeof x = Term.UOp UserOp.Int ∧
      __eo_typeof y = Term.UOp UserOp.Int ∧
      __eo_typeof a = Term.UOp UserOp.Int ∧
      __eo_typeof b = Term.UOp UserOp.Int) ∨
    (__eo_typeof x = Term.UOp UserOp.Real ∧
      __eo_typeof y = Term.UOp UserOp.Real ∧
      __eo_typeof a = Term.UOp UserOp.Real ∧
      __eo_typeof b = Term.UOp UserOp.Real) := by
  intro h
  unfold mtTangentMkLeft at h
  rcases eo_typeof_mk_rel_geq_args_of_nonstuck _ _ h with hInt | hReal
  · rcases hInt with ⟨hProd, hTangent⟩
    rcases eo_typeof_mk_mult_int_args _ _ hProd with ⟨hx, hYOne⟩
    rcases eo_typeof_mk_mult_int_args _ _ hYOne with ⟨hy, _⟩
    rcases eo_typeof_mk_neg_int_args _ _ hTangent with ⟨_, hAB⟩
    rcases eo_typeof_mk_mult_int_args _ _ hAB with ⟨ha, hBOne⟩
    rcases eo_typeof_mk_mult_int_args _ _ hBOne with ⟨hb, _⟩
    exact Or.inl ⟨hx, hy, ha, hb⟩
  · rcases hReal with ⟨hProd, hTangent⟩
    rcases eo_typeof_mk_mult_real_args _ _ hProd with ⟨hx, hYOne⟩
    rcases eo_typeof_mk_mult_real_args _ _ hYOne with ⟨hy, _⟩
    rcases eo_typeof_mk_neg_real_args _ _ hTangent with ⟨_, hAB⟩
    rcases eo_typeof_mk_mult_real_args _ _ hAB with ⟨ha, hBOne⟩
    rcases eo_typeof_mk_mult_real_args _ _ hBOne with ⟨hb, _⟩
    exact Or.inr ⟨hx, hy, ha, hb⟩

private theorem mtTangentMkLeft_arg_types_of_nonstuck_leq
    (oneX oneA oneB zero x y a b : Term) :
    __eo_typeof
      (mtTangentMkLeft UserOp.leq oneX oneA oneB zero x y a b) ≠ Term.Stuck ->
    (__eo_typeof x = Term.UOp UserOp.Int ∧
      __eo_typeof y = Term.UOp UserOp.Int ∧
      __eo_typeof a = Term.UOp UserOp.Int ∧
      __eo_typeof b = Term.UOp UserOp.Int) ∨
    (__eo_typeof x = Term.UOp UserOp.Real ∧
      __eo_typeof y = Term.UOp UserOp.Real ∧
      __eo_typeof a = Term.UOp UserOp.Real ∧
      __eo_typeof b = Term.UOp UserOp.Real) := by
  intro h
  unfold mtTangentMkLeft at h
  rcases eo_typeof_mk_rel_leq_args_of_nonstuck _ _ h with hInt | hReal
  · rcases hInt with ⟨hProd, hTangent⟩
    rcases eo_typeof_mk_mult_int_args _ _ hProd with ⟨hx, hYOne⟩
    rcases eo_typeof_mk_mult_int_args _ _ hYOne with ⟨hy, _⟩
    rcases eo_typeof_mk_neg_int_args _ _ hTangent with ⟨_, hAB⟩
    rcases eo_typeof_mk_mult_int_args _ _ hAB with ⟨ha, hBOne⟩
    rcases eo_typeof_mk_mult_int_args _ _ hBOne with ⟨hb, _⟩
    exact Or.inl ⟨hx, hy, ha, hb⟩
  · rcases hReal with ⟨hProd, hTangent⟩
    rcases eo_typeof_mk_mult_real_args _ _ hProd with ⟨hx, hYOne⟩
    rcases eo_typeof_mk_mult_real_args _ _ hYOne with ⟨hy, _⟩
    rcases eo_typeof_mk_neg_real_args _ _ hTangent with ⟨_, hAB⟩
    rcases eo_typeof_mk_mult_real_args _ _ hAB with ⟨ha, hBOne⟩
    rcases eo_typeof_mk_mult_real_args _ _ hBOne with ⟨hb, _⟩
    exact Or.inr ⟨hx, hy, ha, hb⟩

private theorem mtTangentMkFormula_arg_types_geq
    (firstYRel secondYRel : UserOp) (x y a b : Term) :
    __eo_typeof
      (mtTangentMkFormula UserOp.geq firstYRel secondYRel x y a b) = Term.Bool ->
    (__eo_typeof x = Term.UOp UserOp.Int ∧
      __eo_typeof y = Term.UOp UserOp.Int ∧
      __eo_typeof a = Term.UOp UserOp.Int ∧
      __eo_typeof b = Term.UOp UserOp.Int) ∨
    (__eo_typeof x = Term.UOp UserOp.Real ∧
      __eo_typeof y = Term.UOp UserOp.Real ∧
      __eo_typeof a = Term.UOp UserOp.Real ∧
      __eo_typeof b = Term.UOp UserOp.Real) := by
  intro h
  unfold mtTangentMkFormula at h
  dsimp at h
  have hLeftNN := eo_typeof_mk_eq_left_type_ne_stuck _ _ h
  exact mtTangentMkLeft_arg_types_of_nonstuck_geq _ _ _ _ _ _ _ _ hLeftNN

private theorem mtTangentMkFormula_arg_types_leq
    (firstYRel secondYRel : UserOp) (x y a b : Term) :
    __eo_typeof
      (mtTangentMkFormula UserOp.leq firstYRel secondYRel x y a b) = Term.Bool ->
    (__eo_typeof x = Term.UOp UserOp.Int ∧
      __eo_typeof y = Term.UOp UserOp.Int ∧
      __eo_typeof a = Term.UOp UserOp.Int ∧
      __eo_typeof b = Term.UOp UserOp.Int) ∨
    (__eo_typeof x = Term.UOp UserOp.Real ∧
      __eo_typeof y = Term.UOp UserOp.Real ∧
      __eo_typeof a = Term.UOp UserOp.Real ∧
      __eo_typeof b = Term.UOp UserOp.Real) := by
  intro h
  unfold mtTangentMkFormula at h
  dsimp at h
  have hLeftNN := eo_typeof_mk_eq_left_type_ne_stuck _ _ h
  exact mtTangentMkLeft_arg_types_of_nonstuck_leq _ _ _ _ _ _ _ _ hLeftNN

private theorem prog_eq_mk_true_of_ne_stuck
    (x y a b : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck)
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_prog_arith_mult_tangent x y a b (Term.Boolean true) =
      mtTangentMkFormula UserOp.geq UserOp.leq UserOp.geq x y a b := by
  unfold __eo_prog_arith_mult_tangent mtTangentMkFormula mtTangentMkLeft
    mtTangentMkRhs mtMkRel
  simp [__eo_mk_apply,__eo_ite, native_ite, native_teq]

private theorem prog_eq_mk_false_of_ne_stuck
    (x y a b : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck)
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_prog_arith_mult_tangent x y a b (Term.Boolean false) =
      mtTangentMkFormula UserOp.leq UserOp.geq UserOp.leq x y a b := by
  unfold __eo_prog_arith_mult_tangent mtTangentMkFormula mtTangentMkLeft
    mtTangentMkRhs mtMkRel
  simp [__eo_mk_apply,__eo_ite, native_ite, native_teq]

private theorem arith_mult_tangent_arg_types_true
    (x y a b : Term)
    (h : __eo_typeof
      (__eo_prog_arith_mult_tangent x y a b (Term.Boolean true)) = Term.Bool) :
    (__eo_typeof x = Term.UOp UserOp.Int ∧
      __eo_typeof y = Term.UOp UserOp.Int ∧
      __eo_typeof a = Term.UOp UserOp.Int ∧
      __eo_typeof b = Term.UOp UserOp.Int) ∨
    (__eo_typeof x = Term.UOp UserOp.Real ∧
      __eo_typeof y = Term.UOp UserOp.Real ∧
      __eo_typeof a = Term.UOp UserOp.Real ∧
      __eo_typeof b = Term.UOp UserOp.Real) := by
  have hx : x ≠ Term.Stuck := by
    intro hs
    subst x
    change Term.Stuck = Term.Bool at h
    cases h
  have hy : y ≠ Term.Stuck := by
    intro hs
    subst y
    have hBad : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_arith_mult_tangent, hx] using h
    change Term.Stuck = Term.Bool at hBad
    cases hBad
  have ha : a ≠ Term.Stuck := by
    intro hs
    subst a
    have hBad : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_arith_mult_tangent, hx, hy] using h
    change Term.Stuck = Term.Bool at hBad
    cases hBad
  have hb : b ≠ Term.Stuck := by
    intro hs
    subst b
    have hBad : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_arith_mult_tangent, hx, hy, ha] using h
    change Term.Stuck = Term.Bool at hBad
    cases hBad
  rw [prog_eq_mk_true_of_ne_stuck x y a b hx hy ha hb] at h
  exact mtTangentMkFormula_arg_types_geq _ _ _ _ _ _ h

private theorem arith_mult_tangent_arg_types_false
    (x y a b : Term)
    (h : __eo_typeof
      (__eo_prog_arith_mult_tangent x y a b (Term.Boolean false)) = Term.Bool) :
    (__eo_typeof x = Term.UOp UserOp.Int ∧
      __eo_typeof y = Term.UOp UserOp.Int ∧
      __eo_typeof a = Term.UOp UserOp.Int ∧
      __eo_typeof b = Term.UOp UserOp.Int) ∨
    (__eo_typeof x = Term.UOp UserOp.Real ∧
      __eo_typeof y = Term.UOp UserOp.Real ∧
      __eo_typeof a = Term.UOp UserOp.Real ∧
      __eo_typeof b = Term.UOp UserOp.Real) := by
  have hx : x ≠ Term.Stuck := by
    intro hs
    subst x
    change Term.Stuck = Term.Bool at h
    cases h
  have hy : y ≠ Term.Stuck := by
    intro hs
    subst y
    have hBad : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_arith_mult_tangent, hx] using h
    change Term.Stuck = Term.Bool at hBad
    cases hBad
  have ha : a ≠ Term.Stuck := by
    intro hs
    subst a
    have hBad : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_arith_mult_tangent, hx, hy] using h
    change Term.Stuck = Term.Bool at hBad
    cases hBad
  have hb : b ≠ Term.Stuck := by
    intro hs
    subst b
    have hBad : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_arith_mult_tangent, hx, hy, ha] using h
    change Term.Stuck = Term.Bool at hBad
    cases hBad
  rw [prog_eq_mk_false_of_ne_stuck x y a b hx hy ha hb] at h
  exact mtTangentMkFormula_arg_types_leq _ _ _ _ _ _ h

private theorem prog_eq_int_true
    (x y a b : Term)
    (hTx : __eo_typeof x = Term.UOp UserOp.Int)
    (hTy : __eo_typeof y = Term.UOp UserOp.Int)
    (hTa : __eo_typeof a = Term.UOp UserOp.Int)
    (hTb : __eo_typeof b = Term.UOp UserOp.Int) :
    __eo_prog_arith_mult_tangent x y a b (Term.Boolean true) =
      mtTangentFormula UserOp.geq UserOp.leq UserOp.geq
        (Term.Numeral 1) (Term.Numeral 0) x y a b := by
  have hxNe : x ≠ Term.Stuck := by intro h; subst x; cases hTx
  have hyNe : y ≠ Term.Stuck := by intro h; subst y; cases hTy
  have haNe : a ≠ Term.Stuck := by intro h; subst a; cases hTa
  have hbNe : b ≠ Term.Stuck := by intro h; subst b; cases hTb
  rw [prog_eq_mk_true_of_ne_stuck x y a b hxNe hyNe haNe hbNe]
  have hx1Ty :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) (Term.Numeral 1)) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_plus (__eo_typeof x) (__eo_typeof (Term.Numeral 1)) =
      Term.UOp UserOp.Int
    rw [hTx]
    native_decide
  have hv5Ty :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) b)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) (Term.Numeral 1))) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_plus (__eo_typeof b)
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) (Term.Numeral 1))) =
        Term.UOp UserOp.Int
    rw [hTb, hx1Ty]
    native_decide
  simp [mtTangentFormula, mtRel, mtMul, mtPlus, mtSub, mtAnd, mtOr,
    mtTangentMkFormula, mtTangentMkLeft, mtTangentMkRhs, mtMkRel, __eo_mk_apply,
    __eo_nil, __eo_nil_mult, __eo_nil_plus, __arith_mk_one, __arith_mk_zero,
    hv5Ty, hTx,hTa, hTb]

private theorem prog_eq_int_false
    (x y a b : Term)
    (hTx : __eo_typeof x = Term.UOp UserOp.Int)
    (hTy : __eo_typeof y = Term.UOp UserOp.Int)
    (hTa : __eo_typeof a = Term.UOp UserOp.Int)
    (hTb : __eo_typeof b = Term.UOp UserOp.Int) :
    __eo_prog_arith_mult_tangent x y a b (Term.Boolean false) =
      mtTangentFormula UserOp.leq UserOp.geq UserOp.leq
        (Term.Numeral 1) (Term.Numeral 0) x y a b := by
  have hxNe : x ≠ Term.Stuck := by intro h; subst x; cases hTx
  have hyNe : y ≠ Term.Stuck := by intro h; subst y; cases hTy
  have haNe : a ≠ Term.Stuck := by intro h; subst a; cases hTa
  have hbNe : b ≠ Term.Stuck := by intro h; subst b; cases hTb
  rw [prog_eq_mk_false_of_ne_stuck x y a b hxNe hyNe haNe hbNe]
  have hx1Ty :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) (Term.Numeral 1)) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_plus (__eo_typeof x) (__eo_typeof (Term.Numeral 1)) =
      Term.UOp UserOp.Int
    rw [hTx]
    native_decide
  have hv5Ty :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) b)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) (Term.Numeral 1))) =
        Term.UOp UserOp.Int := by
    change __eo_typeof_plus (__eo_typeof b)
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) (Term.Numeral 1))) =
        Term.UOp UserOp.Int
    rw [hTb, hx1Ty]
    native_decide
  simp [mtTangentFormula, mtRel, mtMul, mtPlus, mtSub, mtAnd, mtOr,
    mtTangentMkFormula, mtTangentMkLeft, mtTangentMkRhs, mtMkRel, __eo_mk_apply,
    __eo_nil, __eo_nil_mult, __eo_nil_plus, __arith_mk_one, __arith_mk_zero,
    hv5Ty, hTx,hTa, hTb]

private theorem prog_eq_real_true
    (x y a b : Term)
    (hTx : __eo_typeof x = Term.UOp UserOp.Real)
    (hTy : __eo_typeof y = Term.UOp UserOp.Real)
    (hTa : __eo_typeof a = Term.UOp UserOp.Real)
    (hTb : __eo_typeof b = Term.UOp UserOp.Real) :
    __eo_prog_arith_mult_tangent x y a b (Term.Boolean true) =
      mtTangentFormula UserOp.geq UserOp.leq UserOp.geq
        (Term.Rational (native_mk_rational 1 1))
        (Term.Rational (native_mk_rational 0 1)) x y a b := by
  have hxNe : x ≠ Term.Stuck := by intro h; subst x; cases hTx
  have hyNe : y ≠ Term.Stuck := by intro h; subst y; cases hTy
  have haNe : a ≠ Term.Stuck := by intro h; subst a; cases hTa
  have hbNe : b ≠ Term.Stuck := by intro h; subst b; cases hTb
  rw [prog_eq_mk_true_of_ne_stuck x y a b hxNe hyNe haNe hbNe]
  have hx1Ty :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x)
          (Term.Rational (native_mk_rational 1 1))) =
        Term.UOp UserOp.Real := by
    change __eo_typeof_plus (__eo_typeof x)
      (__eo_typeof (Term.Rational (native_mk_rational 1 1))) =
      Term.UOp UserOp.Real
    rw [hTx]
    native_decide
  have hv5Ty :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) b)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x)
            (Term.Rational (native_mk_rational 1 1)))) =
        Term.UOp UserOp.Real := by
    change __eo_typeof_plus (__eo_typeof b)
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x)
        (Term.Rational (native_mk_rational 1 1)))) =
        Term.UOp UserOp.Real
    rw [hTb, hx1Ty]
    native_decide
  simp [mtTangentFormula, mtRel, mtMul, mtPlus, mtSub, mtAnd, mtOr,
    mtTangentMkFormula, mtTangentMkLeft, mtTangentMkRhs, mtMkRel, __eo_mk_apply,
    __eo_nil, __eo_nil_mult, __eo_nil_plus, __arith_mk_one, __arith_mk_zero,
    hv5Ty, hTx,hTa, hTb]

private theorem prog_eq_real_false
    (x y a b : Term)
    (hTx : __eo_typeof x = Term.UOp UserOp.Real)
    (hTy : __eo_typeof y = Term.UOp UserOp.Real)
    (hTa : __eo_typeof a = Term.UOp UserOp.Real)
    (hTb : __eo_typeof b = Term.UOp UserOp.Real) :
    __eo_prog_arith_mult_tangent x y a b (Term.Boolean false) =
      mtTangentFormula UserOp.leq UserOp.geq UserOp.leq
        (Term.Rational (native_mk_rational 1 1))
        (Term.Rational (native_mk_rational 0 1)) x y a b := by
  have hxNe : x ≠ Term.Stuck := by intro h; subst x; cases hTx
  have hyNe : y ≠ Term.Stuck := by intro h; subst y; cases hTy
  have haNe : a ≠ Term.Stuck := by intro h; subst a; cases hTa
  have hbNe : b ≠ Term.Stuck := by intro h; subst b; cases hTb
  rw [prog_eq_mk_false_of_ne_stuck x y a b hxNe hyNe haNe hbNe]
  have hx1Ty :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x)
          (Term.Rational (native_mk_rational 1 1))) =
        Term.UOp UserOp.Real := by
    change __eo_typeof_plus (__eo_typeof x)
      (__eo_typeof (Term.Rational (native_mk_rational 1 1))) =
      Term.UOp UserOp.Real
    rw [hTx]
    native_decide
  have hv5Ty :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) b)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x)
            (Term.Rational (native_mk_rational 1 1)))) =
        Term.UOp UserOp.Real := by
    change __eo_typeof_plus (__eo_typeof b)
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x)
        (Term.Rational (native_mk_rational 1 1)))) =
        Term.UOp UserOp.Real
    rw [hTb, hx1Ty]
    native_decide
  simp [mtTangentFormula, mtRel, mtMul, mtPlus, mtSub, mtAnd, mtOr,
    mtTangentMkFormula, mtTangentMkLeft, mtTangentMkRhs, mtMkRel, __eo_mk_apply,
    __eo_nil, __eo_nil_mult, __eo_nil_plus, __arith_mk_one, __arith_mk_zero,
    hv5Ty, hTx,hTa, hTb]

private theorem tangent_true_int_properties
    (M : SmtModel) (hM : model_wf M) (x y a b : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hBTrans : RuleProofs.eo_has_smt_translation b)
    (hTx : __eo_typeof x = Term.UOp UserOp.Int)
    (hTy : __eo_typeof y = Term.UOp UserOp.Int)
    (hTa : __eo_typeof a = Term.UOp UserOp.Int)
    (hTb : __eo_typeof b = Term.UOp UserOp.Int) :
    StepRuleProperties M []
      (__eo_prog_arith_mult_tangent x y a b (Term.Boolean true)) := by
  have hProg := prog_eq_int_true x y a b hTx hTy hTa hTb
  have hXSmt := smt_type_int_of_eo_type x hXTrans hTx
  have hYSmt := smt_type_int_of_eo_type y hYTrans hTy
  have hASmt := smt_type_int_of_eo_type a hATrans hTa
  have hBSmt := smt_type_int_of_eo_type b hBTrans hTb
  have hBool :
      RuleProofs.eo_has_bool_type
        (mtTangentFormula UserOp.geq UserOp.leq UserOp.geq
          (Term.Numeral 1) (Term.Numeral 0) x y a b) := by
    exact mtTangent_true_has_bool_type_of_smt_type
      (Term.Numeral 1) (Term.Numeral 0) x y a b SmtType.Int
      (by native_decide) (by native_decide) hXSmt hYSmt hASmt hBSmt (Or.inl rfl)
  have hEval := mtTangent_true_int_eval M hM x y a b hXSmt hYSmt hASmt hBSmt
  rw [hProg]
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool⟩
  intro _hTrue
  exact RuleProofs.eo_interprets_of_bool_eval M _ true hBool hEval

private theorem tangent_false_int_properties
    (M : SmtModel) (hM : model_wf M) (x y a b : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hBTrans : RuleProofs.eo_has_smt_translation b)
    (hTx : __eo_typeof x = Term.UOp UserOp.Int)
    (hTy : __eo_typeof y = Term.UOp UserOp.Int)
    (hTa : __eo_typeof a = Term.UOp UserOp.Int)
    (hTb : __eo_typeof b = Term.UOp UserOp.Int) :
    StepRuleProperties M []
      (__eo_prog_arith_mult_tangent x y a b (Term.Boolean false)) := by
  have hProg := prog_eq_int_false x y a b hTx hTy hTa hTb
  have hXSmt := smt_type_int_of_eo_type x hXTrans hTx
  have hYSmt := smt_type_int_of_eo_type y hYTrans hTy
  have hASmt := smt_type_int_of_eo_type a hATrans hTa
  have hBSmt := smt_type_int_of_eo_type b hBTrans hTb
  have hBool :
      RuleProofs.eo_has_bool_type
        (mtTangentFormula UserOp.leq UserOp.geq UserOp.leq
          (Term.Numeral 1) (Term.Numeral 0) x y a b) := by
    exact mtTangent_false_has_bool_type_of_smt_type
      (Term.Numeral 1) (Term.Numeral 0) x y a b SmtType.Int
      (by native_decide) (by native_decide) hXSmt hYSmt hASmt hBSmt (Or.inl rfl)
  have hEval := mtTangent_false_int_eval M hM x y a b hXSmt hYSmt hASmt hBSmt
  rw [hProg]
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool⟩
  intro _hTrue
  exact RuleProofs.eo_interprets_of_bool_eval M _ true hBool hEval

private theorem tangent_true_real_properties
    (M : SmtModel) (hM : model_wf M) (x y a b : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hBTrans : RuleProofs.eo_has_smt_translation b)
    (hTx : __eo_typeof x = Term.UOp UserOp.Real)
    (hTy : __eo_typeof y = Term.UOp UserOp.Real)
    (hTa : __eo_typeof a = Term.UOp UserOp.Real)
    (hTb : __eo_typeof b = Term.UOp UserOp.Real) :
    StepRuleProperties M []
      (__eo_prog_arith_mult_tangent x y a b (Term.Boolean true)) := by
  have hProg := prog_eq_real_true x y a b hTx hTy hTa hTb
  have hXSmt := smt_type_real_of_eo_type x hXTrans hTx
  have hYSmt := smt_type_real_of_eo_type y hYTrans hTy
  have hASmt := smt_type_real_of_eo_type a hATrans hTa
  have hBSmt := smt_type_real_of_eo_type b hBTrans hTb
  have hBool :
      RuleProofs.eo_has_bool_type
        (mtTangentFormula UserOp.geq UserOp.leq UserOp.geq
          (Term.Rational (native_mk_rational 1 1))
          (Term.Rational (native_mk_rational 0 1)) x y a b) := by
    exact mtTangent_true_has_bool_type_of_smt_type
      (Term.Rational (native_mk_rational 1 1))
      (Term.Rational (native_mk_rational 0 1)) x y a b SmtType.Real
      (by native_decide) (by native_decide) hXSmt hYSmt hASmt hBSmt (Or.inr rfl)
  have hEval := mtTangent_true_real_eval M hM x y a b hXSmt hYSmt hASmt hBSmt
  rw [hProg]
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool⟩
  intro _hTrue
  exact RuleProofs.eo_interprets_of_bool_eval M _ true hBool hEval

private theorem tangent_false_real_properties
    (M : SmtModel) (hM : model_wf M) (x y a b : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hBTrans : RuleProofs.eo_has_smt_translation b)
    (hTx : __eo_typeof x = Term.UOp UserOp.Real)
    (hTy : __eo_typeof y = Term.UOp UserOp.Real)
    (hTa : __eo_typeof a = Term.UOp UserOp.Real)
    (hTb : __eo_typeof b = Term.UOp UserOp.Real) :
    StepRuleProperties M []
      (__eo_prog_arith_mult_tangent x y a b (Term.Boolean false)) := by
  have hProg := prog_eq_real_false x y a b hTx hTy hTa hTb
  have hXSmt := smt_type_real_of_eo_type x hXTrans hTx
  have hYSmt := smt_type_real_of_eo_type y hYTrans hTy
  have hASmt := smt_type_real_of_eo_type a hATrans hTa
  have hBSmt := smt_type_real_of_eo_type b hBTrans hTb
  have hBool :
      RuleProofs.eo_has_bool_type
        (mtTangentFormula UserOp.leq UserOp.geq UserOp.leq
          (Term.Rational (native_mk_rational 1 1))
          (Term.Rational (native_mk_rational 0 1)) x y a b) := by
    exact mtTangent_false_has_bool_type_of_smt_type
      (Term.Rational (native_mk_rational 1 1))
      (Term.Rational (native_mk_rational 0 1)) x y a b SmtType.Real
      (by native_decide) (by native_decide) hXSmt hYSmt hASmt hBSmt (Or.inr rfl)
  have hEval := mtTangent_false_real_eval M hM x y a b hXSmt hYSmt hASmt hBSmt
  rw [hProg]
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool⟩
  intro _hTrue
  exact RuleProofs.eo_interprets_of_bool_eval M _ true hBool hEval

public theorem cmd_step_arith_mult_tangent_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_tangent args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_mult_tangent args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_tangent args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_mult_tangent args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons x args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons y args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons b args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons pol args =>
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
                              change __eo_prog_arith_mult_tangent x y a b pol ≠
                                Term.Stuck at hProg
                              change __eo_typeof
                                (__eo_prog_arith_mult_tangent x y a b pol) =
                                  Term.Bool at hResultTy
                              have hArgsTrans :
                                  cArgListTranslationOk
                                    (CArgList.cons x
                                      (CArgList.cons y
                                        (CArgList.cons a
                                          (CArgList.cons b
                                            (CArgList.cons pol CArgList.nil))))) := by
                                simpa [cmdTranslationOk] using hCmdTrans
                              have hXTrans : RuleProofs.eo_has_smt_translation x := by
                                simpa [cArgListTranslationOk,
                                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                                  using hArgsTrans.1
                              have hYTrans : RuleProofs.eo_has_smt_translation y := by
                                simpa [cArgListTranslationOk,
                                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                                  using hArgsTrans.2.1
                              have hATrans : RuleProofs.eo_has_smt_translation a := by
                                simpa [cArgListTranslationOk,
                                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                                  using hArgsTrans.2.2.1
                              have hBTrans : RuleProofs.eo_has_smt_translation b := by
                                simpa [cArgListTranslationOk,
                                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                                  using hArgsTrans.2.2.2.1
                              have hxNe : x ≠ Term.Stuck := by
                                intro hx
                                subst x
                                exact hProg rfl
                              have hyNe : y ≠ Term.Stuck := by
                                intro hy
                                subst y
                                apply hProg
                                simp [__eo_prog_arith_mult_tangent]
                              have haNe : a ≠ Term.Stuck := by
                                intro ha
                                subst a
                                apply hProg
                                simp [__eo_prog_arith_mult_tangent]
                              have hbNe : b ≠ Term.Stuck := by
                                intro hb
                                subst b
                                apply hProg
                                simp [__eo_prog_arith_mult_tangent]
                              cases pol with
                              | Boolean sign =>
                                  cases sign with
                                  | false =>
                                      have hTypes :=
                                        arith_mult_tangent_arg_types_false x y a b
                                          hResultTy
                                      rcases hTypes with hTypes | hTypes
                                      · rcases hTypes with ⟨hTx, hTy, hTa, hTb⟩
                                        change StepRuleProperties M []
                                          (__eo_prog_arith_mult_tangent x y a b
                                            (Term.Boolean false))
                                        exact tangent_false_int_properties M hM x y a b
                                          hXTrans hYTrans hATrans hBTrans
                                          hTx hTy hTa hTb
                                      · rcases hTypes with ⟨hTx, hTy, hTa, hTb⟩
                                        change StepRuleProperties M []
                                          (__eo_prog_arith_mult_tangent x y a b
                                            (Term.Boolean false))
                                        exact tangent_false_real_properties M hM x y a b
                                          hXTrans hYTrans hATrans hBTrans
                                          hTx hTy hTa hTb
                                  | true =>
                                      have hTypes :=
                                        arith_mult_tangent_arg_types_true x y a b
                                          hResultTy
                                      rcases hTypes with hTypes | hTypes
                                      · rcases hTypes with ⟨hTx, hTy, hTa, hTb⟩
                                        change StepRuleProperties M []
                                          (__eo_prog_arith_mult_tangent x y a b
                                            (Term.Boolean true))
                                        exact tangent_true_int_properties M hM x y a b
                                          hXTrans hYTrans hATrans hBTrans
                                          hTx hTy hTa hTb
                                      · rcases hTypes with ⟨hTx, hTy, hTa, hTb⟩
                                        change StepRuleProperties M []
                                          (__eo_prog_arith_mult_tangent x y a b
                                            (Term.Boolean true))
                                        exact tangent_true_real_properties M hM x y a b
                                          hXTrans hYTrans hATrans hBTrans
                                          hTx hTy hTa hTb
                              | _ =>
                                  exfalso
                                  apply hProg
                                  simp [__eo_prog_arith_mult_tangent, __eo_ite,
                                    __eo_mk_apply,native_ite, native_teq]
