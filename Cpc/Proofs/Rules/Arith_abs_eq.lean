module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithAbsEq

private abbrev absTerm (t : Term) : Term :=
  Term.Apply Term.abs t

private abbrev negTerm (t : Term) : Term :=
  Term.Apply Term.__eoo_neg_2 t

private abbrev eqTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply Term.eq a) b

private abbrev orTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply Term.or a) b

private abbrev rhsTerm (x y : Term) : Term :=
  orTerm (eqTerm x y) (orTerm (eqTerm x (negTerm y)) (Term.Boolean false))

private abbrev resultTerm (x y : Term) : Term :=
  eqTerm (eqTerm (absTerm x) (absTerm y)) (rhsTerm x y)

private theorem eval_abs (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.abs a) =
      __smtx_model_eval_abs (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_uneg (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.uneg a) =
      __smtx_model_eval_uneg (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem prog_eq_of_nonstuck (x y : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_prog_arith_abs_eq x y = resultTerm x y := by
  by_cases hxSt : x = Term.Stuck
  · exact False.elim (hx hxSt)
  by_cases hySt : y = Term.Stuck
  · exact False.elim (hy hySt)
  cases x <;> cases y <;>
    first
      | exact False.elim (hx rfl)
      | exact False.elim (hy rfl)
      | rfl

private theorem arg_types
    (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hResultTy : __eo_typeof (__eo_prog_arith_abs_eq x y) = Term.Bool) :
    (__eo_typeof x = Term.Int ∧ __eo_typeof y = Term.Int) ∨
      (__eo_typeof x = Term.Real ∧ __eo_typeof y = Term.Real) := by
  have hx : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hy : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  rw [prog_eq_of_nonstuck x y hx hy] at hResultTy
  change __eo_typeof_eq (__eo_typeof (eqTerm (absTerm x) (absTerm y)))
      (__eo_typeof (rhsTerm x y)) = Term.Bool at hResultTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof (absTerm x)) (__eo_typeof (absTerm y)))
      (__eo_typeof_or (__eo_typeof (eqTerm x y))
        (__eo_typeof (orTerm (eqTerm x (negTerm y)) (Term.Boolean false)))) =
        Term.Bool at hResultTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof_abs (__eo_typeof x))
        (__eo_typeof_abs (__eo_typeof y)))
      (__eo_typeof_or (__eo_typeof_eq (__eo_typeof x) (__eo_typeof y))
        (__eo_typeof_or (__eo_typeof (eqTerm x (negTerm y)))
          (__eo_typeof (Term.Boolean false)))) = Term.Bool at hResultTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof_abs (__eo_typeof x))
        (__eo_typeof_abs (__eo_typeof y)))
      (__eo_typeof_or (__eo_typeof_eq (__eo_typeof x) (__eo_typeof y))
        (__eo_typeof_or (__eo_typeof_eq (__eo_typeof x) (__eo_typeof (negTerm y)))
          (__eo_typeof (Term.Boolean false)))) = Term.Bool at hResultTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof_abs (__eo_typeof x))
        (__eo_typeof_abs (__eo_typeof y)))
      (__eo_typeof_or (__eo_typeof_eq (__eo_typeof x) (__eo_typeof y))
        (__eo_typeof_or
          (__eo_typeof_eq (__eo_typeof x) (__eo_typeof_abs (__eo_typeof y)))
          Term.Bool)) = Term.Bool at hResultTy
  cases hxTy : __eo_typeof x with
  | UOp opx =>
      cases opx <;>
        simp [__eo_typeof_eq, __eo_typeof_or, __eo_typeof_abs,
          __eo_requires, __is_arith_type, __eo_eq, native_ite,
          native_teq, native_not, SmtEval.native_not, hxTy] at hResultTy ⊢
      case Int =>
        cases hyTy : __eo_typeof y with
        | UOp opy =>
            cases opy <;>
              simp [__eo_typeof_eq, __eo_typeof_or, __eo_typeof_abs,
                __eo_requires, __is_arith_type, __eo_eq, native_ite,
                native_teq, native_not, SmtEval.native_not, hxTy, hyTy]
                at hResultTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_or, __eo_typeof_abs,
              __eo_requires, __is_arith_type, __eo_eq, native_ite,
              native_teq, native_not, SmtEval.native_not, hxTy, hyTy]
              at hResultTy
      case Real =>
        cases hyTy : __eo_typeof y with
        | UOp opy =>
            cases opy <;>
              simp [__eo_typeof_eq, __eo_typeof_or, __eo_typeof_abs,
                __eo_requires, __is_arith_type, __eo_eq, native_ite,
                native_teq, native_not, SmtEval.native_not, hxTy, hyTy]
                at hResultTy ⊢
        | _ =>
            simp [__eo_typeof_eq, __eo_typeof_or, __eo_typeof_abs,
              __eo_requires, __is_arith_type, __eo_eq, native_ite,
              native_teq, native_not, SmtEval.native_not, hxTy, hyTy]
              at hResultTy
  | _ =>
      simp [__eo_typeof_eq, __eo_typeof_or, __eo_typeof_abs,
        __eo_requires, __is_arith_type, __eo_eq, native_ite,
        native_teq, native_not, SmtEval.native_not, hxTy] at hResultTy

private theorem smt_of_eo_type
    (t ty : Term) (smtTy : SmtType)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof t = ty)
    (hTyMap : __eo_to_smt_type ty = smtTy) :
    __smtx_typeof (__eo_to_smt t) = smtTy := by
  have h := TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    t ty (__eo_to_smt t) rfl hTrans hTy
  simpa [hTyMap] using h

private theorem smt_int_of_eo_int (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof t = Term.Int) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  exact smt_of_eo_type t Term.Int SmtType.Int hTrans hTy rfl

private theorem smt_real_of_eo_real (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof t = Term.Real) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
  exact smt_of_eo_type t Term.Real SmtType.Real hTrans hTy rfl

private theorem smt_abs_int (t : Term)
    (hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Int := by
  rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl]
  rw [typeof_abs_eq, hSmt]
  simp [__smtx_typeof_arith_overload_op_1]

private theorem smt_abs_real (t : Term)
    (hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Real := by
  rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl]
  rw [typeof_abs_eq, hSmt]
  simp [__smtx_typeof_arith_overload_op_1]

private theorem smt_neg_int (t : Term)
    (hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (negTerm t)) = SmtType.Int := by
  rw [show __eo_to_smt (negTerm t) = SmtTerm.uneg (__eo_to_smt t) by rfl]
  rw [typeof_uneg_eq, hSmt]
  simp [__smtx_typeof_arith_overload_op_1]

private theorem smt_neg_real (t : Term)
    (hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt (negTerm t)) = SmtType.Real := by
  rw [show __eo_to_smt (negTerm t) = SmtTerm.uneg (__eo_to_smt t) by rfl]
  rw [typeof_uneg_eq, hSmt]
  simp [__smtx_typeof_arith_overload_op_1]

private theorem smt_or_bool (a b : Term)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Bool)
    (hb : __smtx_typeof (__eo_to_smt b) = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt (orTerm a b)) = SmtType.Bool := by
  rw [show __eo_to_smt (orTerm a b) =
      SmtTerm.or (__eo_to_smt a) (__eo_to_smt b) by rfl]
  rw [typeof_or_eq, ha, hb]
  simp [native_Teq, native_ite]

private theorem false_smt_bool :
    __smtx_typeof (__eo_to_smt (Term.Boolean false)) = SmtType.Bool := by
  change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
  rw [__smtx_typeof.eq_1]

private theorem eq_bool_of_same_type (a b : Term) (ty : SmtType)
    (ha : __smtx_typeof (__eo_to_smt a) = ty)
    (hb : __smtx_typeof (__eo_to_smt b) = ty)
    (hNonNone : ty ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (eqTerm a b)) = SmtType.Bool := by
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
    (by rw [ha, hb]) (by rw [ha]; exact hNonNone)

private theorem typed_result_of_smt_type
    (x y : Term) (ty : SmtType)
    (hxSmt : __smtx_typeof (__eo_to_smt x) = ty)
    (hySmt : __smtx_typeof (__eo_to_smt y) = ty)
    (hAbsX : __smtx_typeof (__eo_to_smt (absTerm x)) = ty)
    (hAbsY : __smtx_typeof (__eo_to_smt (absTerm y)) = ty)
    (hNegY : __smtx_typeof (__eo_to_smt (negTerm y)) = ty)
    (hNonNone : ty ≠ SmtType.None) :
    RuleProofs.eo_has_bool_type (resultTerm x y) := by
  have hAbsEq : __smtx_typeof (__eo_to_smt (eqTerm (absTerm x) (absTerm y))) =
      SmtType.Bool :=
    eq_bool_of_same_type (absTerm x) (absTerm y) ty hAbsX hAbsY hNonNone
  have hEqXY :
      __smtx_typeof (__eo_to_smt (eqTerm x y)) = SmtType.Bool :=
    eq_bool_of_same_type x y ty hxSmt hySmt hNonNone
  have hEqXNegY :
      __smtx_typeof (__eo_to_smt (eqTerm x (negTerm y))) = SmtType.Bool :=
    eq_bool_of_same_type x (negTerm y) ty hxSmt hNegY hNonNone
  have hOrTail :
      __smtx_typeof
        (__eo_to_smt (orTerm (eqTerm x (negTerm y)) (Term.Boolean false))) =
        SmtType.Bool :=
    smt_or_bool (eqTerm x (negTerm y)) (Term.Boolean false)
      hEqXNegY false_smt_bool
  have hRhs : __smtx_typeof (__eo_to_smt (rhsTerm x y)) = SmtType.Bool :=
    smt_or_bool (eqTerm x y)
      (orTerm (eqTerm x (negTerm y)) (Term.Boolean false)) hEqXY hOrTail
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (eqTerm (absTerm x) (absTerm y)) (rhsTerm x y)
    (by rw [hAbsEq, hRhs]) (by rw [hAbsEq]; decide)

private theorem typed_result_int (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hxTy : __eo_typeof x = Term.Int)
    (hyTy : __eo_typeof y = Term.Int) :
    RuleProofs.eo_has_bool_type (resultTerm x y) := by
  have hxSmt := smt_int_of_eo_int x hxTrans hxTy
  have hySmt := smt_int_of_eo_int y hyTrans hyTy
  exact typed_result_of_smt_type x y SmtType.Int hxSmt hySmt
    (smt_abs_int x hxSmt) (smt_abs_int y hySmt) (smt_neg_int y hySmt)
    (by decide)

private theorem typed_result_real (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hxTy : __eo_typeof x = Term.Real)
    (hyTy : __eo_typeof y = Term.Real) :
    RuleProofs.eo_has_bool_type (resultTerm x y) := by
  have hxSmt := smt_real_of_eo_real x hxTrans hxTy
  have hySmt := smt_real_of_eo_real y hyTrans hyTy
  exact typed_result_of_smt_type x y SmtType.Real hxSmt hySmt
    (smt_abs_real x hxSmt) (smt_abs_real y hySmt) (smt_neg_real y hySmt)
    (by decide)

private theorem typed___eo_prog_arith_abs_eq_impl
    (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (__eo_prog_arith_abs_eq x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_arith_abs_eq x y) := by
  intro hxTrans hyTrans hResultTy
  have hx : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hy : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  have hProgEq := prog_eq_of_nonstuck x y hx hy
  rcases arg_types x y hxTrans hyTrans hResultTy with hInt | hReal
  · rw [hProgEq]
    exact typed_result_int x y hxTrans hyTrans hInt.1 hInt.2
  · rw [hProgEq]
    exact typed_result_real x y hxTrans hyTrans hReal.1 hReal.2

private theorem eval_abs_int (M : SmtModel) (x : Term) (n : native_Int)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral n) :
    __smtx_model_eval M (__eo_to_smt (absTerm x)) =
      SmtValue.Numeral (if n < 0 then native_zneg n else n) := by
  rw [show __eo_to_smt (absTerm x) = SmtTerm.abs (__eo_to_smt x) by rfl]
  rw [eval_abs, hx]
  simp [__smtx_model_eval_abs, native_zabs, native_zneg]

private theorem eval_abs_real (M : SmtModel) (x : Term) (q : native_Rat)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Rational q) :
    __smtx_model_eval M (__eo_to_smt (absTerm x)) =
      SmtValue.Rational (if q < 0 then native_qneg q else q) := by
  rw [show __eo_to_smt (absTerm x) = SmtTerm.abs (__eo_to_smt x) by rfl]
  rw [eval_abs, hx]
  simp [__smtx_model_eval_abs, native_qabs, native_qneg]

private theorem eval_neg_int (M : SmtModel) (x : Term) (n : native_Int)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral n) :
    __smtx_model_eval M (__eo_to_smt (negTerm x)) =
      SmtValue.Numeral (native_zneg n) := by
  rw [show __eo_to_smt (negTerm x) = SmtTerm.uneg (__eo_to_smt x) by rfl]
  rw [eval_uneg, hx]
  simp [__smtx_model_eval_uneg]

private theorem eval_neg_real (M : SmtModel) (x : Term) (q : native_Rat)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Rational q) :
    __smtx_model_eval M (__eo_to_smt (negTerm x)) =
      SmtValue.Rational (native_qneg q) := by
  rw [show __eo_to_smt (negTerm x) = SmtTerm.uneg (__eo_to_smt x) by rfl]
  rw [eval_uneg, hx]
  simp [__smtx_model_eval_uneg]

private theorem eval_false (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
      SmtValue.Boolean false := by
  change __smtx_model_eval M (SmtTerm.Boolean false) = SmtValue.Boolean false
  rw [__smtx_model_eval.eq_1]

private theorem int_abs_eq_bool (x y : native_Int) :
    native_zeq (if x < 0 then native_zneg x else x)
      (if y < 0 then native_zneg y else y) =
    native_or (native_zeq x y)
      (native_or (native_zeq x (native_zneg y)) false) := by
  unfold native_zeq native_or native_zneg
  grind

private theorem real_abs_eq_bool (x y : native_Rat) :
    native_qeq (if x < 0 then native_qneg x else x)
      (if y < 0 then native_qneg y else y) =
    native_or (native_qeq x y)
      (native_or (native_qeq x (native_qneg y)) false) := by
  unfold native_qeq native_or native_qneg
  grind

private theorem eval_result_int
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hxTy : __eo_typeof x = Term.Int)
    (hyTy : __eo_typeof y = Term.Int) :
    __smtx_model_eval M (__eo_to_smt (resultTerm x y)) =
      SmtValue.Boolean true := by
  have hxSmt := smt_int_of_eo_int x hxTrans hxTy
  have hySmt := smt_int_of_eo_int y hyTrans hyTy
  have hxEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt x) SmtType.Int hxSmt
      (by simp) type_inhabited_int
  have hyEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt y) SmtType.Int hySmt
      (by simp) type_inhabited_int
  rcases int_value_canonical hxEvalTy with ⟨xi, hxEval⟩
  rcases int_value_canonical hyEvalTy with ⟨yi, hyEval⟩
  have hxAbs := eval_abs_int M x xi hxEval
  have hyAbs := eval_abs_int M y yi hyEval
  have hyNeg := eval_neg_int M y yi hyEval
  have hEqAbs :
      __smtx_model_eval M (__eo_to_smt (eqTerm (absTerm x) (absTerm y))) =
        SmtValue.Boolean
          (native_zeq (if xi < 0 then native_zneg xi else xi)
            (if yi < 0 then native_zneg yi else yi)) := by
    rw [show __eo_to_smt (eqTerm (absTerm x) (absTerm y)) =
        SmtTerm.eq (__eo_to_smt (absTerm x)) (__eo_to_smt (absTerm y)) by rfl]
    rw [smtx_eval_eq_term_eq, hxAbs, hyAbs]
    simp [__smtx_model_eval_eq, native_veq, native_zeq]
  have hEqXY :
      __smtx_model_eval M (__eo_to_smt (eqTerm x y)) =
        SmtValue.Boolean (native_zeq xi yi) := by
    rw [show __eo_to_smt (eqTerm x y) =
        SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) by rfl]
    rw [smtx_eval_eq_term_eq, hxEval, hyEval]
    simp [__smtx_model_eval_eq, native_veq, native_zeq]
  have hEqXNegY :
      __smtx_model_eval M (__eo_to_smt (eqTerm x (negTerm y))) =
        SmtValue.Boolean (native_zeq xi (native_zneg yi)) := by
    rw [show __eo_to_smt (eqTerm x (negTerm y)) =
        SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (negTerm y)) by rfl]
    rw [smtx_eval_eq_term_eq, hxEval, hyNeg]
    simp [__smtx_model_eval_eq, native_veq, native_zeq]
  have hOrTail :
      __smtx_model_eval M
          (__eo_to_smt (orTerm (eqTerm x (negTerm y)) (Term.Boolean false))) =
        SmtValue.Boolean (native_or (native_zeq xi (native_zneg yi)) false) := by
    rw [show __eo_to_smt (orTerm (eqTerm x (negTerm y)) (Term.Boolean false)) =
        SmtTerm.or (__eo_to_smt (eqTerm x (negTerm y)))
          (__eo_to_smt (Term.Boolean false)) by rfl]
    rw [smtx_eval_or_term_eq, hEqXNegY, eval_false]
    simp [__smtx_model_eval_or]
  have hRhs :
      __smtx_model_eval M (__eo_to_smt (rhsTerm x y)) =
        SmtValue.Boolean
          (native_or (native_zeq xi yi)
            (native_or (native_zeq xi (native_zneg yi)) false)) := by
    rw [show __eo_to_smt (rhsTerm x y) =
        SmtTerm.or (__eo_to_smt (eqTerm x y))
          (__eo_to_smt (orTerm (eqTerm x (negTerm y)) (Term.Boolean false))) by rfl]
    rw [smtx_eval_or_term_eq, hEqXY, hOrTail]
    simp [__smtx_model_eval_or]
  rw [show __eo_to_smt (resultTerm x y) =
      SmtTerm.eq (__eo_to_smt (eqTerm (absTerm x) (absTerm y)))
        (__eo_to_smt (rhsTerm x y)) by rfl]
  rw [smtx_eval_eq_term_eq, hEqAbs, hRhs]
  rw [int_abs_eq_bool xi yi]
  simp [__smtx_model_eval_eq, native_veq]

private theorem eval_result_real
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hxTy : __eo_typeof x = Term.Real)
    (hyTy : __eo_typeof y = Term.Real) :
    __smtx_model_eval M (__eo_to_smt (resultTerm x y)) =
      SmtValue.Boolean true := by
  have hxSmt := smt_real_of_eo_real x hxTrans hxTy
  have hySmt := smt_real_of_eo_real y hyTrans hyTy
  have hxEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Real :=
    smt_model_eval_preserves_type M hM (__eo_to_smt x) SmtType.Real hxSmt
      (by simp) type_inhabited_real
  have hyEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Real :=
    smt_model_eval_preserves_type M hM (__eo_to_smt y) SmtType.Real hySmt
      (by simp) type_inhabited_real
  rcases real_value_canonical hxEvalTy with ⟨xq, hxEval⟩
  rcases real_value_canonical hyEvalTy with ⟨yq, hyEval⟩
  have hxAbs := eval_abs_real M x xq hxEval
  have hyAbs := eval_abs_real M y yq hyEval
  have hyNeg := eval_neg_real M y yq hyEval
  have hEqAbs :
      __smtx_model_eval M (__eo_to_smt (eqTerm (absTerm x) (absTerm y))) =
        SmtValue.Boolean
          (native_qeq (if xq < 0 then native_qneg xq else xq)
            (if yq < 0 then native_qneg yq else yq)) := by
    rw [show __eo_to_smt (eqTerm (absTerm x) (absTerm y)) =
        SmtTerm.eq (__eo_to_smt (absTerm x)) (__eo_to_smt (absTerm y)) by rfl]
    rw [smtx_eval_eq_term_eq, hxAbs, hyAbs]
    simp [__smtx_model_eval_eq, native_veq, native_qeq]
  have hEqXY :
      __smtx_model_eval M (__eo_to_smt (eqTerm x y)) =
        SmtValue.Boolean (native_qeq xq yq) := by
    rw [show __eo_to_smt (eqTerm x y) =
        SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) by rfl]
    rw [smtx_eval_eq_term_eq, hxEval, hyEval]
    simp [__smtx_model_eval_eq, native_veq, native_qeq]
  have hEqXNegY :
      __smtx_model_eval M (__eo_to_smt (eqTerm x (negTerm y))) =
        SmtValue.Boolean (native_qeq xq (native_qneg yq)) := by
    rw [show __eo_to_smt (eqTerm x (negTerm y)) =
        SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (negTerm y)) by rfl]
    rw [smtx_eval_eq_term_eq, hxEval, hyNeg]
    simp [__smtx_model_eval_eq, native_veq, native_qeq]
  have hOrTail :
      __smtx_model_eval M
          (__eo_to_smt (orTerm (eqTerm x (negTerm y)) (Term.Boolean false))) =
        SmtValue.Boolean (native_or (native_qeq xq (native_qneg yq)) false) := by
    rw [show __eo_to_smt (orTerm (eqTerm x (negTerm y)) (Term.Boolean false)) =
        SmtTerm.or (__eo_to_smt (eqTerm x (negTerm y)))
          (__eo_to_smt (Term.Boolean false)) by rfl]
    rw [smtx_eval_or_term_eq, hEqXNegY, eval_false]
    simp [__smtx_model_eval_or]
  have hRhs :
      __smtx_model_eval M (__eo_to_smt (rhsTerm x y)) =
        SmtValue.Boolean
          (native_or (native_qeq xq yq)
            (native_or (native_qeq xq (native_qneg yq)) false)) := by
    rw [show __eo_to_smt (rhsTerm x y) =
        SmtTerm.or (__eo_to_smt (eqTerm x y))
          (__eo_to_smt (orTerm (eqTerm x (negTerm y)) (Term.Boolean false))) by rfl]
    rw [smtx_eval_or_term_eq, hEqXY, hOrTail]
    simp [__smtx_model_eval_or]
  rw [show __eo_to_smt (resultTerm x y) =
      SmtTerm.eq (__eo_to_smt (eqTerm (absTerm x) (absTerm y)))
        (__eo_to_smt (rhsTerm x y)) by rfl]
  rw [smtx_eval_eq_term_eq, hEqAbs, hRhs]
  rw [real_abs_eq_bool xq yq]
  simp [__smtx_model_eval_eq, native_veq]

private theorem facts___eo_prog_arith_abs_eq_impl
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (__eo_prog_arith_abs_eq x y) = Term.Bool ->
    eo_interprets M (__eo_prog_arith_abs_eq x y) true := by
  intro hxTrans hyTrans hResultTy
  have hx : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  have hy : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hyTrans
  have hProgEq := prog_eq_of_nonstuck x y hx hy
  have hBool :
      RuleProofs.eo_has_bool_type (__eo_prog_arith_abs_eq x y) :=
    typed___eo_prog_arith_abs_eq_impl x y hxTrans hyTrans hResultTy
  rcases arg_types x y hxTrans hyTrans hResultTy with hInt | hReal
  · rw [hProgEq] at hBool ⊢
    exact RuleProofs.eo_interprets_of_bool_eval M (resultTerm x y) true
      hBool (eval_result_int M hM x y hxTrans hyTrans hInt.1 hInt.2)
  · rw [hProgEq] at hBool ⊢
    exact RuleProofs.eo_interprets_of_bool_eval M (resultTerm x y) true
      hBool (eval_result_real M hM x y hxTrans hyTrans hReal.1 hReal.2)

end ArithAbsEq

open ArithAbsEq in
public theorem cmd_step_arith_abs_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_abs_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_abs_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_abs_eq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_abs_eq args premises ≠ Term.Stuck :=
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
                  let X1 := a1
                  let Y1 := a2
                  have hArgsTrans :
                      cArgListTranslationOk
                        (CArgList.cons X1 (CArgList.cons Y1 CArgList.nil)) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  have hXTrans : RuleProofs.eo_has_smt_translation X1 := by
                    simpa [cArgListTranslationOk] using hArgsTrans.1
                  have hYTrans : RuleProofs.eo_has_smt_translation Y1 := by
                    simpa [cArgListTranslationOk] using hArgsTrans.2
                  change __eo_typeof (__eo_prog_arith_abs_eq X1 Y1) =
                    Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hPremTrue
                    change eo_interprets M (__eo_prog_arith_abs_eq X1 Y1) true
                    exact facts___eo_prog_arith_abs_eq_impl M hM X1 Y1
                      hXTrans hYTrans hResultTy
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arith_abs_eq X1 Y1)
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                      (__eo_prog_arith_abs_eq X1 Y1)
                      (typed___eo_prog_arith_abs_eq_impl X1 Y1
                        hXTrans hYTrans hResultTy)
