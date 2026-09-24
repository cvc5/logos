module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace IntTightSupport

private theorem eo_to_smt_lt_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) =
      SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_leq_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) =
      SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_gt_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) =
      SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_geq_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b) =
      SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_numeral_eq (n : native_Int) :
    __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n := by
  rfl

private theorem eo_to_smt_rational_eq (q : native_Rat) :
    __eo_to_smt (Term.Rational q) = SmtTerm.Rational q := by
  rfl

private theorem eo_to_smt_string_eq (s : native_String) :
    __eo_to_smt (Term.String s) = SmtTerm.String s := by
  rfl

private theorem eo_to_smt_binary_eq (w n : native_Int) :
    __eo_to_smt (Term.Binary w n) = SmtTerm.Binary w n := by
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

private theorem lt_args_of_has_bool_type (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) ->
    (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.Real) := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy
  rw [eo_to_smt_lt_eq a b, typeof_lt_eq] at hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [typeof_lt_eq, hTy]
    simp
  exact arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt)
    (typeof_lt_eq (__eo_to_smt a) (__eo_to_smt b)) hNN

private theorem gt_args_of_has_bool_type (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) ->
    (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.Real) := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy
  rw [eo_to_smt_gt_eq a b, typeof_gt_eq] at hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [typeof_gt_eq, hTy]
    simp
  exact arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt)
    (typeof_gt_eq (__eo_to_smt a) (__eo_to_smt b)) hNN

private theorem smt_left_non_none_of_arith_args
    {a b : Term}
    (hArgs :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
  rcases hArgs with hInt | hReal
  · simp [hInt.1]
  · simp [hReal.1]

private theorem eo_typeof_left_int_of_leq_numeral_bool
    {a : Term} {n : native_Int}
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) (Term.Numeral n)) =
        Term.Bool) :
    __eo_typeof a = Term.UOp UserOp.Int := by
  change __eo_typeof_lt (__eo_typeof a) (Term.UOp UserOp.Int) = Term.Bool at hTy
  cases hA : __eo_typeof a <;>
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      native_ite, native_teq, native_not, hA] at hTy
  case UOp op =>
    cases op <;>
      simp at hTy
    rfl

private theorem eo_typeof_left_int_of_geq_numeral_bool
    {a : Term} {n : native_Int}
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) (Term.Numeral n)) =
        Term.Bool) :
    __eo_typeof a = Term.UOp UserOp.Int := by
  change __eo_typeof_lt (__eo_typeof a) (Term.UOp UserOp.Int) = Term.Bool at hTy
  cases hA : __eo_typeof a <;>
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      native_ite, native_teq, native_not, hA] at hTy
  case UOp op =>
    cases op <;>
      simp at hTy
    rfl

private theorem smt_type_left_int_of_leq_numeral_bool
    {a : Term} {n : native_Int}
    (hNonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None)
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) (Term.Numeral n)) =
        Term.Bool) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hEoTy : __eo_typeof a = Term.UOp UserOp.Int :=
    eo_typeof_left_int_of_leq_numeral_bool hTy
  have hSmtTy :
      __smtx_typeof (__eo_to_smt a) =
        __eo_to_smt_type (Term.UOp UserOp.Int) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      a (Term.UOp UserOp.Int) (__eo_to_smt a) rfl hNonNone hEoTy
  simpa [__eo_to_smt_type] using hSmtTy

private theorem smt_type_left_int_of_geq_numeral_bool
    {a : Term} {n : native_Int}
    (hNonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None)
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) (Term.Numeral n)) =
        Term.Bool) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hEoTy : __eo_typeof a = Term.UOp UserOp.Int :=
    eo_typeof_left_int_of_geq_numeral_bool hTy
  have hSmtTy :
      __smtx_typeof (__eo_to_smt a) =
        __eo_to_smt_type (Term.UOp UserOp.Int) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      a (Term.UOp UserOp.Int) (__eo_to_smt a) rfl hNonNone hEoTy
  simpa [__eo_to_smt_type] using hSmtTy

private theorem smt_right_int_of_left_int
    {a b : Term}
    (hLeft : __smtx_typeof (__eo_to_smt a) = SmtType.Int)
    (hArgs :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    __smtx_typeof (__eo_to_smt b) = SmtType.Int := by
  rcases hArgs with hInt | hReal
  · exact hInt.2
  · have hContra : SmtType.Real = SmtType.Int := hReal.1.symm.trans hLeft
    cases hContra

private theorem leq_numeral_has_bool_type
    {a : Term} {n : native_Int}
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Int) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) (Term.Numeral n)) := by
  unfold RuleProofs.eo_has_bool_type
  rw [eo_to_smt_leq_eq a (Term.Numeral n), typeof_leq_eq]
  rw [eo_to_smt_numeral_eq n, __smtx_typeof.eq_2]
  simp [__smtx_typeof_arith_overload_op_2_ret, hA]

private theorem geq_numeral_has_bool_type
    {a : Term} {n : native_Int}
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Int) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) (Term.Numeral n)) := by
  unfold RuleProofs.eo_has_bool_type
  rw [eo_to_smt_geq_eq a (Term.Numeral n), typeof_geq_eq]
  rw [eo_to_smt_numeral_eq n, __smtx_typeof.eq_2]
  simp [__smtx_typeof_arith_overload_op_2_ret, hA]

theorem int_tight_ub_interprets_numeral
    (M : SmtModel) (hM : model_wf M)
    (a : Term) (n : native_Int)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) (Term.Numeral n)))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
          (__greatest_int_lt (Term.Numeral n))) = Term.Bool)
    (hPremTrue :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) (Term.Numeral n)) true) :
      eo_interprets M
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
        (__greatest_int_lt (Term.Numeral n))) true := by
  have hArgs := lt_args_of_has_bool_type a (Term.Numeral n) hPremBool
  have hANonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    smt_left_non_none_of_arith_args hArgs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a)
          (Term.Numeral (native_zplus (-1 : native_Int) n))) = Term.Bool := by
    simpa [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq, __eo_add,
      __eo_ite, __eo_mk_apply, native_ite, native_teq, native_not,
      native_to_real, SmtEval.native_to_real, native_mk_rational,
      SmtEval.native_mk_rational] using hResultTy
  have hAInt :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
    smt_type_left_int_of_leq_numeral_bool hANonNone hResultTy'
  rcases smt_eval_int_of_type M hM a hAInt with ⟨m, hEvalA⟩
  have hLtBool : native_zlt m n = true := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_lt_eq] at hPremTrue
    cases hPremTrue with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_17, hEvalA, eo_to_smt_numeral_eq n,
          __smtx_model_eval.eq_2] at hEval
        simp [__smtx_model_eval_lt] at hEval
        exact hEval
  have hLt : m < n := by
    simpa [native_zlt, SmtEval.native_zlt] using hLtBool
  have hLe : m ≤ native_zplus (-1 : native_Int) n := by
    have hLe' : m ≤ n - 1 := Int.le_sub_one_of_lt hLt
    change m ≤ (-1 : Int) + n
    simpa [Int.sub_eq_add_neg, Int.add_comm] using hLe'
  have hConclusionBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a)
          (Term.Numeral (native_zplus (-1 : native_Int) n))) :=
    leq_numeral_has_bool_type hAInt
  apply RuleProofs.eo_interprets_of_bool_eval M
  · simpa [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq, __eo_add,
      __eo_ite, __eo_mk_apply, native_ite, native_teq, native_not,
      native_to_real, SmtEval.native_to_real, native_mk_rational,
      SmtEval.native_mk_rational] using hConclusionBool
  · have hTight :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
            (__greatest_int_lt (Term.Numeral n)) =
          Term.Apply (Term.Apply (Term.UOp UserOp.leq) a)
            (Term.Numeral (native_zplus (-1 : native_Int) n)) := by
      simp [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq, __eo_add,
        __eo_ite, __eo_mk_apply, native_ite, native_teq,
        native_to_real, SmtEval.native_to_real, native_mk_rational,
        SmtEval.native_mk_rational]
    rw [hTight, eo_to_smt_leq_eq, eo_to_smt_numeral_eq, __smtx_model_eval.eq_18,
      hEvalA, __smtx_model_eval.eq_2]
    simp [__smtx_model_eval_leq, native_zleq, SmtEval.native_zleq, hLe]

theorem int_tight_ub_has_smt_translation_numeral
    (a : Term) (n : native_Int)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) (Term.Numeral n)))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
          (__greatest_int_lt (Term.Numeral n))) = Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
        (__greatest_int_lt (Term.Numeral n))) := by
  have hArgs := lt_args_of_has_bool_type a (Term.Numeral n) hPremBool
  have hANonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    smt_left_non_none_of_arith_args hArgs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a)
          (Term.Numeral (native_zplus (-1 : native_Int) n))) = Term.Bool := by
    simpa [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq, __eo_add,
      __eo_ite, __eo_mk_apply, native_ite, native_teq, native_not,
      native_to_real, SmtEval.native_to_real, native_mk_rational,
      SmtEval.native_mk_rational] using hResultTy
  have hAInt :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
    smt_type_left_int_of_leq_numeral_bool hANonNone hResultTy'
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ <|
    by
      simpa [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq, __eo_add,
        __eo_ite, __eo_mk_apply, native_ite, native_teq, native_not,
        native_to_real, SmtEval.native_to_real, native_mk_rational,
        SmtEval.native_mk_rational] using
        (leq_numeral_has_bool_type (a := a)
          (n := native_zplus (-1 : native_Int) n) hAInt)

theorem int_tight_lb_interprets_numeral
    (M : SmtModel) (hM : model_wf M)
    (a : Term) (n : native_Int)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) (Term.Numeral n)))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
          (__least_int_gt (Term.Numeral n))) = Term.Bool)
    (hPremTrue :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) (Term.Numeral n)) true) :
    eo_interprets M
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
        (__least_int_gt (Term.Numeral n))) true := by
  have hArgs := gt_args_of_has_bool_type a (Term.Numeral n) hPremBool
  have hANonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    smt_left_non_none_of_arith_args hArgs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a)
          (Term.Numeral (native_zplus (1 : native_Int) n))) = Term.Bool := by
    simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply] using hResultTy
  have hAInt :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
    smt_type_left_int_of_geq_numeral_bool hANonNone hResultTy'
  rcases smt_eval_int_of_type M hM a hAInt with ⟨m, hEvalA⟩
  have hLtBool : native_zlt n m = true := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_gt_eq] at hPremTrue
    cases hPremTrue with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_19, hEvalA, eo_to_smt_numeral_eq n,
          __smtx_model_eval.eq_2] at hEval
        simp [__smtx_model_eval_gt, __smtx_model_eval_lt] at hEval
        exact hEval
  have hLt : n < m := by
    simpa [native_zlt, SmtEval.native_zlt] using hLtBool
  have hLe : native_zplus (1 : native_Int) n ≤ m := by
    have hLe' : n + 1 ≤ m := Int.add_one_le_iff.mpr hLt
    change (1 : Int) + n ≤ m
    simpa [Int.add_comm] using hLe'
  have hConclusionBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a)
          (Term.Numeral (native_zplus (1 : native_Int) n))) :=
    geq_numeral_has_bool_type hAInt
  apply RuleProofs.eo_interprets_of_bool_eval M
  · simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply] using hConclusionBool
  · have hTight :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
            (__least_int_gt (Term.Numeral n)) =
          Term.Apply (Term.Apply (Term.UOp UserOp.geq) a)
            (Term.Numeral (native_zplus (1 : native_Int) n)) := by
      simp [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply]
    rw [hTight, eo_to_smt_geq_eq, eo_to_smt_numeral_eq, __smtx_model_eval.eq_20,
      hEvalA, __smtx_model_eval.eq_2]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, native_zleq,
      SmtEval.native_zleq, hLe]

theorem int_tight_lb_has_smt_translation_numeral
    (a : Term) (n : native_Int)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) (Term.Numeral n)))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
          (__least_int_gt (Term.Numeral n))) = Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
        (__least_int_gt (Term.Numeral n))) := by
  have hArgs := gt_args_of_has_bool_type a (Term.Numeral n) hPremBool
  have hANonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    smt_left_non_none_of_arith_args hArgs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a)
          (Term.Numeral (native_zplus (1 : native_Int) n))) = Term.Bool := by
    simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply] using hResultTy
  have hAInt :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
    smt_type_left_int_of_geq_numeral_bool hANonNone hResultTy'
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ <|
    by
      simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply] using
        (geq_numeral_has_bool_type (a := a)
          (n := native_zplus (1 : native_Int) n) hAInt)

private theorem false_of_typeof_stuck_bool {P : Prop}
    (hTy : __eo_typeof Term.Stuck = Term.Bool) : P := by
  have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
    native_decide
  exact False.elim (hBad hTy)

private theorem false_of_rational_lt_tight_ub
    {a : Term} {q : native_Rat}
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) (Term.Rational q)))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
          (__greatest_int_lt (Term.Rational q))) = Term.Bool) :
    False := by
  have hArgs := lt_args_of_has_bool_type a (Term.Rational q) hPremBool
  have hANonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    smt_left_non_none_of_arith_args hArgs
  by_cases hWhole : native_to_real (native_to_int q) = q
  · have hResultTy' :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a)
            (Term.Numeral (native_zplus (-1 : native_Int) (native_to_int q)))) =
          Term.Bool := by
      simpa [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq, __eo_add,
        __eo_ite, __eo_mk_apply, native_ite, native_teq, native_not, hWhole] using
        hResultTy
    have hAInt :
        __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
      smt_type_left_int_of_leq_numeral_bool hANonNone hResultTy'
    have hBInt :
        __smtx_typeof (__eo_to_smt (Term.Rational q)) = SmtType.Int :=
      smt_right_int_of_left_int hAInt hArgs
    rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3] at hBInt
    cases hBInt
  · have hResultTy' :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a)
            (Term.Numeral (native_to_int q))) = Term.Bool := by
      simp [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq,
        __eo_ite, __eo_mk_apply, native_ite, native_teq, hWhole] at hResultTy
      simpa using hResultTy
    have hAInt :
        __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
      smt_type_left_int_of_leq_numeral_bool hANonNone hResultTy'
    have hBInt :
        __smtx_typeof (__eo_to_smt (Term.Rational q)) = SmtType.Int :=
      smt_right_int_of_left_int hAInt hArgs
    rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3] at hBInt
    cases hBInt

private theorem false_of_rational_gt_tight_lb
    {a : Term} {q : native_Rat}
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) (Term.Rational q)))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
          (__least_int_gt (Term.Rational q))) = Term.Bool) :
    False := by
  have hArgs := gt_args_of_has_bool_type a (Term.Rational q) hPremBool
  have hANonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    smt_left_non_none_of_arith_args hArgs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a)
          (Term.Numeral (native_zplus (1 : native_Int) (native_to_int q)))) =
        Term.Bool := by
    simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply] using hResultTy
  have hAInt :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
    smt_type_left_int_of_geq_numeral_bool hANonNone hResultTy'
  have hBInt :
      __smtx_typeof (__eo_to_smt (Term.Rational q)) = SmtType.Int :=
    smt_right_int_of_left_int hAInt hArgs
  rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3] at hBInt
  cases hBInt

private theorem false_of_string_gt_tight_lb
    {a : Term} {str : native_String}
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) (Term.String str)))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
          (__least_int_gt (Term.String str))) = Term.Bool) :
    False := by
  have hArgs := gt_args_of_has_bool_type a (Term.String str) hPremBool
  have hANonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    smt_left_non_none_of_arith_args hArgs
  by_cases hLen : native_zeq 1 (native_str_len str) = true
  · have hResultTy' :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a)
            (Term.Numeral (native_zplus (1 : native_Int) (native_str_to_code str)))) =
          Term.Bool := by
      simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply, native_ite, hLen] using
        hResultTy
    have hAInt :
        __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
      smt_type_left_int_of_geq_numeral_bool hANonNone hResultTy'
    have hBInt :
        __smtx_typeof (__eo_to_smt (Term.String str)) = SmtType.Int :=
      smt_right_int_of_left_int hAInt hArgs
    rw [eo_to_smt_string_eq, __smtx_typeof.eq_4] at hBInt
    cases hValid : native_string_valid str <;>
      simp [native_ite, hValid] at hBInt
  · have hStuck :
        __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply, native_ite, hLen] using
        hResultTy
    exact false_of_typeof_stuck_bool hStuck

private theorem false_of_binary_gt_tight_lb
    {a : Term} {w n : native_Int}
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) (Term.Binary w n)))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
          (__least_int_gt (Term.Binary w n))) = Term.Bool) :
    False := by
  have hArgs := gt_args_of_has_bool_type a (Term.Binary w n) hPremBool
  have hANonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    smt_left_non_none_of_arith_args hArgs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a)
          (Term.Numeral (native_zplus (1 : native_Int) n))) =
        Term.Bool := by
    simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply] using hResultTy
  have hAInt :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int :=
    smt_type_left_int_of_geq_numeral_bool hANonNone hResultTy'
  have hBInt :
      __smtx_typeof (__eo_to_smt (Term.Binary w n)) = SmtType.Int :=
    smt_right_int_of_left_int hAInt hArgs
  rw [eo_to_smt_binary_eq, __smtx_typeof.eq_5] at hBInt
  cases hBinTy :
      native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
    simp [native_ite, hBinTy] at hBInt

theorem int_tight_ub_interprets
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
          (__greatest_int_lt b)) = Term.Bool)
    (hPremTrue :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) true) :
    eo_interprets M
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
        (__greatest_int_lt b)) true := by
  cases b <;>
    try
      exact false_of_typeof_stuck_bool (by
        simpa [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq, __eo_add,
          __eo_ite, __eo_mk_apply, native_ite, native_teq, native_not] using hResultTy)
  case Numeral n =>
    exact int_tight_ub_interprets_numeral M hM a n hPremBool hResultTy hPremTrue
  case Rational q =>
    exact False.elim (false_of_rational_lt_tight_ub hPremBool hResultTy)

theorem int_tight_ub_has_smt_translation
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
          (__greatest_int_lt b)) = Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
        (__greatest_int_lt b)) := by
  cases b <;>
    try
      exact false_of_typeof_stuck_bool (by
        simpa [__greatest_int_lt, __eo_to_z, __eo_to_q, __eo_eq, __eo_add,
          __eo_ite, __eo_mk_apply, native_ite, native_teq, native_not] using hResultTy)
  case Numeral n =>
    exact int_tight_ub_has_smt_translation_numeral a n hPremBool hResultTy
  case Rational q =>
    exact False.elim (false_of_rational_lt_tight_ub hPremBool hResultTy)

theorem int_tight_lb_interprets
    (M : SmtModel) (hM : model_wf M)
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
          (__least_int_gt b)) = Term.Bool)
    (hPremTrue :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) true) :
    eo_interprets M
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
        (__least_int_gt b)) true := by
  cases b <;>
    try
      exact false_of_typeof_stuck_bool (by
        simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply, native_ite] using
          hResultTy)
  case Numeral n =>
    exact int_tight_lb_interprets_numeral M hM a n hPremBool hResultTy hPremTrue
  case Rational q =>
    exact False.elim (false_of_rational_gt_tight_lb hPremBool hResultTy)
  case String str =>
    exact False.elim (false_of_string_gt_tight_lb hPremBool hResultTy)
  case Binary w n =>
    exact False.elim (false_of_binary_gt_tight_lb hPremBool hResultTy)

theorem int_tight_lb_has_smt_translation
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b))
    (hResultTy :
      __eo_typeof
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
          (__least_int_gt b)) = Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
        (__least_int_gt b)) := by
  cases b <;>
    try
      exact false_of_typeof_stuck_bool (by
        simpa [__least_int_gt, __eo_to_z, __eo_add, __eo_mk_apply, native_ite] using
          hResultTy)
  case Numeral n =>
    exact int_tight_lb_has_smt_translation_numeral a n hPremBool hResultTy
  case Rational q =>
    exact False.elim (false_of_rational_gt_tight_lb hPremBool hResultTy)
  case String str =>
    exact False.elim (false_of_string_gt_tight_lb hPremBool hResultTy)
  case Binary w n =>
    exact False.elim (false_of_binary_gt_tight_lb hPremBool hResultTy)

theorem int_tight_ub_prog_interprets
    (M : SmtModel) (hM : model_wf M)
    (P : Term)
    (hPremBool : RuleProofs.eo_has_bool_type P)
    (hResultTy : __eo_typeof (__eo_prog_int_tight_ub (Proof.pf P)) = Term.Bool)
    (hPremTrue : eo_interprets M P true) :
    eo_interprets M (__eo_prog_int_tight_ub (Proof.pf P)) true := by
  cases P <;>
    try
      exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_ub] using hResultTy)
  case Apply f b =>
    cases f <;>
      try
        exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_ub] using hResultTy)
    case Apply g a =>
      cases g <;>
        try
          exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_ub] using hResultTy)
      case UOp op =>
        cases op <;>
          try
            exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_ub] using hResultTy)
        case lt =>
          have hResultTy' :
              __eo_typeof
                (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
                  (__greatest_int_lt b)) = Term.Bool := by
            simpa [__eo_prog_int_tight_ub] using hResultTy
          simpa [__eo_prog_int_tight_ub] using
            int_tight_ub_interprets M hM a b hPremBool hResultTy' hPremTrue

theorem int_tight_ub_prog_has_smt_translation
    (P : Term)
    (hPremBool : RuleProofs.eo_has_bool_type P)
    (hResultTy : __eo_typeof (__eo_prog_int_tight_ub (Proof.pf P)) = Term.Bool) :
    RuleProofs.eo_has_smt_translation (__eo_prog_int_tight_ub (Proof.pf P)) := by
  cases P <;>
    try
      exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_ub] using hResultTy)
  case Apply f b =>
    cases f <;>
      try
        exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_ub] using hResultTy)
    case Apply g a =>
      cases g <;>
        try
          exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_ub] using hResultTy)
      case UOp op =>
        cases op <;>
          try
            exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_ub] using hResultTy)
        case lt =>
          have hResultTy' :
              __eo_typeof
                (__eo_mk_apply (Term.Apply (Term.UOp UserOp.leq) a)
                  (__greatest_int_lt b)) = Term.Bool := by
            simpa [__eo_prog_int_tight_ub] using hResultTy
          simpa [__eo_prog_int_tight_ub] using
            int_tight_ub_has_smt_translation a b hPremBool hResultTy'

theorem int_tight_lb_prog_interprets
    (M : SmtModel) (hM : model_wf M)
    (P : Term)
    (hPremBool : RuleProofs.eo_has_bool_type P)
    (hResultTy : __eo_typeof (__eo_prog_int_tight_lb (Proof.pf P)) = Term.Bool)
    (hPremTrue : eo_interprets M P true) :
    eo_interprets M (__eo_prog_int_tight_lb (Proof.pf P)) true := by
  cases P <;>
    try
      exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_lb] using hResultTy)
  case Apply f b =>
    cases f <;>
      try
        exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_lb] using hResultTy)
    case Apply g a =>
      cases g <;>
        try
          exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_lb] using hResultTy)
      case UOp op =>
        cases op <;>
          try
            exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_lb] using hResultTy)
        case gt =>
          have hResultTy' :
              __eo_typeof
                (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
                  (__least_int_gt b)) = Term.Bool := by
            simpa [__eo_prog_int_tight_lb] using hResultTy
          simpa [__eo_prog_int_tight_lb] using
            int_tight_lb_interprets M hM a b hPremBool hResultTy' hPremTrue

theorem int_tight_lb_prog_has_smt_translation
    (P : Term)
    (hPremBool : RuleProofs.eo_has_bool_type P)
    (hResultTy : __eo_typeof (__eo_prog_int_tight_lb (Proof.pf P)) = Term.Bool) :
    RuleProofs.eo_has_smt_translation (__eo_prog_int_tight_lb (Proof.pf P)) := by
  cases P <;>
    try
      exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_lb] using hResultTy)
  case Apply f b =>
    cases f <;>
      try
        exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_lb] using hResultTy)
    case Apply g a =>
      cases g <;>
        try
          exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_lb] using hResultTy)
      case UOp op =>
        cases op <;>
          try
            exact false_of_typeof_stuck_bool (by simpa [__eo_prog_int_tight_lb] using hResultTy)
        case gt =>
          have hResultTy' :
              __eo_typeof
                (__eo_mk_apply (Term.Apply (Term.UOp UserOp.geq) a)
                  (__least_int_gt b)) = Term.Bool := by
            simpa [__eo_prog_int_tight_lb] using hResultTy
          simpa [__eo_prog_int_tight_lb] using
            int_tight_lb_has_smt_translation a b hPremBool hResultTy'

end IntTightSupport
