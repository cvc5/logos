module

public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_plus_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) =
      SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_lt_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) =
      SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_leq_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) =
      SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_eq_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
      SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem arith_sum_lt_args_of_bool (a1 b1 a2 b2 : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) ->
    (__smtx_typeof (__eo_to_smt a1) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt b1) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt a2) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt b2) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt a1) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt b1) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt a2) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt b2) = SmtType.Real) := by
  intro hTy
  have hTy' :
      __smtx_typeof
        (SmtTerm.lt
          (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2))
          (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2))) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eo_to_smt_lt_eq, eo_to_smt_plus_eq] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.lt
          (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2))
          (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2))) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt)
      (typeof_lt_eq
        (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2))
        (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2))) hNN with hOut | hOut
  · have hLeftNN :
        term_has_non_none_type (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2)) := by
      unfold term_has_non_none_type
      rw [hOut.1]
      simp
    have hRightNN :
        term_has_non_none_type (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2)) := by
      unfold term_has_non_none_type
      rw [hOut.2]
      simp
    rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
        (typeof_plus_eq (__eo_to_smt a1) (__eo_to_smt a2)) hLeftNN with hLeft | hLeft
    · rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
          (typeof_plus_eq (__eo_to_smt b1) (__eo_to_smt b2)) hRightNN with hRight | hRight
      · exact Or.inl ⟨hLeft.1, hRight.1, hLeft.2, hRight.2⟩
      · have hRightTy :
            __smtx_typeof (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2)) =
              SmtType.Real := by
          rw [typeof_plus_eq]
          simp [__smtx_typeof_arith_overload_op_2, hRight.1, hRight.2]
        rw [hRightTy] at hOut
        cases hOut.2
    · have hLeftTy :
          __smtx_typeof (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2)) =
            SmtType.Real := by
        rw [typeof_plus_eq]
        simp [__smtx_typeof_arith_overload_op_2, hLeft.1, hLeft.2]
      rw [hLeftTy] at hOut
      cases hOut.1
  · have hLeftNN :
        term_has_non_none_type (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2)) := by
      unfold term_has_non_none_type
      rw [hOut.1]
      simp
    have hRightNN :
        term_has_non_none_type (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2)) := by
      unfold term_has_non_none_type
      rw [hOut.2]
      simp
    rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
        (typeof_plus_eq (__eo_to_smt a1) (__eo_to_smt a2)) hLeftNN with hLeft | hLeft
    · have hLeftTy :
          __smtx_typeof (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2)) =
            SmtType.Int := by
        rw [typeof_plus_eq]
        simp [__smtx_typeof_arith_overload_op_2, hLeft.1, hLeft.2]
      rw [hLeftTy] at hOut
      cases hOut.1
    · rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
          (typeof_plus_eq (__eo_to_smt b1) (__eo_to_smt b2)) hRightNN with hRight | hRight
      · have hRightTy :
            __smtx_typeof (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2)) =
              SmtType.Int := by
          rw [typeof_plus_eq]
          simp [__smtx_typeof_arith_overload_op_2, hRight.1, hRight.2]
        rw [hRightTy] at hOut
        cases hOut.2
      · exact Or.inr ⟨hLeft.1, hRight.1, hLeft.2, hRight.2⟩

private theorem arith_sum_leq_args_of_bool (a1 b1 a2 b2 : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) ->
    (__smtx_typeof (__eo_to_smt a1) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt b1) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt a2) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt b2) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt a1) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt b1) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt a2) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt b2) = SmtType.Real) := by
  intro hTy
  have hTy' :
      __smtx_typeof
        (SmtTerm.leq
          (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2))
          (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2))) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eo_to_smt_leq_eq, eo_to_smt_plus_eq] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.leq
          (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2))
          (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2))) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
      (typeof_leq_eq
        (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2))
        (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2))) hNN with hOut | hOut
  · have hLeftNN :
        term_has_non_none_type (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2)) := by
      unfold term_has_non_none_type
      rw [hOut.1]
      simp
    have hRightNN :
        term_has_non_none_type (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2)) := by
      unfold term_has_non_none_type
      rw [hOut.2]
      simp
    rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
        (typeof_plus_eq (__eo_to_smt a1) (__eo_to_smt a2)) hLeftNN with hLeft | hLeft
    · rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
          (typeof_plus_eq (__eo_to_smt b1) (__eo_to_smt b2)) hRightNN with hRight | hRight
      · exact Or.inl ⟨hLeft.1, hRight.1, hLeft.2, hRight.2⟩
      · have hRightTy :
            __smtx_typeof (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2)) =
              SmtType.Real := by
          rw [typeof_plus_eq]
          simp [__smtx_typeof_arith_overload_op_2, hRight.1, hRight.2]
        rw [hRightTy] at hOut
        cases hOut.2
    · have hLeftTy :
          __smtx_typeof (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2)) =
            SmtType.Real := by
        rw [typeof_plus_eq]
        simp [__smtx_typeof_arith_overload_op_2, hLeft.1, hLeft.2]
      rw [hLeftTy] at hOut
      cases hOut.1
  · have hLeftNN :
        term_has_non_none_type (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2)) := by
      unfold term_has_non_none_type
      rw [hOut.1]
      simp
    have hRightNN :
        term_has_non_none_type (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2)) := by
      unfold term_has_non_none_type
      rw [hOut.2]
      simp
    rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
        (typeof_plus_eq (__eo_to_smt a1) (__eo_to_smt a2)) hLeftNN with hLeft | hLeft
    · have hLeftTy :
          __smtx_typeof (SmtTerm.plus (__eo_to_smt a1) (__eo_to_smt a2)) =
            SmtType.Int := by
        rw [typeof_plus_eq]
        simp [__smtx_typeof_arith_overload_op_2, hLeft.1, hLeft.2]
      rw [hLeftTy] at hOut
      cases hOut.1
    · rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
          (typeof_plus_eq (__eo_to_smt b1) (__eo_to_smt b2)) hRightNN with hRight | hRight
      · have hRightTy :
            __smtx_typeof (SmtTerm.plus (__eo_to_smt b1) (__eo_to_smt b2)) =
              SmtType.Int := by
          rw [typeof_plus_eq]
          simp [__smtx_typeof_arith_overload_op_2, hRight.1, hRight.2]
        rw [hRightTy] at hOut
        cases hOut.2
      · exact Or.inr ⟨hLeft.1, hRight.1, hLeft.2, hRight.2⟩

private theorem native_zleq_of_zlt_true {a b : native_Int} :
    native_zlt a b = true -> native_zleq a b = true := by
  intro h
  have hLt : a < b := by
    simpa [native_zlt, SmtEval.native_zlt] using h
  have hLe : a <= b := Int.le_of_lt hLt
  simpa [native_zleq, SmtEval.native_zleq] using hLe

private theorem native_qleq_of_qlt_true {a b : native_Rat} :
    native_qlt a b = true -> native_qleq a b = true := by
  intro h
  have hLt : a < b := by
    simpa [native_qlt, SmtEval.native_qlt] using h
  have hLe : a <= b := Rat.le_of_lt hLt
  simpa [native_qleq, Smtm.native_qleq] using hLe

private theorem native_zlt_add_of_zlt_of_zle {a b c d : native_Int} :
    native_zlt a b = true ->
    native_zleq c d = true ->
    native_zlt (native_zplus a c) (native_zplus b d) = true := by
  intro hlt hle
  have hltp : a < b := by
    simpa [native_zlt, SmtEval.native_zlt] using hlt
  have hlep : c <= d := by
    simpa [native_zleq, SmtEval.native_zleq] using hle
  have hres : native_zplus a c < native_zplus b d :=
    Int.add_lt_add_of_lt_of_le hltp hlep
  simp only [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus]
  exact decide_eq_true hres

private theorem native_zlt_add_of_zle_of_zlt {a b c d : native_Int} :
    native_zleq a b = true ->
    native_zlt c d = true ->
    native_zlt (native_zplus a c) (native_zplus b d) = true := by
  intro hle hlt
  have hlep : a <= b := by
    simpa [native_zleq, SmtEval.native_zleq] using hle
  have hltp : c < d := by
    simpa [native_zlt, SmtEval.native_zlt] using hlt
  have hres : native_zplus a c < native_zplus b d :=
    Int.add_lt_add_of_le_of_lt hlep hltp
  simp only [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus]
  exact decide_eq_true hres

private theorem native_zleq_add_of_zle_of_zle {a b c d : native_Int} :
    native_zleq a b = true ->
    native_zleq c d = true ->
    native_zleq (native_zplus a c) (native_zplus b d) = true := by
  intro hle1 hle2
  have hle1p : a <= b := by
    simpa [native_zleq, SmtEval.native_zleq] using hle1
  have hle2p : c <= d := by
    simpa [native_zleq, SmtEval.native_zleq] using hle2
  have hres : native_zplus a c <= native_zplus b d :=
    Int.add_le_add hle1p hle2p
  simp only [native_zleq, SmtEval.native_zleq, native_zplus, SmtEval.native_zplus]
  exact decide_eq_true hres

private theorem native_qlt_add_of_qlt_of_qle {a b c d : native_Rat} :
    native_qlt a b = true ->
    native_qleq c d = true ->
    native_qlt (native_qplus a c) (native_qplus b d) = true := by
  intro hlt hle
  have hltp : a < b := by
    simpa [native_qlt, SmtEval.native_qlt] using hlt
  have hlep : c <= d := by
    simpa [native_qleq, Smtm.native_qleq] using hle
  have hres : a + c < b + d := by
    grind
  simp only [native_qlt, SmtEval.native_qlt, native_qplus, SmtEval.native_qplus]
  exact decide_eq_true hres

private theorem native_qlt_add_of_qle_of_qlt {a b c d : native_Rat} :
    native_qleq a b = true ->
    native_qlt c d = true ->
    native_qlt (native_qplus a c) (native_qplus b d) = true := by
  intro hle hlt
  have hlep : a <= b := by
    simpa [native_qleq, Smtm.native_qleq] using hle
  have hltp : c < d := by
    simpa [native_qlt, SmtEval.native_qlt] using hlt
  have hres : a + c < b + d := by
    grind
  simp only [native_qlt, SmtEval.native_qlt, native_qplus, SmtEval.native_qplus]
  exact decide_eq_true hres

private theorem native_qleq_add_of_qle_of_qle {a b c d : native_Rat} :
    native_qleq a b = true ->
    native_qleq c d = true ->
    native_qleq (native_qplus a c) (native_qplus b d) = true := by
  intro hle1 hle2
  have hle1p : a <= b := by
    simpa [native_qleq, Smtm.native_qleq] using hle1
  have hle2p : c <= d := by
    simpa [native_qleq, Smtm.native_qleq] using hle2
  have hres : a + c <= b + d := by
    grind
  simp only [native_qleq, Smtm.native_qleq, native_qplus, SmtEval.native_qplus]
  exact decide_eq_true hres

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

private theorem int_lt_eval_of_lt_true
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Int)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Int) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) true ->
    ∃ n m : native_Int,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Numeral n ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Numeral m ∧
      native_zlt n m = true := by
  intro h
  rcases smt_eval_int_of_type M hM a hA with ⟨n, ha⟩
  rcases smt_eval_int_of_type M hM b hB with ⟨m, hb⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_lt_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [__smtx_model_eval.eq_17, ha, hb] at hEval
      simp [__smtx_model_eval_lt] at hEval
      exact ⟨n, m, ha, hb, hEval⟩

private theorem int_le_eval_of_leq_true
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Int)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Int) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) true ->
    ∃ n m : native_Int,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Numeral n ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Numeral m ∧
      native_zleq n m = true := by
  intro h
  rcases smt_eval_int_of_type M hM a hA with ⟨n, ha⟩
  rcases smt_eval_int_of_type M hM b hB with ⟨m, hb⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_leq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [__smtx_model_eval.eq_18, ha, hb] at hEval
      simp [__smtx_model_eval_leq] at hEval
      exact ⟨n, m, ha, hb, hEval⟩

private theorem int_le_eval_of_eq_true
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Int)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Int) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) true ->
    ∃ n m : native_Int,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Numeral n ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Numeral m ∧
      native_zleq n m = true := by
  intro h
  rcases smt_eval_int_of_type M hM a hA with ⟨n, ha⟩
  rcases smt_eval_int_of_type M hM b hB with ⟨m, hb⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq, ha, hb] at hEval
      simp [__smtx_model_eval_eq, native_veq] at hEval
      subst m
      exact ⟨n, n, ha, hb, by simp [native_zleq, SmtEval.native_zleq]⟩

private theorem real_lt_eval_of_lt_true
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Real)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Real) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) true ->
    ∃ q r : native_Rat,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Rational q ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Rational r ∧
      native_qlt q r = true := by
  intro h
  rcases smt_eval_real_of_type M hM a hA with ⟨q, ha⟩
  rcases smt_eval_real_of_type M hM b hB with ⟨r, hb⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_lt_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [__smtx_model_eval.eq_17, ha, hb] at hEval
      simp [__smtx_model_eval_lt] at hEval
      exact ⟨q, r, ha, hb, hEval⟩

private theorem real_le_eval_of_leq_true
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Real)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Real) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) true ->
    ∃ q r : native_Rat,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Rational q ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Rational r ∧
      native_qleq q r = true := by
  intro h
  rcases smt_eval_real_of_type M hM a hA with ⟨q, ha⟩
  rcases smt_eval_real_of_type M hM b hB with ⟨r, hb⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_leq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [__smtx_model_eval.eq_18, ha, hb] at hEval
      simp [__smtx_model_eval_leq] at hEval
      exact ⟨q, r, ha, hb, hEval⟩

private theorem real_le_eval_of_eq_true
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hA : __smtx_typeof (__eo_to_smt a) = SmtType.Real)
    (hB : __smtx_typeof (__eo_to_smt b) = SmtType.Real) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) true ->
    ∃ q r : native_Rat,
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Rational q ∧
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Rational r ∧
      native_qleq q r = true := by
  intro h
  rcases smt_eval_real_of_type M hM a hA with ⟨q, ha⟩
  rcases smt_eval_real_of_type M hM b hB with ⟨r, hb⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq, ha, hb] at hEval
      simp [__smtx_model_eval_eq, native_veq] at hEval
      subst r
      exact ⟨q, q, ha, hb, by simp [native_qleq, Smtm.native_qleq]⟩

private theorem sum_lt_true_of_int_eval
    (M : SmtModel) (a1 b1 a2 b2 : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)))
    {n1 m1 n2 m2 : native_Int}
    (ha1 : __smtx_model_eval M (__eo_to_smt a1) = SmtValue.Numeral n1)
    (hb1 : __smtx_model_eval M (__eo_to_smt b1) = SmtValue.Numeral m1)
    (ha2 : __smtx_model_eval M (__eo_to_smt a2) = SmtValue.Numeral n2)
    (hb2 : __smtx_model_eval M (__eo_to_smt b2) = SmtValue.Numeral m2)
    (hLt : native_zlt n1 m1 = true)
    (hLe : native_zleq n2 m2 = true) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · rw [eo_to_smt_lt_eq, eo_to_smt_plus_eq, eo_to_smt_plus_eq,
      __smtx_model_eval.eq_17, __smtx_model_eval.eq_14, __smtx_model_eval.eq_14,
      ha1, ha2, hb1, hb2]
    simpa [__smtx_model_eval_plus, __smtx_model_eval_lt] using
      native_zlt_add_of_zlt_of_zle hLt hLe

private theorem sum_lt_true_of_real_eval
    (M : SmtModel) (a1 b1 a2 b2 : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)))
    {q1 r1 q2 r2 : native_Rat}
    (ha1 : __smtx_model_eval M (__eo_to_smt a1) = SmtValue.Rational q1)
    (hb1 : __smtx_model_eval M (__eo_to_smt b1) = SmtValue.Rational r1)
    (ha2 : __smtx_model_eval M (__eo_to_smt a2) = SmtValue.Rational q2)
    (hb2 : __smtx_model_eval M (__eo_to_smt b2) = SmtValue.Rational r2)
    (hLt : native_qlt q1 r1 = true)
    (hLe : native_qleq q2 r2 = true) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · rw [eo_to_smt_lt_eq, eo_to_smt_plus_eq, eo_to_smt_plus_eq,
      __smtx_model_eval.eq_17, __smtx_model_eval.eq_14, __smtx_model_eval.eq_14,
      ha1, ha2, hb1, hb2]
    simpa [__smtx_model_eval_plus, __smtx_model_eval_lt] using
      native_qlt_add_of_qlt_of_qle hLt hLe

private theorem sum_lt_true_of_int_eval_right
    (M : SmtModel) (a1 b1 a2 b2 : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)))
    {n1 m1 n2 m2 : native_Int}
    (ha1 : __smtx_model_eval M (__eo_to_smt a1) = SmtValue.Numeral n1)
    (hb1 : __smtx_model_eval M (__eo_to_smt b1) = SmtValue.Numeral m1)
    (ha2 : __smtx_model_eval M (__eo_to_smt a2) = SmtValue.Numeral n2)
    (hb2 : __smtx_model_eval M (__eo_to_smt b2) = SmtValue.Numeral m2)
    (hLe : native_zleq n1 m1 = true)
    (hLt : native_zlt n2 m2 = true) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · rw [eo_to_smt_lt_eq, eo_to_smt_plus_eq, eo_to_smt_plus_eq,
      __smtx_model_eval.eq_17, __smtx_model_eval.eq_14, __smtx_model_eval.eq_14,
      ha1, ha2, hb1, hb2]
    simpa [__smtx_model_eval_plus, __smtx_model_eval_lt] using
      native_zlt_add_of_zle_of_zlt hLe hLt

private theorem sum_lt_true_of_real_eval_right
    (M : SmtModel) (a1 b1 a2 b2 : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)))
    {q1 r1 q2 r2 : native_Rat}
    (ha1 : __smtx_model_eval M (__eo_to_smt a1) = SmtValue.Rational q1)
    (hb1 : __smtx_model_eval M (__eo_to_smt b1) = SmtValue.Rational r1)
    (ha2 : __smtx_model_eval M (__eo_to_smt a2) = SmtValue.Rational q2)
    (hb2 : __smtx_model_eval M (__eo_to_smt b2) = SmtValue.Rational r2)
    (hLe : native_qleq q1 r1 = true)
    (hLt : native_qlt q2 r2 = true) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · rw [eo_to_smt_lt_eq, eo_to_smt_plus_eq, eo_to_smt_plus_eq,
      __smtx_model_eval.eq_17, __smtx_model_eval.eq_14, __smtx_model_eval.eq_14,
      ha1, ha2, hb1, hb2]
    simpa [__smtx_model_eval_plus, __smtx_model_eval_lt] using
      native_qlt_add_of_qle_of_qlt hLe hLt

private theorem sum_leq_true_of_int_eval
    (M : SmtModel) (a1 b1 a2 b2 : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)))
    {n1 m1 n2 m2 : native_Int}
    (ha1 : __smtx_model_eval M (__eo_to_smt a1) = SmtValue.Numeral n1)
    (hb1 : __smtx_model_eval M (__eo_to_smt b1) = SmtValue.Numeral m1)
    (ha2 : __smtx_model_eval M (__eo_to_smt a2) = SmtValue.Numeral n2)
    (hb2 : __smtx_model_eval M (__eo_to_smt b2) = SmtValue.Numeral m2)
    (hLe1 : native_zleq n1 m1 = true)
    (hLe2 : native_zleq n2 m2 = true) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · rw [eo_to_smt_leq_eq, eo_to_smt_plus_eq, eo_to_smt_plus_eq,
      __smtx_model_eval.eq_18, __smtx_model_eval.eq_14, __smtx_model_eval.eq_14,
      ha1, ha2, hb1, hb2]
    simpa [__smtx_model_eval_plus, __smtx_model_eval_leq] using
      native_zleq_add_of_zle_of_zle hLe1 hLe2

private theorem sum_leq_true_of_real_eval
    (M : SmtModel) (a1 b1 a2 b2 : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)))
    {q1 r1 q2 r2 : native_Rat}
    (ha1 : __smtx_model_eval M (__eo_to_smt a1) = SmtValue.Rational q1)
    (hb1 : __smtx_model_eval M (__eo_to_smt b1) = SmtValue.Rational r1)
    (ha2 : __smtx_model_eval M (__eo_to_smt a2) = SmtValue.Rational q2)
    (hb2 : __smtx_model_eval M (__eo_to_smt b2) = SmtValue.Rational r2)
    (hLe1 : native_qleq q1 r1 = true)
    (hLe2 : native_qleq q2 r2 = true) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · rw [eo_to_smt_leq_eq, eo_to_smt_plus_eq, eo_to_smt_plus_eq,
      __smtx_model_eval.eq_18, __smtx_model_eval.eq_14, __smtx_model_eval.eq_14,
      ha1, ha2, hb1, hb2]
    simpa [__smtx_model_eval_plus, __smtx_model_eval_leq] using
      native_qleq_add_of_qle_of_qle hLe1 hLe2

private theorem arith_rel_sum_true
    (M : SmtModel) (hM : model_wf M)
    (r1 r2 a1 b1 a2 b2 : Term)
    (h1 : eo_interprets M (Term.Apply (Term.Apply r1 a1) b1) true)
    (h2 : eo_interprets M (Term.Apply (Term.Apply r2 a2) b2) true)
    (hBool : RuleProofs.eo_has_bool_type
      (__arith_rel_sum r1 r2
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2))) :
    eo_interprets M
      (__arith_rel_sum r1 r2
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) true := by
  cases r1 <;> try
    (exfalso
     exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
       (by simpa [__arith_rel_sum] using hBool) rfl)
  case UOp op1 =>
    cases op1 <;> try
      (exfalso
       exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
         (by simpa [__arith_rel_sum] using hBool) rfl)
    case lt =>
      cases r2 <;> try
        (exfalso
         exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
           (by simpa [__arith_rel_sum] using hBool) rfl)
      case UOp op2 =>
        cases op2 <;> try
          (exfalso
           exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
             (by simpa [__arith_rel_sum] using hBool) rfl)
        case lt =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_lt_eval_of_lt_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLt1⟩
            rcases int_lt_eval_of_lt_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLt2⟩
            exact sum_lt_true_of_int_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLt1 (native_zleq_of_zlt_true hLt2)
          · rcases real_lt_eval_of_lt_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLt1⟩
            rcases real_lt_eval_of_lt_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLt2⟩
            exact sum_lt_true_of_real_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLt1 (native_qleq_of_qlt_true hLt2)
        case eq =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_lt_eval_of_lt_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLt1⟩
            rcases int_le_eval_of_eq_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLe2⟩
            exact sum_lt_true_of_int_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLt1 hLe2
          · rcases real_lt_eval_of_lt_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLt1⟩
            rcases real_le_eval_of_eq_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLe2⟩
            exact sum_lt_true_of_real_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLt1 hLe2
        case leq =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_lt_eval_of_lt_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLt1⟩
            rcases int_le_eval_of_leq_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLe2⟩
            exact sum_lt_true_of_int_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLt1 hLe2
          · rcases real_lt_eval_of_lt_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLt1⟩
            rcases real_le_eval_of_leq_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLe2⟩
            exact sum_lt_true_of_real_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLt1 hLe2
    case leq =>
      cases r2 <;> try
        (exfalso
         exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
           (by simpa [__arith_rel_sum] using hBool) rfl)
      case UOp op2 =>
        cases op2 <;> try
          (exfalso
           exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
             (by simpa [__arith_rel_sum] using hBool) rfl)
        case lt =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_le_eval_of_leq_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLe1⟩
            rcases int_lt_eval_of_lt_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLt2⟩
            exact sum_lt_true_of_int_eval_right M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLt2
          · rcases real_le_eval_of_leq_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLe1⟩
            rcases real_lt_eval_of_lt_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLt2⟩
            exact sum_lt_true_of_real_eval_right M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLt2
        case eq =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.leq)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_leq_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_le_eval_of_leq_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLe1⟩
            rcases int_le_eval_of_eq_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLe2⟩
            exact sum_leq_true_of_int_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLe2
          · rcases real_le_eval_of_leq_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLe1⟩
            rcases real_le_eval_of_eq_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLe2⟩
            exact sum_leq_true_of_real_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLe2
        case leq =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.leq)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_leq_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_le_eval_of_leq_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLe1⟩
            rcases int_le_eval_of_leq_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLe2⟩
            exact sum_leq_true_of_int_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLe2
          · rcases real_le_eval_of_leq_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLe1⟩
            rcases real_le_eval_of_leq_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLe2⟩
            exact sum_leq_true_of_real_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLe2
    case eq =>
      cases r2 <;> try
        (exfalso
         exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
           (by simpa [__arith_rel_sum] using hBool) rfl)
      case UOp op2 =>
        cases op2 <;> try
          (exfalso
           exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
             (by simpa [__arith_rel_sum] using hBool) rfl)
        case lt =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_le_eval_of_eq_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLe1⟩
            rcases int_lt_eval_of_lt_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLt2⟩
            exact sum_lt_true_of_int_eval_right M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLt2
          · rcases real_le_eval_of_eq_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLe1⟩
            rcases real_lt_eval_of_lt_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLt2⟩
            exact sum_lt_true_of_real_eval_right M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLt2
        case eq =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.leq)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_leq_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_le_eval_of_eq_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLe1⟩
            rcases int_le_eval_of_eq_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLe2⟩
            exact sum_leq_true_of_int_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLe2
          · rcases real_le_eval_of_eq_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLe1⟩
            rcases real_le_eval_of_eq_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLe2⟩
            exact sum_leq_true_of_real_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLe2
        case leq =>
          have hOutBool : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.leq)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_leq_args_of_bool a1 b1 a2 b2 hOutBool with hInt | hReal
          · rcases int_le_eval_of_eq_true M hM a1 b1 hInt.1 hInt.2.1 h1 with
              ⟨n1, m1, ha1, hb1, hLe1⟩
            rcases int_le_eval_of_leq_true M hM a2 b2 hInt.2.2.1 hInt.2.2.2 h2 with
              ⟨n2, m2, ha2, hb2, hLe2⟩
            exact sum_leq_true_of_int_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLe2
          · rcases real_le_eval_of_eq_true M hM a1 b1 hReal.1 hReal.2.1 h1 with
              ⟨q1, r1, ha1, hb1, hLe1⟩
            rcases real_le_eval_of_leq_true M hM a2 b2 hReal.2.2.1 hReal.2.2.2 h2 with
              ⟨q2, r2, ha2, hb2, hLe2⟩
            exact sum_leq_true_of_real_eval M a1 b1 a2 b2 hOutBool
              ha1 hb1 ha2 hb2 hLe1 hLe2

private def arithSumStep : Term -> Term -> Term
  | (Term.Apply (Term.Apply r1 a1) b1), (Term.Apply (Term.Apply r2 a2) b2) =>
      __arith_rel_sum r1 r2
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)
  | _, _ => Term.Stuck

private def arithSumFoldList : List Term -> Term -> Term
  | [], acc => acc
  | p :: ps, acc => arithSumFoldList ps (arithSumStep p acc)

private def arithSumFoldRight : List Term -> Term -> Term
  | [], acc => acc
  | p :: ps, acc => arithSumStep p (arithSumFoldRight ps acc)

private def arithSumZeroAcc (a : Term) : Term :=
  let z := __arith_mk_zero (__eo_typeof a)
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) z) z

private theorem arithSumFoldList_append :
    ∀ (xs ys : List Term) (acc : Term),
      arithSumFoldList (xs ++ ys) acc =
        arithSumFoldList ys (arithSumFoldList xs acc) := by
  intro xs ys acc
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons p xs ih =>
      simpa [arithSumFoldList] using ih (arithSumStep p acc)

private theorem arithSumFoldList_reverse_eq_right :
    ∀ (ps : List Term) (acc : Term),
      arithSumFoldList ps.reverse acc = arithSumFoldRight ps acc := by
  intro ps acc
  induction ps generalizing acc with
  | nil =>
      rfl
  | cons p ps ih =>
      calc
        arithSumFoldList (p :: ps).reverse acc =
            arithSumFoldList ([p]) (arithSumFoldList ps.reverse acc) := by
              rw [List.reverse_cons, arithSumFoldList_append]
        _ = arithSumStep p (arithSumFoldList ps.reverse acc) := by
              rfl
        _ = arithSumStep p (arithSumFoldRight ps acc) := by
              rw [ih]
        _ = arithSumFoldRight (p :: ps) acc := by
              rfl

private theorem arithSumStep_stuck_right (p : Term) :
    arithSumStep p Term.Stuck = Term.Stuck := by
  cases p <;> try rfl
  case Apply f x =>
    cases f <;> rfl

private theorem arithSumFoldList_stuck :
    ∀ ps : List Term, arithSumFoldList ps Term.Stuck = Term.Stuck := by
  intro ps
  induction ps with
  | nil =>
      rfl
  | cons p ps ih =>
      simp [arithSumFoldList, arithSumStep_stuck_right, ih]

private theorem arithSumFoldRight_stuck :
    ∀ ps : List Term, arithSumFoldRight ps Term.Stuck = Term.Stuck := by
  intro ps
  induction ps with
  | nil =>
      rfl
  | cons p ps ih =>
      simp [arithSumFoldRight, ih, arithSumStep_stuck_right]

private theorem arithSumFoldList_eq_mk_rec :
    ∀ (ps : List Term) (acc : Term),
      __mk_arith_sum_ub_rec (premiseAndFormulaList ps) acc =
        arithSumFoldList ps acc := by
  intro ps acc
  induction ps generalizing acc with
  | nil =>
      cases acc <;> rfl
  | cons p ps ih =>
      cases p
      case Apply pf pb =>
        cases pf
        case Apply r1 a1 =>
          cases acc <;>
            simp [premiseAndFormulaList, arithSumFoldList, arithSumStep,
              __mk_arith_sum_ub_rec, arithSumFoldList_stuck]
          case Apply af ab =>
            cases af <;>
              simp [__mk_arith_sum_ub_rec, arithSumFoldList_stuck, ih]
        all_goals
          cases acc <;>
            simp [premiseAndFormulaList, arithSumFoldList, arithSumStep,
              __mk_arith_sum_ub_rec, arithSumFoldList_stuck]
      all_goals
        cases acc <;>
          simp [premiseAndFormulaList, arithSumFoldList, arithSumStep,
            __mk_arith_sum_ub_rec, arithSumFoldList_stuck]

private theorem eo_get_nil_rec_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        Term.Boolean true := by
  intro ps
  induction ps with
  | nil =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires, __eo_is_list_nil,
        native_ite, native_teq, native_not, SmtEval.native_not]
  | cons p ps ih =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires, ih,
        native_ite, native_teq, native_not, SmtEval.native_not]

private theorem eo_list_rev_rec_and_premiseAndFormulaList :
    ∀ xs ys : List Term,
      __eo_list_rev_rec (premiseAndFormulaList xs) (premiseAndFormulaList ys) =
        premiseAndFormulaList (xs.reverse ++ ys) := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      cases ys <;> rfl
  | cons p xs ih =>
      cases ys with
      | nil =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih [p]
      | cons y ys =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih (p :: y :: ys)

private theorem eo_list_rev_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_list_rev (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        premiseAndFormulaList ps.reverse := by
  intro ps
  unfold __eo_list_rev
  simp [__eo_requires, premiseAndFormulaList_is_and_list,
    eo_get_nil_rec_and_premiseAndFormulaList, native_ite, native_teq,
    native_not, SmtEval.native_not]
  simpa [premiseAndFormulaList] using
    eo_list_rev_rec_and_premiseAndFormulaList ps []

private theorem mk_arith_sum_ub_eq_fold_right
    (r a b : Term) (ps : List Term) :
    __mk_arith_sum_ub
      (premiseAndFormulaList (Term.Apply (Term.Apply r a) b :: ps)) =
      arithSumFoldRight (Term.Apply (Term.Apply r a) b :: ps) (arithSumZeroAcc a) := by
  unfold premiseAndFormulaList
  unfold __mk_arith_sum_ub
  change __mk_arith_sum_ub_rec
      (__eo_list_rev (Term.UOp UserOp.and)
        (premiseAndFormulaList (Term.Apply (Term.Apply r a) b :: ps)))
      (arithSumZeroAcc a) =
      arithSumFoldRight (Term.Apply (Term.Apply r a) b :: ps) (arithSumZeroAcc a)
  rw [eo_list_rev_and_premiseAndFormulaList]
  rw [arithSumFoldList_eq_mk_rec]
  rw [arithSumFoldList_reverse_eq_right]

private theorem arithSumZeroAcc_true_of_not_stuck
    (M : SmtModel) (a : Term) :
    arithSumZeroAcc a ≠ Term.Stuck ->
    eo_interprets M (arithSumZeroAcc a) true := by
  intro hAcc
  have hAcc' :
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq) (__arith_mk_zero (__eo_typeof a)))
        (__arith_mk_zero (__eo_typeof a)) ≠ Term.Stuck := by
    simpa [arithSumZeroAcc] using hAcc
  have hZeroNe : __arith_mk_zero (__eo_typeof a) ≠ Term.Stuck := by
    intro hZero
    apply hAcc'
    rw [hZero]
    rfl
  unfold arithSumZeroAcc
  cases hTy : __eo_typeof a
  case UOp op =>
    cases op
    case Int =>
      change eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Numeral 0)) (Term.Numeral 0))
        true
      apply RuleProofs.eo_interprets_eq_of_rel M
      · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
          (Term.Numeral 0) (Term.Numeral 0)
          (by rfl)
          (by
            change __smtx_typeof (SmtTerm.Numeral 0) ≠ SmtType.None
            unfold __smtx_typeof
            intro hNone
            cases hNone)
      · exact RuleProofs.smt_value_rel_refl
          (__smtx_model_eval M (__eo_to_smt (Term.Numeral 0)))
    case Real =>
      change eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Rational (native_mk_rational 0 1)))
          (Term.Rational (native_mk_rational 0 1))) true
      apply RuleProofs.eo_interprets_eq_of_rel M
      · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
          (Term.Rational (native_mk_rational 0 1))
          (Term.Rational (native_mk_rational 0 1))
          (by rfl)
          (by
            change __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) ≠ SmtType.None
            unfold __smtx_typeof
            intro hNone
            cases hNone)
      · exact RuleProofs.smt_value_rel_refl
          (__smtx_model_eval M (__eo_to_smt
            (Term.Rational (native_mk_rational 0 1))))
    all_goals
      exfalso
      apply hZeroNe
      simp [__arith_mk_zero, hTy]
  all_goals
    exfalso
    apply hZeroNe
    simp [__arith_mk_zero, hTy]

private theorem eo_typeof_lt_bool_args
    (A B : Term) :
    __eo_typeof_lt A B = Term.Bool ->
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  intro h
  exact RuleProofs.eo_typeof_lt_bool_cases A B h

private theorem eo_typeof_plus_eq_int_args
    (A B : Term) :
    __eo_typeof_plus A B = Term.UOp UserOp.Int ->
    A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int := by
  intro h
  exact RuleProofs.eo_typeof_plus_int_args A B h

private theorem eo_typeof_plus_eq_real_args
    (A B : Term) :
    __eo_typeof_plus A B = Term.UOp UserOp.Real ->
    A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real := by
  intro h
  exact RuleProofs.eo_typeof_plus_real_args A B h

private theorem eo_typeof_right_rel_of_sum_rel_bool
    (op : UserOp) (a1 b1 a2 b2 : Term)
    (hStep :
      __eo_typeof_lt
        (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
        (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool)
    (hOp : op = UserOp.lt ∨ op = UserOp.eq ∨ op = UserOp.leq) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) a2) b2) = Term.Bool := by
  rcases eo_typeof_lt_bool_args
      (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
      (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) hStep with hInt | hReal
  · rcases eo_typeof_plus_eq_int_args (__eo_typeof a1) (__eo_typeof a2) hInt.1 with ⟨_, ha2⟩
    rcases eo_typeof_plus_eq_int_args (__eo_typeof b1) (__eo_typeof b2) hInt.2 with ⟨_, hb2⟩
    rcases hOp with rfl | hOp
    · change __eo_typeof_lt (__eo_typeof a2) (__eo_typeof b2) = Term.Bool
      rw [ha2, hb2]
      native_decide
    · rcases hOp with rfl | rfl
      · change __eo_typeof_eq (__eo_typeof a2) (__eo_typeof b2) = Term.Bool
        rw [ha2, hb2]
        native_decide
      · change __eo_typeof_lt (__eo_typeof a2) (__eo_typeof b2) = Term.Bool
        rw [ha2, hb2]
        native_decide
  · rcases eo_typeof_plus_eq_real_args (__eo_typeof a1) (__eo_typeof a2) hReal.1 with ⟨_, ha2⟩
    rcases eo_typeof_plus_eq_real_args (__eo_typeof b1) (__eo_typeof b2) hReal.2 with ⟨_, hb2⟩
    rcases hOp with rfl | hOp
    · change __eo_typeof_lt (__eo_typeof a2) (__eo_typeof b2) = Term.Bool
      rw [ha2, hb2]
      native_decide
    · rcases hOp with rfl | rfl
      · change __eo_typeof_eq (__eo_typeof a2) (__eo_typeof b2) = Term.Bool
        rw [ha2, hb2]
        native_decide
      · change __eo_typeof_lt (__eo_typeof a2) (__eo_typeof b2) = Term.Bool
        rw [ha2, hb2]
        native_decide

private theorem smt_type_eq_int_of_eo_type_and_translation
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hEo : __eo_typeof t = Term.UOp UserOp.Int) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  rw [hEo] at hMatch
  simpa [__eo_to_smt_type] using hMatch

private theorem smt_type_eq_real_of_eo_type_and_translation
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hEo : __eo_typeof t = Term.UOp UserOp.Real) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  rw [hEo] at hMatch
  simpa [__eo_to_smt_type] using hMatch

private theorem smt_translation_of_smt_int
    (t : Term)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    RuleProofs.eo_has_smt_translation t := by
  intro hNone
  rw [h] at hNone
  cases hNone

private theorem smt_translation_of_smt_real
    (t : Term)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    RuleProofs.eo_has_smt_translation t := by
  intro hNone
  rw [h] at hNone
  cases hNone

private theorem arith_rel_lt_args_of_bool
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) ->
    (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.Real) := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eo_to_smt_lt_eq] using hTy
  have hNN :
      term_has_non_none_type (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  exact arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt)
    (typeof_lt_eq (__eo_to_smt a) (__eo_to_smt b)) hNN

private theorem arith_rel_leq_args_of_bool
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) ->
    (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.Real) := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eo_to_smt_leq_eq] using hTy
  have hNN :
      term_has_non_none_type (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  exact arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
    (typeof_leq_eq (__eo_to_smt a) (__eo_to_smt b)) hNN

private theorem rel_operands_have_smt_translation
    (op : UserOp) (a b : Term)
    (hOp : op = UserOp.lt ∨ op = UserOp.eq ∨ op = UserOp.leq)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp op) a) b)) :
    RuleProofs.eo_has_smt_translation a ∧
      RuleProofs.eo_has_smt_translation b := by
  rcases hOp with rfl | hOp
  · rcases arith_rel_lt_args_of_bool a b hBool with hInt | hReal
    · exact ⟨smt_translation_of_smt_int a hInt.1,
        smt_translation_of_smt_int b hInt.2⟩
    · exact ⟨smt_translation_of_smt_real a hReal.1,
        smt_translation_of_smt_real b hReal.2⟩
  · rcases hOp with rfl | rfl
    · rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hBool with
        ⟨hEq, hNonNone⟩
      constructor
      · exact hNonNone
      · intro hNone
        apply hNonNone
        rw [hEq, hNone]
    · rcases arith_rel_leq_args_of_bool a b hBool with hInt | hReal
      · exact ⟨smt_translation_of_smt_int a hInt.1,
          smt_translation_of_smt_int b hInt.2⟩
      · exact ⟨smt_translation_of_smt_real a hReal.1,
          smt_translation_of_smt_real b hReal.2⟩

private theorem sum_terms_smt_arith_of_step_type
    (a1 b1 a2 b2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hB1Trans : RuleProofs.eo_has_smt_translation b1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hB2Trans : RuleProofs.eo_has_smt_translation b2)
    (hStep :
      __eo_typeof_lt
        (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
        (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool) :
    (__smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2)) =
        SmtType.Int ∧
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) =
        SmtType.Int) ∨
    (__smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2)) =
        SmtType.Real ∧
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) =
        SmtType.Real) := by
  rcases eo_typeof_lt_bool_args
      (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
      (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) hStep with hInt | hReal
  · rcases eo_typeof_plus_eq_int_args (__eo_typeof a1) (__eo_typeof a2) hInt.1 with ⟨ha1, ha2⟩
    rcases eo_typeof_plus_eq_int_args (__eo_typeof b1) (__eo_typeof b2) hInt.2 with ⟨hb1, hb2⟩
    have hA1Smt := smt_type_eq_int_of_eo_type_and_translation a1 hA1Trans ha1
    have hA2Smt := smt_type_eq_int_of_eo_type_and_translation a2 hA2Trans ha2
    have hB1Smt := smt_type_eq_int_of_eo_type_and_translation b1 hB1Trans hb1
    have hB2Smt := smt_type_eq_int_of_eo_type_and_translation b2 hB2Trans hb2
    refine Or.inl ⟨?_, ?_⟩
    · rw [eo_to_smt_plus_eq, typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hA1Smt, hA2Smt]
    · rw [eo_to_smt_plus_eq, typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hB1Smt, hB2Smt]
  · rcases eo_typeof_plus_eq_real_args (__eo_typeof a1) (__eo_typeof a2) hReal.1 with ⟨ha1, ha2⟩
    rcases eo_typeof_plus_eq_real_args (__eo_typeof b1) (__eo_typeof b2) hReal.2 with ⟨hb1, hb2⟩
    have hA1Smt := smt_type_eq_real_of_eo_type_and_translation a1 hA1Trans ha1
    have hA2Smt := smt_type_eq_real_of_eo_type_and_translation a2 hA2Trans ha2
    have hB1Smt := smt_type_eq_real_of_eo_type_and_translation b1 hB1Trans hb1
    have hB2Smt := smt_type_eq_real_of_eo_type_and_translation b2 hB2Trans hb2
    refine Or.inr ⟨?_, ?_⟩
    · rw [eo_to_smt_plus_eq, typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hA1Smt, hA2Smt]
    · rw [eo_to_smt_plus_eq, typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hB1Smt, hB2Smt]

private theorem sum_lt_has_bool_type_of_step_type
    (a1 b1 a2 b2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hB1Trans : RuleProofs.eo_has_smt_translation b1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hB2Trans : RuleProofs.eo_has_smt_translation b2)
    (hStep :
      __eo_typeof_lt
        (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
        (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
  rcases sum_terms_smt_arith_of_step_type a1 b1 a2 b2
      hA1Trans hB1Trans hA2Trans hB2Trans hStep with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem sum_leq_has_bool_type_of_step_type
    (a1 b1 a2 b2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hB1Trans : RuleProofs.eo_has_smt_translation b1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hB2Trans : RuleProofs.eo_has_smt_translation b2)
    (hStep :
      __eo_typeof_lt
        (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
        (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
  rcases sum_terms_smt_arith_of_step_type a1 b1 a2 b2
      hA1Trans hB1Trans hA2Trans hB2Trans hStep with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_leq_eq, typeof_leq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_leq_eq, typeof_leq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem arithSumStep_right_typeof_bool_of_typeof_bool
    (p tail : Term) :
    __eo_typeof (arithSumStep p tail) = Term.Bool ->
    __eo_typeof tail = Term.Bool := by
  intro hStepTy
  cases p
  case Apply pf b1 =>
    cases pf
    case Apply r1 a1 =>
      cases tail
      case Apply tf b2 =>
        cases tf
        case Apply r2 a2 =>
          cases r1
          case UOp op1 =>
            cases op1
            case lt =>
              cases r2
              case UOp op2 =>
                cases op2
                case lt =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.lt a1 b1 a2 b2
                    hStepTy (Or.inl rfl)
                case eq =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.eq a1 b1 a2 b2
                    hStepTy (Or.inr (Or.inl rfl))
                case leq =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.leq a1 b1 a2 b2
                    hStepTy (Or.inr (Or.inr rfl))
                all_goals
                  exfalso
                  exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
              all_goals
                exfalso
                exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
            case leq =>
              cases r2
              case UOp op2 =>
                cases op2
                case lt =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.lt a1 b1 a2 b2
                    hStepTy (Or.inl rfl)
                case eq =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.eq a1 b1 a2 b2
                    hStepTy (Or.inr (Or.inl rfl))
                case leq =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.leq a1 b1 a2 b2
                    hStepTy (Or.inr (Or.inr rfl))
                all_goals
                  exfalso
                  exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
              all_goals
                exfalso
                exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
            case eq =>
              cases r2
              case UOp op2 =>
                cases op2
                case lt =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.lt a1 b1 a2 b2
                    hStepTy (Or.inl rfl)
                case eq =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.eq a1 b1 a2 b2
                    hStepTy (Or.inr (Or.inl rfl))
                case leq =>
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact eo_typeof_right_rel_of_sum_rel_bool UserOp.leq a1 b1 a2 b2
                    hStepTy (Or.inr (Or.inr rfl))
                all_goals
                  exfalso
                  exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
              all_goals
                exfalso
                exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
            all_goals
              exfalso
              exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
          all_goals
            exfalso
            exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
        all_goals
          exfalso
          exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep])
      all_goals
        exfalso
        exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep])
    all_goals
      exfalso
      exact term_ne_stuck_of_typeof_bool hStepTy rfl
  all_goals
    exfalso
    exact term_ne_stuck_of_typeof_bool hStepTy rfl

private theorem arithSumStep_has_bool_type_of_typeof_bool
    (p tail : Term) :
    RuleProofs.eo_has_bool_type p ->
    RuleProofs.eo_has_bool_type tail ->
    __eo_typeof (arithSumStep p tail) = Term.Bool ->
    RuleProofs.eo_has_bool_type (arithSumStep p tail) := by
  intro hPBool hTailBool hStepTy
  cases p
  case Apply pf b1 =>
    cases pf
    case Apply r1 a1 =>
      cases tail
      case Apply tf b2 =>
        cases tf
        case Apply r2 a2 =>
          cases r1
          case UOp op1 =>
            cases op1
            case lt =>
              have hPTrans := rel_operands_have_smt_translation UserOp.lt a1 b1
                (Or.inl rfl) (by simpa using hPBool)
              cases r2
              case UOp op2 =>
                cases op2
                case lt =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.lt a2 b2
                    (Or.inl rfl) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_lt_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                case eq =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.eq a2 b2
                    (Or.inr (Or.inl rfl)) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_lt_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                case leq =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.leq a2 b2
                    (Or.inr (Or.inr rfl)) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_lt_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                all_goals
                  exfalso
                  exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
              all_goals
                exfalso
                exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
            case leq =>
              have hPTrans := rel_operands_have_smt_translation UserOp.leq a1 b1
                (Or.inr (Or.inr rfl)) (by simpa using hPBool)
              cases r2
              case UOp op2 =>
                cases op2
                case lt =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.lt a2 b2
                    (Or.inl rfl) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_lt_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                case eq =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.eq a2 b2
                    (Or.inr (Or.inl rfl)) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_leq_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                case leq =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.leq a2 b2
                    (Or.inr (Or.inr rfl)) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_leq_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                all_goals
                  exfalso
                  exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
              all_goals
                exfalso
                exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
            case eq =>
              have hPTrans := rel_operands_have_smt_translation UserOp.eq a1 b1
                (Or.inr (Or.inl rfl)) (by simpa using hPBool)
              cases r2
              case UOp op2 =>
                cases op2
                case lt =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.lt a2 b2
                    (Or.inl rfl) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_lt_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                case eq =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.eq a2 b2
                    (Or.inr (Or.inl rfl)) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_leq_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                case leq =>
                  have hTailTrans := rel_operands_have_smt_translation UserOp.leq a2 b2
                    (Or.inr (Or.inr rfl)) (by simpa using hTailBool)
                  change __eo_typeof_lt
                    (__eo_typeof_plus (__eo_typeof a1) (__eo_typeof a2))
                    (__eo_typeof_plus (__eo_typeof b1) (__eo_typeof b2)) = Term.Bool at hStepTy
                  exact sum_leq_has_bool_type_of_step_type a1 b1 a2 b2
                    hPTrans.1 hPTrans.2 hTailTrans.1 hTailTrans.2 hStepTy
                all_goals
                  exfalso
                  exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
              all_goals
                exfalso
                exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
            all_goals
              exfalso
              exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
          all_goals
            exfalso
            exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep, __arith_rel_sum])
        all_goals
          exfalso
          exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep])
      all_goals
        exfalso
        exact term_ne_stuck_of_typeof_bool hStepTy (by simp [arithSumStep])
    all_goals
      exfalso
      exact term_ne_stuck_of_typeof_bool hStepTy rfl
  all_goals
    exfalso
    exact term_ne_stuck_of_typeof_bool hStepTy rfl

private theorem arithSumFoldRight_acc_ne_stuck_of_ne_stuck
    (ps : List Term) (acc : Term) :
    arithSumFoldRight ps acc ≠ Term.Stuck ->
    acc ≠ Term.Stuck := by
  intro hFold hAcc
  subst acc
  rw [arithSumFoldRight_stuck] at hFold
  exact hFold rfl

private theorem arithSumFoldRight_has_bool_type_of_typeof_bool :
    ∀ (ps : List Term) (acc : Term),
      AllHaveBoolType ps ->
      RuleProofs.eo_has_bool_type acc ->
      __eo_typeof (arithSumFoldRight ps acc) = Term.Bool ->
      RuleProofs.eo_has_bool_type (arithSumFoldRight ps acc) := by
  intro ps acc hPsBool hAccBool hFoldTy
  induction ps generalizing acc with
  | nil =>
      simpa [arithSumFoldRight] using hAccBool
  | cons p ps ih =>
      let tail := arithSumFoldRight ps acc
      have hTailTy : __eo_typeof tail = Term.Bool :=
        arithSumStep_right_typeof_bool_of_typeof_bool p tail
          (by simpa [tail, arithSumFoldRight] using hFoldTy)
      have hTailBool : RuleProofs.eo_has_bool_type tail := by
        apply ih
        · intro t ht
          exact hPsBool t (by simp [ht])
        · exact hAccBool
        · exact hTailTy
      have hPBool : RuleProofs.eo_has_bool_type p :=
        hPsBool p (by simp)
      exact arithSumStep_has_bool_type_of_typeof_bool p tail hPBool hTailBool
        (by simpa [tail, arithSumFoldRight] using hFoldTy)

private theorem eo_has_bool_type_lt_of_arith
    (a b : Term)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) := by
  rcases hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem eo_has_bool_type_leq_of_arith
    (a b : Term)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) := by
  rcases hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_leq_eq, typeof_leq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_leq_eq, typeof_leq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem eo_has_bool_type_eq_of_arith
    (a b : Term)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
  rcases hTy with hInt | hReal
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
      (by rw [hInt.1, hInt.2]) (by rw [hInt.1]; simp)
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
      (by rw [hReal.1, hReal.2]) (by rw [hReal.1]; simp)

private theorem arith_rel_sum_right_bool_of_bool
    (r1 r2 a1 b1 a2 b2 : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (__arith_rel_sum r1 r2
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2))) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply r2 a2) b2) := by
  cases r1 <;> try
    (exfalso
     exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
       (by simpa [__arith_rel_sum] using hBool) rfl)
  case UOp op1 =>
    cases op1 <;> try
      (exfalso
       exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
         (by simpa [__arith_rel_sum] using hBool) rfl)
    case lt =>
      cases r2 <;> try
        (exfalso
         exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
           (by simpa [__arith_rel_sum] using hBool) rfl)
      case UOp op2 =>
        cases op2 <;> try
          (exfalso
           exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
             (by simpa [__arith_rel_sum] using hBool) rfl)
        case lt =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_lt_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_lt_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)
        case eq =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_eq_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_eq_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)
        case leq =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_leq_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_leq_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)
    case leq =>
      cases r2 <;> try
        (exfalso
         exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
           (by simpa [__arith_rel_sum] using hBool) rfl)
      case UOp op2 =>
        cases op2 <;> try
          (exfalso
           exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
             (by simpa [__arith_rel_sum] using hBool) rfl)
        case lt =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_lt_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_lt_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)
        case eq =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.leq)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_leq_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_eq_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_eq_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)
        case leq =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.leq)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_leq_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_leq_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_leq_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)
    case eq =>
      cases r2 <;> try
        (exfalso
         exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
           (by simpa [__arith_rel_sum] using hBool) rfl)
      case UOp op2 =>
        cases op2 <;> try
          (exfalso
           exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
             (by simpa [__arith_rel_sum] using hBool) rfl)
        case lt =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_lt_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_lt_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_lt_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)
        case eq =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.leq)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_leq_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_eq_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_eq_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)
        case leq =>
          have hOut : RuleProofs.eo_has_bool_type
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.leq)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2))
                (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) := by
            simpa [__arith_rel_sum] using hBool
          rcases arith_sum_leq_args_of_bool a1 b1 a2 b2 hOut with hInt | hReal
          · exact eo_has_bool_type_leq_of_arith a2 b2
              (Or.inl ⟨hInt.2.2.1, hInt.2.2.2⟩)
          · exact eo_has_bool_type_leq_of_arith a2 b2
              (Or.inr ⟨hReal.2.2.1, hReal.2.2.2⟩)

private theorem arithSumFoldRight_true
    (M : SmtModel) (hM : model_wf M) :
    ∀ (ps : List Term) (acc : Term),
      AllInterpretedTrue M ps ->
      AllHaveBoolType ps ->
      eo_interprets M acc true ->
      RuleProofs.eo_has_bool_type (arithSumFoldRight ps acc) ->
      eo_interprets M (arithSumFoldRight ps acc) true := by
  intro ps acc hTrue hBool hAccTrue hOutBool
  induction ps generalizing acc with
  | nil =>
      simpa [arithSumFoldRight] using hAccTrue
  | cons p ps ih =>
      cases p <;> try
        (exfalso
         exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
           (by simpa [arithSumFoldRight, arithSumStep] using hOutBool) rfl)
      case Apply pf b1 =>
        cases pf <;> try
          (exfalso
           exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
             (by simpa [arithSumFoldRight, arithSumStep] using hOutBool) rfl)
        case Apply r1 a1 =>
          let tail := arithSumFoldRight ps acc
          cases hTailShape : tail <;> try
            (exfalso
             exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
               (by simpa [tail, hTailShape, arithSumFoldRight, arithSumStep] using hOutBool) rfl)
          case Apply tf b2 =>
            cases tf <;> try
              (exfalso
               exact RuleProofs.term_ne_stuck_of_has_bool_type Term.Stuck
                 (by simpa [tail, hTailShape, arithSumFoldRight, arithSumStep] using hOutBool) rfl)
            case Apply r2 a2 =>
              have hTailBool : RuleProofs.eo_has_bool_type tail := by
                have hRight :=
                  arith_rel_sum_right_bool_of_bool r1 r2 a1 b1 a2 b2
                    (by simpa [tail, hTailShape, arithSumFoldRight, arithSumStep] using hOutBool)
                simpa [tail, hTailShape] using hRight
              have hTailTrue : eo_interprets M tail true := by
                apply ih
                · intro t ht
                  exact hTrue t (by simp [ht])
                · intro t ht
                  exact hBool t (by simp [ht])
                · exact hAccTrue
                · exact hTailBool
              have hStepTrue :
                  eo_interprets M
                    (__arith_rel_sum r1 r2
                      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a1) a2)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) b1) b2)) true := by
                exact arith_rel_sum_true M hM r1 r2 a1 b1 a2 b2
                  (hTrue (Term.Apply (Term.Apply r1 a1) b1) (by simp))
                  (by simpa [tail, hTailShape] using hTailTrue)
                  (by simpa [tail, hTailShape, arithSumFoldRight, arithSumStep] using hOutBool)
              simpa [tail, hTailShape, arithSumFoldRight, arithSumStep] using hStepTrue

public theorem cmd_step_arith_sum_ub_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_sum_ub args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_sum_ub args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_sum_ub args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_sum_ub args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      let ps := premiseTermList s premises
      have hMk :
          __eo_mk_premise_list (Term.UOp UserOp.and) premises s =
            premiseAndFormulaList ps := by
        simpa [ps] using mk_premise_list_and_eq_premiseAndFormulaList s premises
      have hProgPs :
          __eo_prog_arith_sum_ub (Proof.pf (premiseAndFormulaList ps)) ≠ Term.Stuck := by
        change __eo_prog_arith_sum_ub
          (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) ≠
            Term.Stuck at hProg
        simpa [hMk] using hProg
      have hResultTyPs :
          __eo_typeof
            (__eo_prog_arith_sum_ub (Proof.pf (premiseAndFormulaList ps))) =
            Term.Bool := by
        change __eo_typeof
          (__eo_prog_arith_sum_ub
            (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) =
            Term.Bool at hResultTy
        simpa [hMk] using hResultTy
      cases hPs : ps with
      | nil =>
          have hStuck :
              __eo_prog_arith_sum_ub (Proof.pf (premiseAndFormulaList [])) =
                Term.Stuck := by
            rfl
          exact False.elim (hProgPs (by simpa [hPs] using hStuck))
      | cons p psTail =>
          cases p with
          | Apply pf b =>
              cases pf with
              | Apply r a =>
                  let rel := Term.Apply (Term.Apply r a) b
                  let acc := arithSumZeroAcc a
                  let fold := arithSumFoldRight (rel :: psTail) acc
                  have hProgEq :
                      __eo_prog_arith_sum_ub
                        (Proof.pf (premiseAndFormulaList (rel :: psTail))) =
                        fold := by
                    simpa [rel, acc, fold, __eo_prog_arith_sum_ub] using
                      mk_arith_sum_ub_eq_fold_right r a b psTail
                  have hFoldTy : __eo_typeof fold = Term.Bool := by
                    simpa [ps, hPs, rel, fold, hProgEq] using hResultTyPs
                  have hFoldNe : fold ≠ Term.Stuck := by
                    simpa [ps, hPs, rel, fold, hProgEq] using hProgPs
                  have hAccNe : acc ≠ Term.Stuck :=
                    arithSumFoldRight_acc_ne_stuck_of_ne_stuck (rel :: psTail) acc hFoldNe
                  have hAccTrue : eo_interprets M acc true := by
                    simpa [acc] using arithSumZeroAcc_true_of_not_stuck M a hAccNe
                  have hAccBool : RuleProofs.eo_has_bool_type acc :=
                    RuleProofs.eo_has_bool_type_of_interprets_true M acc hAccTrue
                  have hPremisesBoolList : AllHaveBoolType (rel :: psTail) := by
                    simpa [ps, hPs, rel] using hPremisesBool
                  have hFoldBool : RuleProofs.eo_has_bool_type fold := by
                    exact arithSumFoldRight_has_bool_type_of_typeof_bool
                      (rel :: psTail) acc hPremisesBoolList hAccBool hFoldTy
                  refine ⟨?_, ?_⟩
                  · intro hPremisesTrue
                    have hPremisesTrueList : AllInterpretedTrue M (rel :: psTail) := by
                      simpa [ps, hPs, rel] using hPremisesTrue.true_here
                    change eo_interprets M
                      (__eo_prog_arith_sum_ub
                        (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s))) true
                    rw [hMk]
                    rw [hPs]
                    rw [show __eo_prog_arith_sum_ub
                        (Proof.pf (premiseAndFormulaList (rel :: psTail))) = fold from hProgEq]
                    exact arithSumFoldRight_true M hM (rel :: psTail) acc
                      hPremisesTrueList hPremisesBoolList hAccTrue hFoldBool
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arith_sum_ub
                        (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)))
                    rw [hMk]
                    rw [hPs]
                    rw [show __eo_prog_arith_sum_ub
                        (Proof.pf (premiseAndFormulaList (rel :: psTail))) = fold from hProgEq]
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type fold hFoldBool
              | _ =>
                  have hStuck :
                      __eo_prog_arith_sum_ub
                        (Proof.pf (premiseAndFormulaList ps)) =
                        Term.Stuck := by
                    rw [hPs]
                    rfl
                  exact False.elim (hProgPs hStuck)
          | _ =>
              have hStuck :
                  __eo_prog_arith_sum_ub
                    (Proof.pf (premiseAndFormulaList ps)) =
                    Term.Stuck := by
                rw [hPs]
                rfl
              exact False.elim (hProgPs hStuck)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
