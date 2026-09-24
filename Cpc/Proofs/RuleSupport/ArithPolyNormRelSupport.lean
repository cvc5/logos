module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.CoreArith
import all Cpc.Proofs.TypePreservation.CoreArith
public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.Proofs.TypePreservation.Helpers

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

noncomputable def arith_atom_denote_real (M : SmtModel) (t : Term) : SmtValue :=
  __smtx_to_real_coerce (__smtx_model_eval M (__eo_to_smt t))

theorem eo_to_smt_to_real_eq
    (x : Term) :
  __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x) =
    SmtTerm.to_real (__eo_to_smt x) := by
  rfl

theorem eo_to_smt_neg_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x) =
    SmtTerm.neg (__eo_to_smt y) (__eo_to_smt x) := by
  rfl

theorem eo_to_smt_mult_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x) =
    SmtTerm.mult (__eo_to_smt y) (__eo_to_smt x) := by
  rfl

theorem eo_to_smt_numeral_eq
    (n : native_Int) :
  __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n := by
  rfl

theorem eo_to_smt_rational_eq
    (q : native_Rat) :
  __eo_to_smt (Term.Rational q) = SmtTerm.Rational q := by
  rfl

theorem eo_to_smt_eq_eq
    (x y : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
    SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

theorem eo_to_smt_lt_eq
    (x y : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) =
    SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

theorem eo_to_smt_leq_eq
    (x y : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) =
    SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

theorem eo_to_smt_gt_eq
    (x y : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y) =
    SmtTerm.gt (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

theorem eo_to_smt_geq_eq
    (x y : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y) =
    SmtTerm.geq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

theorem smtx_model_eval_to_real_idempotent
    (v : SmtValue) :
  __smtx_to_real_coerce (__smtx_to_real_coerce v) =
    __smtx_to_real_coerce v := by
  cases v <;> simp [__smtx_to_real_coerce]

theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← eo_to_smt_eq_eq x y]
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

theorem rel_operands_arith_type_of_lt_has_bool_type
    (x y : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) ->
  (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
    __smtx_typeof (__eo_to_smt y) = SmtType.Int) ∨
  (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
    __smtx_typeof (__eo_to_smt y) = SmtType.Real) := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eo_to_smt_lt_eq] using hTy
  have hNN : term_has_non_none_type (SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  exact arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt)
    (typeof_lt_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem rel_operands_arith_type_of_leq_has_bool_type
    (x y : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) ->
  (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
    __smtx_typeof (__eo_to_smt y) = SmtType.Int) ∨
  (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
    __smtx_typeof (__eo_to_smt y) = SmtType.Real) := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eo_to_smt_leq_eq] using hTy
  have hNN : term_has_non_none_type (SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  exact arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
    (typeof_leq_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem rel_operands_arith_type_of_gt_has_bool_type
    (x y : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y) ->
  (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
    __smtx_typeof (__eo_to_smt y) = SmtType.Int) ∨
  (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
    __smtx_typeof (__eo_to_smt y) = SmtType.Real) := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.gt (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eo_to_smt_gt_eq] using hTy
  have hNN : term_has_non_none_type (SmtTerm.gt (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  exact arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt)
    (typeof_gt_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem rel_operands_arith_type_of_geq_has_bool_type
    (x y : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y) ->
  (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
    __smtx_typeof (__eo_to_smt y) = SmtType.Int) ∨
  (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
    __smtx_typeof (__eo_to_smt y) = SmtType.Real) := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.geq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type, eo_to_smt_geq_eq] using hTy
  have hNN : term_has_non_none_type (SmtTerm.geq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  exact arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
    (typeof_geq_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
  __eo_requires x y z ≠ Term.Stuck ->
  x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · exfalso
    have hNe : native_teq x y = false := by
      simp [native_teq, hxy]
    simp [__eo_requires, hNe, native_ite] at hReq

theorem eo_requires_body_ne_stuck_of_ne_stuck
    {x y z : Term} :
  __eo_requires x y z ≠ Term.Stuck ->
  z ≠ Term.Stuck := by
  intro hReq
  have hxy : x = y := eo_requires_arg_eq_of_ne_stuck hReq
  by_cases hxSt : x = Term.Stuck
  · subst x
    subst y
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not] at hReq
  · intro hz
    subst z
    have hReqSt : __eo_requires x y Term.Stuck = Term.Stuck := by
      simp [__eo_requires, hxy, native_teq, native_ite, native_not,
        SmtEval.native_not]
    exact hReq hReqSt

theorem eo_and_true
    {x y : Term} :
  __eo_and x y = Term.Boolean true ->
  x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢

theorem eo_eq_true_eq
    {x y : Term} :
  __eo_eq x y = Term.Boolean true ->
  x = y := by
  intro h
  by_cases hxSt : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  by_cases hySt : y = Term.Stuck
  · subst y
    simp [__eo_eq] at h
  have hyx : y = x := by
    simpa [__eo_eq, hxSt, hySt, native_teq] using h
  exact hyx.symm

theorem is_eq_maybe_to_real_true
    {x d : Term} :
    __is_eq_maybe_to_real x d = Term.Boolean true ->
    x = d ∨ x = Term.Apply (Term.UOp UserOp.to_real) d := by
  intro h
  by_cases hxSt : x = Term.Stuck
  · subst x
    simp [__is_eq_maybe_to_real] at h
  by_cases hdSt : d = Term.Stuck
  · subst d
    cases x <;> simp [__is_eq_maybe_to_real] at h
  by_cases hxd : x = d
  · exact Or.inl hxd
  · right
    have hdx : ¬d = x := by
      intro hdx
      exact hxd hdx.symm
    have hIteFalse : native_teq (__eo_eq x d) (Term.Boolean true) = false := by
      simp [__eo_eq, native_teq, hdx]
    have hIteTrueFalse : native_teq (__eo_eq x d) (Term.Boolean false) = true := by
      simp [__eo_eq, native_teq, hdx]
    have hL1 : __eo_l_1___is_eq_maybe_to_real x d = Term.Boolean true := by
      simpa [__is_eq_maybe_to_real, __eo_ite, native_ite, hIteFalse, hIteTrueFalse] using h
    cases x with
    | Apply f z =>
        cases f with
        | UOp op =>
            cases op <;> simp [__eo_l_1___is_eq_maybe_to_real, __eo_requires,
              __eo_eq, native_teq, native_ite, native_not, SmtEval.native_not] at hL1 ⊢
            by_cases hzSt : z = Term.Stuck
            · subst z
              simp at hL1
            · by_cases hzd : z = d
              · exact hzd
              · have hdz : ¬d = z := by
                  intro hdz
                  exact hzd hdz.symm
                simp [hdz] at hL1
        | _ => simp [__eo_l_1___is_eq_maybe_to_real] at hL1
    | _ => simp [__eo_l_1___is_eq_maybe_to_real] at hL1

theorem native_to_real_neg
    (n : native_Int) :
  native_to_real (native_zneg n) = native_qneg (native_to_real n) := by
  change (-((n : Rat)) * ((1 : Rat)⁻¹)) = -((n : Rat) * ((1 : Rat)⁻¹))
  exact Rat.neg_mul _ _

theorem native_to_real_add
    (n1 n2 : native_Int) :
  native_to_real (native_zplus n1 n2) =
    native_qplus (native_to_real n1) (native_to_real n2) := by
  rw [native_to_real, native_to_real, native_to_real, native_qplus, native_zplus,
    native_mk_rational, native_mk_rational, native_mk_rational]
  rw [← Rat.divInt_eq_div, ← Rat.divInt_eq_div, ← Rat.divInt_eq_div]
  simp [Int.mul_one]

theorem native_to_real_sub
    (n1 n2 : native_Int) :
  native_to_real (native_zplus n1 (native_zneg n2)) =
    native_qplus (native_to_real n1) (native_qneg (native_to_real n2)) := by
  rw [native_to_real_add, native_to_real_neg]

theorem native_to_real_mul
    (n1 n2 : native_Int) :
  native_to_real (native_zmult n1 n2) =
    native_qmult (native_to_real n1) (native_to_real n2) := by
  rw [native_to_real, native_to_real, native_to_real, native_qmult, native_zmult,
    native_mk_rational, native_mk_rational, native_mk_rational]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 n2 (d₁ := 1) (d₂ := 1)).symm

theorem arith_atom_denote_real_of_to_real
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hInt : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
  arith_atom_denote_real M (Term.Apply (Term.UOp UserOp.to_real) t) =
    arith_atom_denote_real M t := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
    simpa [hInt] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simp [term_has_non_none_type, hInt])
  rcases int_value_canonical hEvalTy with ⟨n, hEval⟩
  unfold arith_atom_denote_real
  rw [eo_to_smt_to_real_eq]
  rw [__smtx_model_eval.eq_21, hEval]
  simp [__smtx_model_eval_to_real, __smtx_to_real_coerce]

theorem arith_atom_denote_real_of_neg
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Real) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
    __smtx_model_eval_plus (arith_atom_denote_real M t1)
      (__smtx_model_eval_uneg (arith_atom_denote_real M t2)) := by
  have ht : term_has_non_none_type (SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
          SmtType.None := by
      rw [eo_to_smt_neg_eq]
      exact hNone
    rcases hTy with hTy | hTy
    · cases hTy.symm.trans hNone'
    · cases hTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      have hNN : term_has_non_none_type (__eo_to_smt t1) := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        decide
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        hNN
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      have hNN : term_has_non_none_type (__eo_to_smt t2) := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        decide
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        hNN
    have hEval1TyInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) = SmtType.Int := by
      rw [hEval1Ty, hArgs.1]
    have hEval2TyInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) = SmtType.Int := by
      rw [hEval2Ty, hArgs.2]
    rcases int_value_canonical hEval1TyInt with ⟨n1, hEval1⟩
    rcases int_value_canonical hEval2TyInt with ⟨n2, hEval2⟩
    unfold arith_atom_denote_real
    rw [eo_to_smt_neg_eq, __smtx_model_eval.eq_15, hEval1, hEval2]
    simp only [__smtx_to_real_coerce, __smtx_model_eval_plus, __smtx_model_eval_uneg,
      __smtx_model_eval__, native_to_real_sub]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      have hNN : term_has_non_none_type (__eo_to_smt t1) := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        decide
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        hNN
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      have hNN : term_has_non_none_type (__eo_to_smt t2) := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        decide
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        hNN
    have hEval1TyReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) = SmtType.Real := by
      rw [hEval1Ty, hArgs.1]
    have hEval2TyReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) = SmtType.Real := by
      rw [hEval2Ty, hArgs.2]
    rcases real_value_canonical hEval1TyReal with ⟨q1, hEval1⟩
    rcases real_value_canonical hEval2TyReal with ⟨q2, hEval2⟩
    unfold arith_atom_denote_real
    rw [eo_to_smt_neg_eq, __smtx_model_eval.eq_15, hEval1, hEval2]
    simp only [__smtx_to_real_coerce, __smtx_model_eval_plus, __smtx_model_eval_uneg,
      __smtx_model_eval__]

theorem arith_atom_denote_real_of_mult
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Real) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
    __smtx_model_eval_mult (arith_atom_denote_real M t1) (arith_atom_denote_real M t2) := by
  have ht : term_has_non_none_type (SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
          SmtType.None := by
      rw [eo_to_smt_mult_eq]
      exact hNone
    rcases hTy with hTy | hTy
    · cases hTy.symm.trans hNone'
    · cases hTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      have hNN : term_has_non_none_type (__eo_to_smt t1) := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        decide
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        hNN
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      have hNN : term_has_non_none_type (__eo_to_smt t2) := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        decide
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        hNN
    have hEval1TyInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) = SmtType.Int := by
      rw [hEval1Ty, hArgs.1]
    have hEval2TyInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) = SmtType.Int := by
      rw [hEval2Ty, hArgs.2]
    rcases int_value_canonical hEval1TyInt with ⟨n1, hEval1⟩
    rcases int_value_canonical hEval2TyInt with ⟨n2, hEval2⟩
    unfold arith_atom_denote_real
    rw [eo_to_smt_mult_eq]
    rw [__smtx_model_eval.eq_16, hEval1, hEval2]
    simp only [__smtx_to_real_coerce,
      __smtx_model_eval_mult, native_to_real_mul]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      have hNN : term_has_non_none_type (__eo_to_smt t1) := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        decide
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        hNN
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      have hNN : term_has_non_none_type (__eo_to_smt t2) := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        decide
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        hNN
    have hEval1TyReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) = SmtType.Real := by
      rw [hEval1Ty, hArgs.1]
    have hEval2TyReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) = SmtType.Real := by
      rw [hEval2Ty, hArgs.2]
    rcases real_value_canonical hEval1TyReal with ⟨q1, hEval1⟩
    rcases real_value_canonical hEval2TyReal with ⟨q2, hEval2⟩
    unfold arith_atom_denote_real
    rw [eo_to_smt_mult_eq]
    rw [__smtx_model_eval.eq_16, hEval1, hEval2]
    simp only [__smtx_to_real_coerce,
      __smtx_model_eval_mult]

theorem arith_atom_denote_real_eq_of_smt_value_rel
    (M : SmtModel) (a b : Term) :
  RuleProofs.smt_value_rel (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) ->
  arith_atom_denote_real M a = arith_atom_denote_real M b := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel
  unfold arith_atom_denote_real
  cases hA : __smtx_model_eval M (__eo_to_smt a) <;>
    cases hB : __smtx_model_eval M (__eo_to_smt b) <;>
    simp [__smtx_model_eval_eq, native_veq, __smtx_to_real_coerce, hA, hB] at hRel ⊢
  all_goals
    try subst_vars
    try rfl
    try exact hRel
    try exact hRel.symm
    try exact False.elim hRel

theorem arith_atom_denote_real_of_to_q
    (M : SmtModel) (t : Term) (q : native_Rat) :
  __eo_to_q t = Term.Rational q ->
  arith_atom_denote_real M t = SmtValue.Rational q := by
  intro h
  cases t <;> simp [__eo_to_q] at h
  · cases h
    unfold arith_atom_denote_real
    rw [eo_to_smt_numeral_eq, __smtx_model_eval.eq_2]
    rfl
  · cases h
    unfold arith_atom_denote_real
    rw [eo_to_smt_rational_eq, __smtx_model_eval.eq_3]
    rfl

def arith_poly_norm_rel_const_sign (t : Term) : Term :=
  __eo_ite (__eo_is_neg t)
    (Term.Numeral (-1 : native_Int))
    (__eo_ite (__eo_is_neg (__eo_neg t))
      (Term.Numeral 1)
      (Term.Numeral 0))

def rat_sign_term (q : native_Rat) : Term :=
  if native_qlt q (native_mk_rational 0 1) then
    Term.Numeral (-1 : native_Int)
  else if native_qlt (native_qneg q) (native_mk_rational 0 1) then
    Term.Numeral 1
  else
    Term.Numeral 0

theorem rat_mkRat_one_eq_intCast
    (n : native_Int) :
  mkRat n 1 = (n : Rat) := by
  unfold mkRat
  simp
  rw [Rat.normalize_eq]
  simp

theorem rat_div_one_intCast
    (n : native_Int) :
  ((n : Rat) / (1 : Rat)) = (n : Rat) := by
  change ((n : Rat) / ((1 : Int) : Rat)) = (n : Rat)
  rw [← Rat.divInt_eq_div n 1]
  change Rat.divInt n ((1 : Nat) : Int) = (n : Rat)
  rw [Rat.divInt_ofNat]
  exact rat_mkRat_one_eq_intCast n

theorem rat_zero_div_one :
  ((0 : Rat) / (1 : Rat)) = (0 : Rat) := by
  change (((0 : Int) : Rat) / ((1 : Int) : Rat)) = (((0 : Int) : Rat))
  exact rat_div_one_intCast 0

theorem native_mk_rational_zero :
  native_mk_rational 0 1 = (0 : Rat) := by
  native_decide

theorem native_mk_rational_one :
  native_mk_rational 1 1 = (1 : Rat) := by
  native_decide

theorem intCast_lt_zero_iff
    (n : native_Int) :
  ((n : Rat) < 0) ↔ n < 0 := by
  have hCast : (0 < (-(n : Rat)) ↔ 0 < -n) := by
    simpa [Rat.intCast_neg] using (Rat.intCast_pos (a := -n))
  have hRat : (0 < (-(n : Rat)) ↔ (n : Rat) < 0) := by
    simpa using (Rat.lt_neg_iff (a := (0 : Rat)) (b := (n : Rat)))
  calc
    (n : Rat) < 0 ↔ 0 < -(n : Rat) := hRat.symm
    _ ↔ 0 < -n := hCast
    _ ↔ n < 0 := Int.neg_pos

theorem native_to_real_lt_zero_eq
    (n : native_Int) :
  native_qlt (native_to_real n) (native_mk_rational 0 1) =
    native_zlt n 0 := by
  unfold native_qlt native_to_real native_mk_rational native_zlt
  have hiff : (((n : Rat) / (1 : Rat)) < ((0 : Rat) / (1 : Rat)) ↔ n < 0) := by
    rw [rat_div_one_intCast n, rat_zero_div_one]
    exact intCast_lt_zero_iff n
  by_cases hL : ((n : Rat) / (1 : Rat)) < ((0 : Rat) / (1 : Rat))
  · have hR : n < 0 := hiff.mp hL
    simp [hL, hR]
  · have hR : ¬ n < 0 := fun h => hL (hiff.mpr h)
    simp [hL, hR]

theorem native_to_real_neg_lt_zero_eq
    (n : native_Int) :
  native_qlt (native_qneg (native_to_real n)) (native_mk_rational 0 1) =
    native_zlt (native_zneg n) 0 := by
  rw [← native_to_real_neg, native_to_real_lt_zero_eq]

theorem native_qlt_zero_eq_decide
    (q : native_Rat) :
  native_qlt q (native_mk_rational 0 1) = decide (q < 0) := by
  unfold native_qlt
  change decide (q < native_mk_rational 0 1) = decide (q < 0)
  rw [show native_mk_rational 0 1 = (0 : Rat) by
    unfold native_mk_rational
    exact rat_zero_div_one]

theorem arith_poly_norm_rel_const_sign_of_to_q
    (t : Term) (q : native_Rat) :
  __eo_to_q t = Term.Rational q ->
  arith_poly_norm_rel_const_sign t = rat_sign_term q := by
  intro h
  cases t <;> simp [__eo_to_q] at h
  case Numeral n =>
    cases h
    simp only [arith_poly_norm_rel_const_sign, rat_sign_term, __eo_is_neg, __eo_neg,
      __eo_ite, native_teq, native_ite, native_to_real_lt_zero_eq,
      native_to_real_neg_lt_zero_eq]
    by_cases hneg : native_zlt n 0 = true
    · simp [hneg]
    · have hnegFalse : native_zlt n 0 = false :=
        Bool.eq_false_iff.mpr hneg
      by_cases hpos : native_zlt (native_zneg n) 0 = true
      · simp [hnegFalse, hpos]
      · have hposFalse : native_zlt (native_zneg n) 0 = false :=
          Bool.eq_false_iff.mpr hpos
        simp [hnegFalse, hposFalse]
  case Rational q =>
    cases h
    simp only [arith_poly_norm_rel_const_sign, rat_sign_term, __eo_is_neg, __eo_neg,
      __eo_ite, native_teq, native_ite]
    by_cases hneg : native_qlt q (native_mk_rational 0 1) = true
    · simp [hneg]
    · have hnegFalse : native_qlt q (native_mk_rational 0 1) = false :=
        Bool.eq_false_iff.mpr hneg
      by_cases hpos : native_qlt (native_qneg q) (native_mk_rational 0 1) = true
      · simp [hnegFalse, hpos]
      · have hposFalse :
            native_qlt (native_qneg q) (native_mk_rational 0 1) = false :=
          Bool.eq_false_iff.mpr hpos
        simp [hnegFalse, hposFalse]

theorem rat_same_sign_of_sign_term_eq
    {c d : native_Rat} :
  rat_sign_term c = rat_sign_term d ->
  c ≠ 0 ->
  d ≠ 0 ->
  (0 < c ∧ 0 < d) ∨ (c < 0 ∧ d < 0) := by
  intro hSign hc0 hd0
  by_cases hcneg : c < 0
  · by_cases hdneg : d < 0
    · exact Or.inr ⟨hcneg, hdneg⟩
    · have hdpos : 0 < d := by grind
      have hdneg' : -d < 0 := by grind
      simp [rat_sign_term, native_qlt_zero_eq_decide, native_qneg, hcneg, hdneg,
        hdneg'] at hSign
  · have hcpos : 0 < c := by grind
    have hcneg' : -c < 0 := by grind
    by_cases hdneg : d < 0
    · have hdnneg' : ¬ -d < 0 := by grind
      simp [rat_sign_term, native_qlt_zero_eq_decide, native_qneg, hcneg,
        hcneg', hdneg] at hSign
    · have hdpos : 0 < d := by grind
      exact Or.inl ⟨hcpos, hdpos⟩

theorem eo_not_true_eq_false
    {x : Term} :
  __eo_not x = Term.Boolean true ->
  x = Term.Boolean false := by
  intro h
  cases x <;> simp [__eo_not] at h
  case Boolean b =>
    cases b <;> simp [SmtEval.native_not] at h ⊢

theorem eo_or_false
    {x y : Term} :
  __eo_or x y = Term.Boolean false ->
  x = Term.Boolean false ∧ y = Term.Boolean false := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_or, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [SmtEval.native_or] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h

theorem eo_eq_false_ne
    {x y : Term} :
  __eo_eq x y = Term.Boolean false ->
  x ≠ y := by
  intro h hxy
  subst y
  cases x <;> simp [__eo_eq, native_teq] at h

theorem eo_to_q_exists_of_ne_stuck
    (t : Term) :
  __eo_to_q t ≠ Term.Stuck ->
  ∃ q : native_Rat, __eo_to_q t = Term.Rational q := by
  intro h
  cases t <;> simp [__eo_to_q] at h ⊢

theorem is_poly_norm_rel_consts_true_info
    (r cx cy : Term) :
  __is_poly_norm_rel_consts (Term.Apply (Term.Apply r cx) cy) = Term.Boolean true ->
  ∃ c d : native_Rat,
    __eo_to_q cx = Term.Rational c ∧
    __eo_to_q cy = Term.Rational d ∧
    c ≠ 0 ∧
    d ≠ 0 ∧
    __is_poly_norm_rel_consts_rel (Term.Apply (Term.Apply r cx) cy) =
      Term.Boolean true := by
  intro h
  have hParts :
      __eo_not
          (__eo_or
            (__eo_eq (__eo_to_q cx) (Term.Rational (native_mk_rational 0 1)))
            (__eo_eq (__eo_to_q cy) (Term.Rational (native_mk_rational 0 1)))) =
          Term.Boolean true ∧
        __is_poly_norm_rel_consts_rel (Term.Apply (Term.Apply r cx) cy) =
          Term.Boolean true := by
    exact eo_and_true (by simpa [__is_poly_norm_rel_consts] using h)
  have hOrFalse :
      __eo_or
          (__eo_eq (__eo_to_q cx) (Term.Rational (native_mk_rational 0 1)))
          (__eo_eq (__eo_to_q cy) (Term.Rational (native_mk_rational 0 1))) =
        Term.Boolean false :=
    eo_not_true_eq_false hParts.1
  have hZeroParts := eo_or_false hOrFalse
  have hCxNotStuck : __eo_to_q cx ≠ Term.Stuck := by
    intro hSt
    rw [hSt] at hZeroParts
    simp [__eo_eq] at hZeroParts
  have hCyNotStuck : __eo_to_q cy ≠ Term.Stuck := by
    intro hSt
    rw [hSt] at hZeroParts
    simp [__eo_eq] at hZeroParts
  rcases eo_to_q_exists_of_ne_stuck cx hCxNotStuck with ⟨c, hcx⟩
  rcases eo_to_q_exists_of_ne_stuck cy hCyNotStuck with ⟨d, hcy⟩
  have hc0 : c ≠ 0 := by
    intro hc
    apply eo_eq_false_ne hZeroParts.1
    rw [hcx, hc]
    congr
    unfold native_mk_rational
    exact rat_zero_div_one.symm
  have hd0 : d ≠ 0 := by
    intro hd
    apply eo_eq_false_ne hZeroParts.2
    rw [hcy, hd]
    congr
    unfold native_mk_rational
    exact rat_zero_div_one.symm
  exact ⟨c, d, hcx, hcy, hc0, hd0, hParts.2⟩

theorem same_sign_of_is_poly_norm_rel_consts_rel_true_lt
    {cx cy : Term} {c d : native_Rat} :
  __is_poly_norm_rel_consts_rel
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) cx) cy) =
    Term.Boolean true ->
  __eo_to_q cx = Term.Rational c ->
  __eo_to_q cy = Term.Rational d ->
  c ≠ 0 ->
  d ≠ 0 ->
  (0 < c ∧ 0 < d) ∨ (c < 0 ∧ d < 0) := by
  intro hRel hcx hcy hc0 hd0
  have hSignEq :
      arith_poly_norm_rel_const_sign cx =
        arith_poly_norm_rel_const_sign cy := by
    exact eo_eq_true_eq (by
      simpa [__is_poly_norm_rel_consts_rel, arith_poly_norm_rel_const_sign] using hRel)
  rw [arith_poly_norm_rel_const_sign_of_to_q cx c hcx,
    arith_poly_norm_rel_const_sign_of_to_q cy d hcy] at hSignEq
  exact rat_same_sign_of_sign_term_eq hSignEq hc0 hd0

theorem same_sign_of_is_poly_norm_rel_consts_rel_true_leq
    {cx cy : Term} {c d : native_Rat} :
  __is_poly_norm_rel_consts_rel
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) cx) cy) =
    Term.Boolean true ->
  __eo_to_q cx = Term.Rational c ->
  __eo_to_q cy = Term.Rational d ->
  c ≠ 0 ->
  d ≠ 0 ->
  (0 < c ∧ 0 < d) ∨ (c < 0 ∧ d < 0) := by
  intro hRel hcx hcy hc0 hd0
  exact same_sign_of_is_poly_norm_rel_consts_rel_true_lt
    (cx := cx) (cy := cy) (c := c) (d := d)
    (by simpa [__is_poly_norm_rel_consts_rel] using hRel) hcx hcy hc0 hd0

theorem same_sign_of_is_poly_norm_rel_consts_rel_true_gt
    {cx cy : Term} {c d : native_Rat} :
  __is_poly_norm_rel_consts_rel
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) cx) cy) =
    Term.Boolean true ->
  __eo_to_q cx = Term.Rational c ->
  __eo_to_q cy = Term.Rational d ->
  c ≠ 0 ->
  d ≠ 0 ->
  (0 < c ∧ 0 < d) ∨ (c < 0 ∧ d < 0) := by
  intro hRel hcx hcy hc0 hd0
  exact same_sign_of_is_poly_norm_rel_consts_rel_true_lt
    (cx := cx) (cy := cy) (c := c) (d := d)
    (by simpa [__is_poly_norm_rel_consts_rel] using hRel) hcx hcy hc0 hd0

theorem same_sign_of_is_poly_norm_rel_consts_rel_true_geq
    {cx cy : Term} {c d : native_Rat} :
  __is_poly_norm_rel_consts_rel
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) cx) cy) =
    Term.Boolean true ->
  __eo_to_q cx = Term.Rational c ->
  __eo_to_q cy = Term.Rational d ->
  c ≠ 0 ->
  d ≠ 0 ->
  (0 < c ∧ 0 < d) ∨ (c < 0 ∧ d < 0) := by
  intro hRel hcx hcy hc0 hd0
  exact same_sign_of_is_poly_norm_rel_consts_rel_true_lt
    (cx := cx) (cy := cy) (c := c) (d := d)
    (by simpa [__is_poly_norm_rel_consts_rel] using hRel) hcx hcy hc0 hd0

theorem rat_scaled_zero_iff {c x : Rat} (hc : c ≠ 0) : c * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h | h
    · contradiction
    · exact h
  · intro h
    simp [h, Rat.mul_zero]

theorem rat_same_sign_core_pos {c d x y : Rat}
    (h : c * x = d * y) (hc : 0 < c) (hd : 0 < d) :
    (x < 0 ↔ y < 0) ∧ (0 < x ↔ 0 < y) ∧ (x = 0 ↔ y = 0) := by
  constructor
  · constructor
    · intro hx
      have hcx : c * x < 0 := (Rat.mul_neg_iff_of_pos_left hc).mpr hx
      have hdy : d * y < 0 := by rwa [h] at hcx
      exact (Rat.mul_neg_iff_of_pos_left hd).mp hdy
    · intro hy
      have hdy : d * y < 0 := (Rat.mul_neg_iff_of_pos_left hd).mpr hy
      have hcx : c * x < 0 := by rwa [← h] at hdy
      exact (Rat.mul_neg_iff_of_pos_left hc).mp hcx
  constructor
  · constructor
    · intro hx
      have hcx : 0 < c * x := (Rat.mul_pos_iff_of_pos_left hc).mpr hx
      have hdy : 0 < d * y := by rwa [h] at hcx
      exact (Rat.mul_pos_iff_of_pos_left hd).mp hdy
    · intro hy
      have hdy : 0 < d * y := (Rat.mul_pos_iff_of_pos_left hd).mpr hy
      have hcx : 0 < c * x := by rwa [← h] at hdy
      exact (Rat.mul_pos_iff_of_pos_left hc).mp hcx
  · constructor
    · intro hx
      have hcx : c * x = 0 := by simp [hx, Rat.mul_zero]
      have hdy : d * y = 0 := by rwa [h] at hcx
      rcases Rat.mul_eq_zero.mp hdy with hd0 | hy0
      · exact False.elim (Rat.ne_of_gt hd hd0)
      · exact hy0
    · intro hy
      have hdy : d * y = 0 := by simp [hy, Rat.mul_zero]
      have hcx : c * x = 0 := by rwa [← h] at hdy
      rcases Rat.mul_eq_zero.mp hcx with hc0 | hx0
      · exact False.elim (Rat.ne_of_gt hc hc0)
      · exact hx0

theorem rat_same_sign_core_neg {c d x y : Rat}
    (h : c * x = d * y) (hc : c < 0) (hd : d < 0) :
    (x < 0 ↔ y < 0) ∧ (0 < x ↔ 0 < y) ∧ (x = 0 ↔ y = 0) := by
  have hposc : 0 < -c := by
    exact (Rat.lt_neg_iff (a := 0) (b := c)).mpr (by simpa using hc)
  have hposd : 0 < -d := by
    exact (Rat.lt_neg_iff (a := 0) (b := d)).mpr (by simpa using hd)
  have hneg : (-c) * x = (-d) * y := by rw [Rat.neg_mul, Rat.neg_mul, h]
  exact rat_same_sign_core_pos hneg hposc hposd

theorem native_qlt_zero_eq_of_iff {x y : Rat} (h : (x < 0 ↔ y < 0)) :
    native_qlt x 0 = native_qlt y 0 := by
  unfold native_qlt
  grind

theorem native_qgt_zero_eq_of_iff {x y : Rat} (h : (0 < x ↔ 0 < y)) :
    native_qlt 0 x = native_qlt 0 y := by
  unfold native_qlt
  grind

theorem native_qeq_zero_eq_of_iff {x y : Rat} (h : (x = 0 ↔ y = 0)) :
    native_qeq x 0 = native_qeq y 0 := by
  unfold native_qeq
  grind

theorem native_qleq_zero_eq_of_sign {x y : Rat}
    (hlt : (x < 0 ↔ y < 0)) (heq : (x = 0 ↔ y = 0)) :
    native_qleq x 0 = native_qleq y 0 := by
  unfold native_qleq
  have hle : (x ≤ 0 ↔ y ≤ 0) := by
    rw [Rat.le_iff_lt_or_eq, Rat.le_iff_lt_or_eq]
    grind
  grind

theorem native_qgeq_zero_eq_of_sign {x y : Rat}
    (hgt : (0 < x ↔ 0 < y)) (heq : (x = 0 ↔ y = 0)) :
    native_qleq 0 x = native_qleq 0 y := by
  unfold native_qleq
  have hle : (0 ≤ x ↔ 0 ≤ y) := by
    rw [Rat.le_iff_lt_or_eq, Rat.le_iff_lt_or_eq]
    grind
  grind

theorem smt_eval_int_of_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    ∃ n : native_Int, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral n := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact int_value_canonical (by simpa [hTy] using hPres)

theorem smt_eval_real_of_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    ∃ q : native_Rat, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Rational q := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact real_value_canonical (by simpa [hTy] using hPres)

theorem native_zsub_lt_zero_eq
    (n1 n2 : Int) :
  native_zlt (native_zplus n1 (native_zneg n2)) 0 =
    native_zlt n1 n2 := by
  unfold native_zlt native_zplus native_zneg
  have hiff : n1 + -n2 < 0 ↔ n1 < n2 := by omega
  by_cases hL : n1 + -n2 < 0
  · have hR : n1 < n2 := hiff.mp hL
    simp [hL, hR]
  · have hR : ¬ n1 < n2 := fun h => hL (hiff.mpr h)
    simp [hL, hR]

theorem native_zsub_leq_zero_eq
    (n1 n2 : Int) :
  native_zleq (native_zplus n1 (native_zneg n2)) 0 =
    native_zleq n1 n2 := by
  unfold native_zleq native_zplus native_zneg
  have hiff : n1 + -n2 ≤ 0 ↔ n1 ≤ n2 := by omega
  by_cases hL : n1 + -n2 ≤ 0
  · have hR : n1 ≤ n2 := hiff.mp hL
    simp [hL, hR]
  · have hR : ¬ n1 ≤ n2 := fun h => hL (hiff.mpr h)
    simp [hL, hR]

theorem native_zsub_gt_zero_eq
    (n1 n2 : Int) :
  native_zlt 0 (native_zplus n1 (native_zneg n2)) =
    native_zlt n2 n1 := by
  unfold native_zlt native_zplus native_zneg
  have hiff : 0 < n1 + -n2 ↔ n2 < n1 := by omega
  by_cases hL : 0 < n1 + -n2
  · have hR : n2 < n1 := hiff.mp hL
    simp [hL, hR]
  · have hR : ¬ n2 < n1 := fun h => hL (hiff.mpr h)
    simp [hL, hR]

theorem native_zsub_geq_zero_eq
    (n1 n2 : Int) :
  native_zleq 0 (native_zplus n1 (native_zneg n2)) =
    native_zleq n2 n1 := by
  unfold native_zleq native_zplus native_zneg
  have hiff : 0 ≤ n1 + -n2 ↔ n2 ≤ n1 := by omega
  by_cases hL : 0 ≤ n1 + -n2
  · have hR : n2 ≤ n1 := hiff.mp hL
    simp [hL, hR]
  · have hR : ¬ n2 ≤ n1 := fun h => hL (hiff.mpr h)
    simp [hL, hR]

theorem native_zsub_eq_zero_eq
    (n1 n2 : Int) :
  native_zeq (native_zplus n1 (native_zneg n2)) 0 =
    native_zeq n1 n2 := by
  unfold native_zeq native_zplus native_zneg
  have hiff : n1 + -n2 = 0 ↔ n1 = n2 := by omega
  by_cases hL : n1 + -n2 = 0
  · have hR : n1 = n2 := hiff.mp hL
    subst n1
    simp [Int.add_right_neg]
  · have hR : ¬ n1 = n2 := fun h => hL (hiff.mpr h)
    simp [hL, hR]

theorem native_to_real_sub_lt_zero_eq
    (n1 n2 : Int) :
  native_qlt (native_qplus (native_to_real n1) (native_qneg (native_to_real n2)))
      (native_mk_rational 0 1) =
    native_zlt n1 n2 := by
  rw [← native_to_real_sub, native_to_real_lt_zero_eq, native_zsub_lt_zero_eq]

theorem native_to_real_gt_zero_eq
    (n : Int) :
  native_qlt (native_mk_rational 0 1) (native_to_real n) =
    native_zlt 0 n := by
  unfold native_qlt native_to_real native_mk_rational native_zlt
  have hiff : (((0 : Rat) / (1 : Rat)) < ((n : Rat) / (1 : Rat)) ↔ 0 < n) := by
    rw [rat_zero_div_one, rat_div_one_intCast n]
    exact Rat.intCast_pos
  by_cases hL : ((0 : Rat) / (1 : Rat)) < ((n : Rat) / (1 : Rat))
  · have hR : 0 < n := hiff.mp hL
    simp [hL, hR]
  · have hR : ¬ 0 < n := fun h => hL (hiff.mpr h)
    simp [hL, hR]

theorem native_to_real_sub_gt_zero_eq
    (n1 n2 : Int) :
  native_qlt (native_mk_rational 0 1)
      (native_qplus (native_to_real n1) (native_qneg (native_to_real n2))) =
    native_zlt n2 n1 := by
  rw [← native_to_real_sub, native_to_real_gt_zero_eq, native_zsub_gt_zero_eq]

theorem native_to_real_eq_zero_eq
    (n : Int) :
  native_qeq (native_to_real n) (native_mk_rational 0 1) =
    native_zeq n 0 := by
  unfold native_qeq native_to_real native_mk_rational native_zeq
  have hiff : (((n : Rat) / (1 : Rat)) = ((0 : Rat) / (1 : Rat)) ↔ n = 0) := by
    rw [rat_div_one_intCast n, rat_zero_div_one]
    rw [show (0 : Rat) = ((0 : Int) : Rat) by rfl]
    exact Rat.intCast_inj
  by_cases hL : ((n : Rat) / (1 : Rat)) = ((0 : Rat) / (1 : Rat))
  · have hR : n = 0 := hiff.mp hL
    simp [hR]
  · have hR : ¬ n = 0 := fun h => hL (hiff.mpr h)
    simp [hL, hR]

theorem native_to_real_sub_eq_zero_eq
    (n1 n2 : Int) :
  native_qeq (native_qplus (native_to_real n1) (native_qneg (native_to_real n2)))
      (native_mk_rational 0 1) =
    native_zeq n1 n2 := by
  rw [← native_to_real_sub, native_to_real_eq_zero_eq, native_zsub_eq_zero_eq]

theorem native_qleq_zero_eq_not_gt
    (q : native_Rat) :
  native_qleq q (native_mk_rational 0 1) =
    Bool.not (native_qlt (native_mk_rational 0 1) q) := by
  unfold native_qleq native_qlt
  rw [show native_mk_rational 0 1 = (0 : Rat) by
    unfold native_mk_rational
    exact rat_zero_div_one]
  grind

theorem native_qgeq_zero_eq_not_lt
    (q : native_Rat) :
  native_qleq (native_mk_rational 0 1) q =
    Bool.not (native_qlt q (native_mk_rational 0 1)) := by
  unfold native_qleq native_qlt
  rw [show native_mk_rational 0 1 = (0 : Rat) by
    unfold native_mk_rational
    exact rat_zero_div_one]
  grind

theorem native_zleq_eq_not_gt
    (n1 n2 : Int) :
  native_zleq n1 n2 = Bool.not (native_zlt n2 n1) := by
  unfold native_zleq native_zlt
  have hiff : n1 ≤ n2 ↔ ¬ n2 < n1 := by omega
  by_cases hL : n1 ≤ n2
  · have hR : ¬ n2 < n1 := hiff.mp hL
    simp [hL, hR]
  · have hR : n2 < n1 := by omega
    simp [hL, hR]

theorem native_to_real_sub_leq_zero_eq
    (n1 n2 : Int) :
  native_qleq (native_qplus (native_to_real n1) (native_qneg (native_to_real n2)))
      (native_mk_rational 0 1) =
    native_zleq n1 n2 := by
  rw [native_qleq_zero_eq_not_gt,
    native_to_real_sub_gt_zero_eq,
    native_zleq_eq_not_gt]

theorem native_to_real_sub_geq_zero_eq
    (n1 n2 : Int) :
  native_qleq (native_mk_rational 0 1)
      (native_qplus (native_to_real n1) (native_qneg (native_to_real n2))) =
    native_zleq n2 n1 := by
  rw [native_qgeq_zero_eq_not_lt,
    native_to_real_sub_lt_zero_eq,
    native_zleq_eq_not_gt]

theorem native_qsub_lt_zero_eq
    (q1 q2 : native_Rat) :
  native_qlt (native_qplus q1 (native_qneg q2)) (native_mk_rational 0 1) =
    native_qlt q1 q2 := by
  unfold native_qlt native_qplus native_qneg
  rw [show native_mk_rational 0 1 = (0 : Rat) by
    unfold native_mk_rational
    exact rat_zero_div_one]
  grind

theorem native_qsub_gt_zero_eq
    (q1 q2 : native_Rat) :
  native_qlt (native_mk_rational 0 1) (native_qplus q1 (native_qneg q2)) =
    native_qlt q2 q1 := by
  unfold native_qlt native_qplus native_qneg
  rw [show native_mk_rational 0 1 = (0 : Rat) by
    unfold native_mk_rational
    exact rat_zero_div_one]
  grind

theorem native_qsub_leq_zero_eq
    (q1 q2 : native_Rat) :
  native_qleq (native_qplus q1 (native_qneg q2)) (native_mk_rational 0 1) =
    native_qleq q1 q2 := by
  rw [native_qleq_zero_eq_not_gt, native_qsub_gt_zero_eq]
  unfold native_qleq native_qlt
  grind

theorem native_qsub_geq_zero_eq
    (q1 q2 : native_Rat) :
  native_qleq (native_mk_rational 0 1) (native_qplus q1 (native_qneg q2)) =
    native_qleq q2 q1 := by
  rw [native_qgeq_zero_eq_not_lt, native_qsub_lt_zero_eq]
  unfold native_qleq native_qlt
  grind

theorem native_qsub_eq_zero_eq
    (q1 q2 : native_Rat) :
  native_qeq (native_qplus q1 (native_qneg q2)) (native_mk_rational 0 1) =
    native_qeq q1 q2 := by
  unfold native_qeq native_qplus native_qneg
  rw [show native_mk_rational 0 1 = (0 : Rat) by
    unfold native_mk_rational
    exact rat_zero_div_one]
  grind

theorem mult_term_arith_type_of_non_none
    (x y : Term) :
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) ≠
      SmtType.None ->
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) =
      SmtType.Int ∨
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) =
      SmtType.Real := by
  intro hNN
  have ht : term_has_non_none_type (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← eo_to_smt_mult_eq x y]
    exact hNN
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt x) (__eo_to_smt y)) ht with hArgs | hArgs
  · left
    rw [eo_to_smt_mult_eq, typeof_mult_eq]
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
  · right
    rw [eo_to_smt_mult_eq, typeof_mult_eq]
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]

theorem diff_arith_type_of_scaled_factor
    (cx x one x1 x2 : Term) :
  (__smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one))) =
      SmtType.Int ∨
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one))) =
      SmtType.Real) ->
  (x = Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2 ∨
    x = Term.Apply (Term.UOp UserOp.to_real)
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2)) ->
  __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2)) =
      SmtType.Int ∨
    __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2)) =
      SmtType.Real := by
  intro hOuterTy hX
  let inner := Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one
  have hOuterNN : term_has_non_none_type (SmtTerm.mult (__eo_to_smt cx) (__eo_to_smt inner)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner)) =
          SmtType.None := by
      rw [eo_to_smt_mult_eq]
      exact hNone
    rcases hOuterTy with hOuterTy | hOuterTy
    · cases hOuterTy.symm.trans hNone'
    · cases hOuterTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt cx) (__eo_to_smt inner)) hOuterNN with hOuterArgs |
      hOuterArgs
  · have hInnerTy :
        __smtx_typeof (__eo_to_smt inner) = SmtType.Int := hOuterArgs.2
    have hInnerNN : term_has_non_none_type (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt one)) := by
      have hInnerTy' :
          __smtx_typeof (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt one)) =
            SmtType.Int := by
        simpa [inner, eo_to_smt_mult_eq] using hInnerTy
      unfold term_has_non_none_type
      intro hNone
      rw [hInnerTy'] at hNone
      cases hNone
    rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
        (typeof_mult_eq (__eo_to_smt x) (__eo_to_smt one)) hInnerNN with hArgs | hArgs
    · rcases hX with hX | hX
      · subst x
        exact Or.inl hArgs.1
      · subst x
        have ht : term_has_non_none_type
            (SmtTerm.to_real
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))) := by
          unfold term_has_non_none_type
          rw [← eo_to_smt_to_real_eq]
          intro hNone
          rw [hNone] at hArgs
          cases hArgs.1
        exact Or.inl (to_real_arg_of_non_none
          (t := __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2)) ht)
    · have hInnerTyReal :
          __smtx_typeof (__eo_to_smt inner) = SmtType.Real := by
        rw [show __eo_to_smt inner = SmtTerm.mult (__eo_to_smt x) (__eo_to_smt one) by
          simp [inner, eo_to_smt_mult_eq]]
        rw [typeof_mult_eq]
        simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
      rw [hInnerTy] at hInnerTyReal
      cases hInnerTyReal
  · have hInnerTy :
        __smtx_typeof (__eo_to_smt inner) = SmtType.Real := hOuterArgs.2
    have hInnerNN : term_has_non_none_type (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt one)) := by
      have hInnerTy' :
          __smtx_typeof (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt one)) =
            SmtType.Real := by
        simpa [inner, eo_to_smt_mult_eq] using hInnerTy
      unfold term_has_non_none_type
      intro hNone
      rw [hInnerTy'] at hNone
      cases hNone
    rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
        (typeof_mult_eq (__eo_to_smt x) (__eo_to_smt one)) hInnerNN with hArgs | hArgs
    · have hInnerTyInt :
          __smtx_typeof (__eo_to_smt inner) = SmtType.Int := by
        rw [show __eo_to_smt inner = SmtTerm.mult (__eo_to_smt x) (__eo_to_smt one) by
          simp [inner, eo_to_smt_mult_eq]]
        rw [typeof_mult_eq]
        simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
      rw [hInnerTy] at hInnerTyInt
      cases hInnerTyInt
    · rcases hX with hX | hX
      · subst x
        exact Or.inr hArgs.1
      · subst x
        have ht : term_has_non_none_type
            (SmtTerm.to_real
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))) := by
          unfold term_has_non_none_type
          rw [← eo_to_smt_to_real_eq]
          intro hNone
          rw [hNone] at hArgs
          cases hArgs.1
        exact Or.inl (to_real_arg_of_non_none
          (t := __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2)) ht)

/-- Sharpens `diff_arith_type_of_scaled_factor` for the `to_real` shape: since
    `to_real` only accepts `Int`, the differenced argument must be `Int`. -/
theorem diff_int_type_of_scaled_factor_to_real
    (cx one x1 x2 : Term) :
  (__smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult)
                (Term.Apply (Term.UOp UserOp.to_real)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))) one))) =
      SmtType.Int ∨
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult)
                (Term.Apply (Term.UOp UserOp.to_real)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))) one))) =
      SmtType.Real) ->
  __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2)) =
      SmtType.Int := by
  intro hOuterTy
  rcases diff_arith_type_of_scaled_factor cx
      (Term.Apply (Term.UOp UserOp.to_real)
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))
      one x1 x2 hOuterTy (Or.inr rfl) with hInt | hReal
  · exact hInt
  · exfalso
    have hToRealNone :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp.to_real)
                (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))) =
          SmtType.None := by
      rw [eo_to_smt_to_real_eq, typeof_to_real_eq]
      simp [native_ite, native_Teq, hReal]
    have hInnerNone :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult)
                  (Term.Apply (Term.UOp UserOp.to_real)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))) one)) =
          SmtType.None := by
      rw [eo_to_smt_mult_eq, typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hToRealNone]
    have hOuterNone :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
                (Term.Apply (Term.Apply (Term.UOp UserOp.mult)
                    (Term.Apply (Term.UOp UserOp.to_real)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))) one))) =
          SmtType.None := by
      rw [eo_to_smt_mult_eq, typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hInnerNone]
    rcases hOuterTy with h | h <;> · rw [hOuterNone] at h; cases h

theorem arith_rel_eval_bools_of_diff_type
    (M : SmtModel) (hM : model_wf M) (x1 x2 : Term)
    (hDiffTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2)) =
          SmtType.Int ∨
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2)) =
          SmtType.Real) :
  ∃ q : native_Rat,
    arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2) =
      SmtValue.Rational q ∧
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x1) x2)) =
      SmtValue.Boolean (native_qlt q (native_mk_rational 0 1)) ∧
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x1) x2)) =
      SmtValue.Boolean (native_qleq q (native_mk_rational 0 1)) ∧
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) x2)) =
      SmtValue.Boolean (native_qeq q (native_mk_rational 0 1)) ∧
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x1) x2)) =
      SmtValue.Boolean (native_qlt (native_mk_rational 0 1) q) ∧
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x1) x2)) =
      SmtValue.Boolean (native_qleq (native_mk_rational 0 1) q) := by
  let diff := Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2
  have hNN : term_has_non_none_type (SmtTerm.neg (__eo_to_smt x1) (__eo_to_smt x2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' : __smtx_typeof (__eo_to_smt diff) = SmtType.None := by
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt x1) (__eo_to_smt x2) by rfl]
      exact hNone
    rcases hDiffTy with hDiffTy | hDiffTy
    · cases hDiffTy.symm.trans hNone'
    · cases hDiffTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq (__eo_to_smt x1) (__eo_to_smt x2)) hNN with hArgs | hArgs
  · have hDiffTyInt :
        __smtx_typeof (__eo_to_smt diff) = SmtType.Int := by
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt x1) (__eo_to_smt x2) by rfl]
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
    have _hDiffTyInt' :
        __smtx_typeof (__eo_to_smt diff) = SmtType.Int := by
      rcases hDiffTy with hDiffTy | hDiffTy
      · exact hDiffTy
      · rw [hDiffTyInt] at hDiffTy
        cases hDiffTy
    rcases smt_eval_int_of_type M hM x1 hArgs.1 with ⟨n1, hEval1⟩
    rcases smt_eval_int_of_type M hM x2 hArgs.2 with ⟨n2, hEval2⟩
    let q := native_qplus (native_to_real n1) (native_qneg (native_to_real n2))
    refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold arith_atom_denote_real
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt x1) (__eo_to_smt x2) by rfl]
      rw [__smtx_model_eval.eq_15, hEval1, hEval2]
      simp [__smtx_to_real_coerce, __smtx_model_eval__, q, native_to_real_sub]
    · rw [eo_to_smt_lt_eq, __smtx_model_eval.eq_17, hEval1, hEval2]
      simp [__smtx_model_eval_lt, q, native_to_real_sub_lt_zero_eq]
    · rw [eo_to_smt_leq_eq, __smtx_model_eval.eq_18, hEval1, hEval2]
      simp [__smtx_model_eval_leq, q, native_to_real_sub_leq_zero_eq]
    · rw [eo_to_smt_eq_eq, smtx_eval_eq_term_eq, hEval1, hEval2]
      simp [__smtx_model_eval_eq, native_veq, native_zeq, q, native_to_real_sub_eq_zero_eq]
    · rw [eo_to_smt_gt_eq, __smtx_model_eval.eq_19, hEval1, hEval2]
      simp [__smtx_model_eval_gt, __smtx_model_eval_lt, q, native_to_real_sub_gt_zero_eq]
    · rw [eo_to_smt_geq_eq, __smtx_model_eval.eq_20, hEval1, hEval2]
      simp [__smtx_model_eval_geq, __smtx_model_eval_leq, q, native_to_real_sub_geq_zero_eq]
  · have hDiffTyReal :
        __smtx_typeof (__eo_to_smt diff) = SmtType.Real := by
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt x1) (__eo_to_smt x2) by rfl]
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
    have _hDiffTyReal' :
        __smtx_typeof (__eo_to_smt diff) = SmtType.Real := by
      rcases hDiffTy with hDiffTy | hDiffTy
      · rw [hDiffTyReal] at hDiffTy
        cases hDiffTy
      · exact hDiffTy
    rcases smt_eval_real_of_type M hM x1 hArgs.1 with ⟨q1, hEval1⟩
    rcases smt_eval_real_of_type M hM x2 hArgs.2 with ⟨q2, hEval2⟩
    let q := native_qplus q1 (native_qneg q2)
    refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold arith_atom_denote_real
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt x1) (__eo_to_smt x2) by rfl]
      rw [__smtx_model_eval.eq_15, hEval1, hEval2]
      simp [__smtx_to_real_coerce, __smtx_model_eval__, q]
    · rw [eo_to_smt_lt_eq, __smtx_model_eval.eq_17, hEval1, hEval2]
      simp [__smtx_model_eval_lt, q, native_qsub_lt_zero_eq]
    · rw [eo_to_smt_leq_eq, __smtx_model_eval.eq_18, hEval1, hEval2]
      simp [__smtx_model_eval_leq, q, native_qsub_leq_zero_eq]
    · rw [eo_to_smt_eq_eq, smtx_eval_eq_term_eq, hEval1, hEval2]
      simp only [__smtx_model_eval_eq, native_veq]
      rw [show decide (SmtValue.Rational q1 = SmtValue.Rational q2) = native_qeq q1 q2 by
        simp [native_qeq]]
      change SmtValue.Boolean (native_qeq q1 q2) =
        SmtValue.Boolean (native_qeq q (native_mk_rational 0 1))
      rw [show native_qeq q (native_mk_rational 0 1) = native_qeq q1 q2 by
        dsimp [q]
        rw [native_qsub_eq_zero_eq]]
    · rw [eo_to_smt_gt_eq, __smtx_model_eval.eq_19, hEval1, hEval2]
      simp [__smtx_model_eval_gt, __smtx_model_eval_lt, q, native_qsub_gt_zero_eq]
    · rw [eo_to_smt_geq_eq, __smtx_model_eval.eq_20, hEval1, hEval2]
      simp [__smtx_model_eval_geq, __smtx_model_eval_leq, q, native_qsub_geq_zero_eq]

theorem arith_atom_denote_real_of_scaled_factor
    (M : SmtModel) (hM : model_wf M)
    (cx x one : Term) (c q : native_Rat)
    (hOuterTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one))) =
          SmtType.Int ∨
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one))) =
          SmtType.Real)
    (hCx : arith_atom_denote_real M cx = SmtValue.Rational c)
    (hX : arith_atom_denote_real M x = SmtValue.Rational q)
    (hOne : arith_atom_denote_real M one = SmtValue.Rational (native_mk_rational 1 1)) :
  arith_atom_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)) =
    SmtValue.Rational (native_qmult c q) := by
  let inner := Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one
  have hOuterNN : term_has_non_none_type (SmtTerm.mult (__eo_to_smt cx) (__eo_to_smt inner)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner)) =
        SmtType.None := by
      rw [eo_to_smt_mult_eq]
      exact hNone
    rcases hOuterTy with hOuterTy | hOuterTy
    · cases hOuterTy.symm.trans hNone'
    · cases hOuterTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt cx) (__eo_to_smt inner)) hOuterNN with hOuterArgs |
      hOuterArgs
  · have hInnerTy :
        __smtx_typeof (__eo_to_smt inner) = SmtType.Int := hOuterArgs.2
    have hInnerArith :
        __smtx_typeof (__eo_to_smt inner) = SmtType.Int ∨
          __smtx_typeof (__eo_to_smt inner) = SmtType.Real := Or.inl hInnerTy
    have hOuterArith :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner)) =
            SmtType.Int ∨
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner)) =
            SmtType.Real := by
      have hOuterTyInt :
          __smtx_typeof
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner)) =
            SmtType.Int := by
        rw [eo_to_smt_mult_eq, typeof_mult_eq]
        simp [__smtx_typeof_arith_overload_op_2, hOuterArgs.1, hOuterArgs.2]
      exact Or.inl hOuterTyInt
    change arith_atom_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner) =
      SmtValue.Rational (native_qmult c q)
    rw [arith_atom_denote_real_of_mult M hM cx inner hOuterArith]
    rw [arith_atom_denote_real_of_mult M hM x one hInnerArith]
    simp [hCx, hX, hOne, __smtx_model_eval_mult, native_qmult,
      native_mk_rational_one, Rat.mul_one]
  · have hInnerTy :
        __smtx_typeof (__eo_to_smt inner) = SmtType.Real := hOuterArgs.2
    have hInnerArith :
        __smtx_typeof (__eo_to_smt inner) = SmtType.Int ∨
          __smtx_typeof (__eo_to_smt inner) = SmtType.Real := Or.inr hInnerTy
    have hOuterArith :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner)) =
            SmtType.Int ∨
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner)) =
            SmtType.Real := by
      have hOuterTyReal :
          __smtx_typeof
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner)) =
            SmtType.Real := by
        rw [eo_to_smt_mult_eq, typeof_mult_eq]
        simp [__smtx_typeof_arith_overload_op_2, hOuterArgs.1, hOuterArgs.2]
      exact Or.inr hOuterTyReal
    change arith_atom_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx) inner) =
      SmtValue.Rational (native_qmult c q)
    rw [arith_atom_denote_real_of_mult M hM cx inner hOuterArith]
    rw [arith_atom_denote_real_of_mult M hM x one hInnerArith]
    simp [hCx, hX, hOne, __smtx_model_eval_mult, native_qmult,
      native_mk_rational_one, Rat.mul_one]

theorem arith_rel_smt_value_rel_of_scaled
    (M : SmtModel)
    (r cx cy x1 x2 y1 y2 : Term) (c d qx qy : native_Rat)
    (hCx : __eo_to_q cx = Term.Rational c)
    (hCy : __eo_to_q cy = Term.Rational d)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hConstsRel :
      __is_poly_norm_rel_consts_rel (Term.Apply (Term.Apply r cx) cy) =
        Term.Boolean true)
    (hScaled : native_qmult c qx = native_qmult d qy)
    (hLtX :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x1) x2)) =
        SmtValue.Boolean (native_qlt qx (native_mk_rational 0 1)))
    (hLeX :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x1) x2)) =
        SmtValue.Boolean (native_qleq qx (native_mk_rational 0 1)))
    (hEqX :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) x2)) =
        SmtValue.Boolean (native_qeq qx (native_mk_rational 0 1)))
    (hGtX :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x1) x2)) =
        SmtValue.Boolean (native_qlt (native_mk_rational 0 1) qx))
    (hGeX :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x1) x2)) =
        SmtValue.Boolean (native_qleq (native_mk_rational 0 1) qx))
    (hLtY :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) y1) y2)) =
        SmtValue.Boolean (native_qlt qy (native_mk_rational 0 1)))
    (hLeY :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) y1) y2)) =
        SmtValue.Boolean (native_qleq qy (native_mk_rational 0 1)))
    (hEqY :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y1) y2)) =
        SmtValue.Boolean (native_qeq qy (native_mk_rational 0 1)))
    (hGtY :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) y1) y2)) =
        SmtValue.Boolean (native_qlt (native_mk_rational 0 1) qy))
    (hGeY :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) y1) y2)) =
        SmtValue.Boolean (native_qleq (native_mk_rational 0 1) qy)) :
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply r x1) x2)))
    (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply r y1) y2))) := by
  have hScaled' : c * qx = d * qy := by
    simpa [native_qmult] using hScaled
  have hZeroIff : qx = 0 ↔ qy = 0 := by
    constructor
    · intro hx0
      have hdy : d * qy = 0 := by
        rw [← hScaled', hx0, Rat.mul_zero]
      exact (rat_scaled_zero_iff hd0).mp hdy
    · intro hy0
      have hcx : c * qx = 0 := by
        rw [hScaled', hy0, Rat.mul_zero]
      exact (rat_scaled_zero_iff hc0).mp hcx
  cases r
  case UOp op =>
    cases op
    case eq =>
      have hBool :
          native_qeq qx (native_mk_rational 0 1) =
            native_qeq qy (native_mk_rational 0 1) := by
        simpa [native_mk_rational_zero] using native_qeq_zero_eq_of_iff hZeroIff
      rw [hEqX, hEqY, hBool]
      exact RuleProofs.smt_value_rel_refl _
    case lt =>
      have hSameSign :=
        same_sign_of_is_poly_norm_rel_consts_rel_true_lt
          hConstsRel hCx hCy hc0 hd0
      have hSigns :
          (qx < 0 ↔ qy < 0) ∧ (0 < qx ↔ 0 < qy) ∧ (qx = 0 ↔ qy = 0) := by
        rcases hSameSign with hPos | hNeg
        · exact rat_same_sign_core_pos hScaled' hPos.1 hPos.2
        · exact rat_same_sign_core_neg hScaled' hNeg.1 hNeg.2
      have hBool :
          native_qlt qx (native_mk_rational 0 1) =
            native_qlt qy (native_mk_rational 0 1) := by
        simpa [native_mk_rational_zero] using native_qlt_zero_eq_of_iff hSigns.1
      rw [hLtX, hLtY, hBool]
      exact RuleProofs.smt_value_rel_refl _
    case leq =>
      have hSameSign :=
        same_sign_of_is_poly_norm_rel_consts_rel_true_leq
          hConstsRel hCx hCy hc0 hd0
      have hSigns :
          (qx < 0 ↔ qy < 0) ∧ (0 < qx ↔ 0 < qy) ∧ (qx = 0 ↔ qy = 0) := by
        rcases hSameSign with hPos | hNeg
        · exact rat_same_sign_core_pos hScaled' hPos.1 hPos.2
        · exact rat_same_sign_core_neg hScaled' hNeg.1 hNeg.2
      have hBool :
          native_qleq qx (native_mk_rational 0 1) =
            native_qleq qy (native_mk_rational 0 1) := by
        simpa [native_mk_rational_zero] using
          native_qleq_zero_eq_of_sign hSigns.1 hSigns.2.2
      rw [hLeX, hLeY, hBool]
      exact RuleProofs.smt_value_rel_refl _
    case gt =>
      have hSameSign :=
        same_sign_of_is_poly_norm_rel_consts_rel_true_gt
          hConstsRel hCx hCy hc0 hd0
      have hSigns :
          (qx < 0 ↔ qy < 0) ∧ (0 < qx ↔ 0 < qy) ∧ (qx = 0 ↔ qy = 0) := by
        rcases hSameSign with hPos | hNeg
        · exact rat_same_sign_core_pos hScaled' hPos.1 hPos.2
        · exact rat_same_sign_core_neg hScaled' hNeg.1 hNeg.2
      have hBool :
          native_qlt (native_mk_rational 0 1) qx =
            native_qlt (native_mk_rational 0 1) qy := by
        simpa [native_mk_rational_zero] using native_qgt_zero_eq_of_iff hSigns.2.1
      rw [hGtX, hGtY, hBool]
      exact RuleProofs.smt_value_rel_refl _
    case geq =>
      have hSameSign :=
        same_sign_of_is_poly_norm_rel_consts_rel_true_geq
          hConstsRel hCx hCy hc0 hd0
      have hSigns :
          (qx < 0 ↔ qy < 0) ∧ (0 < qx ↔ 0 < qy) ∧ (qx = 0 ↔ qy = 0) := by
        rcases hSameSign with hPos | hNeg
        · exact rat_same_sign_core_pos hScaled' hPos.1 hPos.2
        · exact rat_same_sign_core_neg hScaled' hNeg.1 hNeg.2
      have hBool :
          native_qleq (native_mk_rational 0 1) qx =
            native_qleq (native_mk_rational 0 1) qy := by
        simpa [native_mk_rational_zero] using
          native_qgeq_zero_eq_of_sign hSigns.2.1 hSigns.2.2
      rw [hGeX, hGeY, hBool]
      exact RuleProofs.smt_value_rel_refl _
    all_goals
      exfalso
      simp [__is_poly_norm_rel_consts_rel] at hConstsRel
  all_goals
    exfalso
    simp [__is_poly_norm_rel_consts_rel] at hConstsRel
