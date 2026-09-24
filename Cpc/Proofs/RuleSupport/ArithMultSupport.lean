module

public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.ArithValueSupport
import all Cpc.Proofs.RuleSupport.ArithValueSupport
public import Cpc.Proofs.RuleSupport.ArithFactorSupport
import all Cpc.Proofs.RuleSupport.ArithFactorSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace ArithMultSupport

open ArithValueSupport
open ArithFactorSupport

abbrev arithZero (m : Term) : Term :=
  __arith_mk_zero (__eo_typeof m)

abbrev arithOne (m : Term) : Term :=
  __eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)

abbrev scale (m x : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.mult) m)
    (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) (arithOne m))

abbrev relTerm (r x y : Term) : Term :=
  Term.Apply (Term.Apply r x) y

/-- Arithmetic relations supported by the multiplication-by-a-sign rules. -/
def arithRelOp : Term -> Prop
  | Term.UOp UserOp.eq => True
  | Term.UOp UserOp.lt => True
  | Term.UOp UserOp.leq => True
  | Term.UOp UserOp.gt => True
  | Term.UOp UserOp.geq => True
  | _ => False

abbrev posAntecedent (m F : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m)))
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (Term.Boolean true))

abbrev negAntecedent (m F : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m)))
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (Term.Boolean true))

abbrev posConclusion (r m a b : Term) : Term :=
  relTerm r (scale m a) (scale m b)

abbrev negConclusion (r m a b : Term) : Term :=
  __arith_rel_inv r (scale m a) (scale m b)

private theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem eo_mk_apply_fun_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  intro hf
  subst f
  simp [__eo_mk_apply] at h

private theorem eo_mk_apply_arg_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem scale_mk_eq_of_ne_stuck (m x : Term)
    (h :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) x) (arithOne m)) ≠
        Term.Stuck) :
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) x) (arithOne m)) =
      scale m x := by
  have hInner :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) x) (arithOne m) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hInner]

private theorem arith_rel_inv_left_ne_stuck_of_ne_stuck (r x y : Term)
    (h : __arith_rel_inv r x y ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases r <;> cases y <;> simp [__arith_rel_inv] at h

private theorem arith_rel_inv_right_ne_stuck_of_ne_stuck (r x y : Term)
    (h : __arith_rel_inv r x y ≠ Term.Stuck) :
    y ≠ Term.Stuck := by
  intro hy
  subst y
  cases r <;> cases x <;> simp [__arith_rel_inv] at h

private theorem mk_arith_mult_pos_unfold_of_rel
    (m r a b : Term)
    (hRel : arithRelOp r)
    (hM : m ≠ Term.Stuck) :
    __mk_arith_mult_pos m (Term.Apply (Term.Apply r a) b) =
      __eo_mk_apply (__eo_mk_apply r
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a) (arithOne m))))
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b) (arithOne m))) := by
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    all_goals
      simp [__mk_arith_mult_pos, arithOne]

private theorem mk_arith_mult_pos_eq_of_ne_stuck
    (m r a b : Term)
    (hRel : arithRelOp r)
    (h :
      __mk_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck) :
    __mk_arith_mult_pos m (Term.Apply (Term.Apply r a) b) =
      posConclusion r m a b := by
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__mk_arith_mult_pos] at h
  let one := arithOne m
  let lhsMk :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a) one)
  let rhsMk :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b) one)
  have hUnfold := mk_arith_mult_pos_unfold_of_rel m r a b hRel hM
  change __mk_arith_mult_pos m (Term.Apply (Term.Apply r a) b) =
    __eo_mk_apply (__eo_mk_apply r lhsMk) rhsMk at hUnfold
  rw [hUnfold] at h ⊢
  have hFun :
      __eo_mk_apply r lhsMk ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
  have hLhs : lhsMk ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFun
  have hRhs : rhsMk ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hFun]
  change Term.Apply (Term.Apply r lhsMk) rhsMk =
    Term.Apply (Term.Apply r (scale m a)) (scale m b)
  rw [show lhsMk = scale m a by
    simpa [lhsMk, one, arithOne] using scale_mk_eq_of_ne_stuck m a hLhs]
  rw [show rhsMk = scale m b by
    simpa [rhsMk, one, arithOne] using scale_mk_eq_of_ne_stuck m b hRhs]

private theorem mk_arith_mult_neg_eq_of_ne_stuck
    (m r a b : Term)
    (h :
      __mk_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck) :
    __mk_arith_mult_neg m (Term.Apply (Term.Apply r a) b) =
      negConclusion r m a b := by
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__mk_arith_mult_neg] at h
  simp [__mk_arith_mult_neg, negConclusion] at h ⊢
  let one := arithOne m
  let lhsMk :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a) one)
  let rhsMk :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b) one)
  have hLhs : lhsMk ≠ Term.Stuck := by
    simpa [lhsMk, one, arithOne] using
      arith_rel_inv_left_ne_stuck_of_ne_stuck r
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a)
            (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)))
        )
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b)
            (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)))
        )
        h
  have hRhs : rhsMk ≠ Term.Stuck := by
    simpa [rhsMk, one, arithOne] using
      arith_rel_inv_right_ne_stuck_of_ne_stuck r
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a)
            (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)))
        )
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b)
            (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)))
        )
        h
  rw [show
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a)
          (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m))) =
        scale m a by
    simpa [arithOne] using scale_mk_eq_of_ne_stuck m a hLhs]
  rw [show
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b)
          (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m))) =
        scale m b by
    simpa [arithOne] using scale_mk_eq_of_ne_stuck m b hRhs]

private theorem prog_arith_mult_pos_eq_of_ne_stuck
    (m r a b : Term)
    (hRel : arithRelOp r)
    (h :
      __eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠
        Term.Stuck) :
    __eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b) =
      Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (posAntecedent m (Term.Apply (Term.Apply r a) b)))
        (posConclusion r m a b) := by
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__eo_prog_arith_mult_pos] at h
  simp [__eo_prog_arith_mult_pos] at h ⊢
  have hConcl :
      __mk_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  have hImp :
      __eo_mk_apply (Term.UOp UserOp.imp)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.and)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply r a) b)) (Term.Boolean true))) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
  have hAnte :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply r a) b)) (Term.Boolean true)) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hImp
  have hAnd :
      __eo_mk_apply (Term.UOp UserOp.and)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m)) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hAnte
  have hSign :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hAnd
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hImp]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hAnte]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hAnd]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSign]
  rw [mk_arith_mult_pos_eq_of_ne_stuck m r a b hRel hConcl]

private theorem prog_arith_mult_neg_eq_of_ne_stuck
    (m r a b : Term)
    (h :
      __eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠
        Term.Stuck) :
    __eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b) =
      Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (negAntecedent m (Term.Apply (Term.Apply r a) b)))
        (negConclusion r m a b) := by
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__eo_prog_arith_mult_neg] at h
  simp [__eo_prog_arith_mult_neg] at h ⊢
  have hConcl :
      __mk_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  have hImp :
      __eo_mk_apply (Term.UOp UserOp.imp)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.and)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply r a) b)) (Term.Boolean true))) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
  have hAnte :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply r a) b)) (Term.Boolean true)) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hImp
  have hAnd :
      __eo_mk_apply (Term.UOp UserOp.and)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m)) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hAnte
  have hSign :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hAnd
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hImp]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hAnte]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hAnd]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSign]
  rw [mk_arith_mult_neg_eq_of_ne_stuck m r a b hConcl]

theorem native_to_real_lt_eq (a b : native_Int) :
    native_qlt (native_to_real a) (native_to_real b) = native_zlt a b := by
  rw [← native_qsub_lt_zero_eq (native_to_real a) (native_to_real b)]
  exact native_to_real_sub_lt_zero_eq a b

theorem native_to_real_leq_eq (a b : native_Int) :
    native_qleq (native_to_real a) (native_to_real b) = native_zleq a b := by
  rw [← native_qsub_leq_zero_eq (native_to_real a) (native_to_real b)]
  exact native_to_real_sub_leq_zero_eq a b

theorem native_to_real_qeq_eq (a b : native_Int) :
    native_qeq (native_to_real a) (native_to_real b) = native_zeq a b := by
  rw [← native_qsub_eq_zero_eq (native_to_real a) (native_to_real b)]
  exact native_to_real_sub_eq_zero_eq a b

private theorem rat_mul_lt_of_pos_left {c a b : Rat}
    (hc : 0 < c) (hab : a < b) :
    c * a < c * b := by
  rw [Rat.lt_iff_sub_pos]
  have hdiff : 0 < b - a := (Rat.lt_iff_sub_pos a b).mp hab
  have hmul : 0 < c * (b - a) :=
    (Rat.mul_pos_iff_of_pos_left hc).mpr hdiff
  simpa [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.add_comm] using hmul

private theorem rat_mul_le_of_pos_left {c a b : Rat}
    (hc : 0 < c) (hab : a ≤ b) :
    c * a ≤ c * b := by
  rcases (Rat.le_iff_lt_or_eq.mp hab) with hlt | heq
  · exact Rat.le_iff_lt_or_eq.mpr (Or.inl (rat_mul_lt_of_pos_left hc hlt))
  · subst b
    exact Rat.le_iff_lt_or_eq.mpr (Or.inr rfl)

private theorem rat_mul_lt_of_neg_left {c a b : Rat}
    (hc : c < 0) (hab : a < b) :
    c * b < c * a := by
  have hpos : 0 < -c :=
    (Rat.lt_neg_iff (a := 0) (b := c)).mpr (by simpa using hc)
  have hltneg : (-c) * a < (-c) * b :=
    rat_mul_lt_of_pos_left hpos hab
  have h := Rat.neg_lt_neg hltneg
  simpa [Rat.neg_mul, Rat.neg_neg] using h

private theorem rat_mul_le_of_neg_left {c a b : Rat}
    (hc : c < 0) (hab : a ≤ b) :
    c * b ≤ c * a := by
  have hpos : 0 < -c :=
    (Rat.lt_neg_iff (a := 0) (b := c)).mpr (by simpa using hc)
  have hleNeg : (-c) * a ≤ (-c) * b :=
    rat_mul_le_of_pos_left hpos hab
  have h := Rat.neg_le_neg hleNeg
  simpa [Rat.neg_mul, Rat.neg_neg] using h

theorem native_qlt_mul_of_pos_left {c a b : native_Rat} :
    native_qlt (native_mk_rational 0 1) c = true ->
    native_qlt a b = true ->
    native_qlt (native_qmult c a) (native_qmult c b) = true := by
  intro hc hab
  have hc' : (0 : Rat) < c := by
    simpa [native_qlt, native_mk_rational_zero] using hc
  have hab' : a < b := by
    simpa [native_qlt] using hab
  have hres : c * a < c * b := rat_mul_lt_of_pos_left hc' hab'
  -- v4.33 `simp` rewrites inside `decide` without refreshing the instance,
  -- so the goal keeps its `decide _ = true` shape; supply it directly.
  simp only [native_qlt, native_qmult]
  exact decide_eq_true hres

theorem native_qleq_mul_of_pos_left {c a b : native_Rat} :
    native_qlt (native_mk_rational 0 1) c = true ->
    native_qleq a b = true ->
    native_qleq (native_qmult c a) (native_qmult c b) = true := by
  intro hc hab
  have hc' : (0 : Rat) < c := by
    simpa [native_qlt, native_mk_rational_zero] using hc
  have hab' : a ≤ b := by
    simpa [native_qleq] using hab
  have hres : c * a ≤ c * b := rat_mul_le_of_pos_left hc' hab'
  -- v4.33 `simp` rewrites inside `decide` without refreshing the instance,
  -- so the goal keeps its `decide _ = true` shape; supply it directly.
  simp only [native_qleq, native_qmult]
  exact decide_eq_true hres

theorem native_qlt_mul_of_neg_left {c a b : native_Rat} :
    native_qlt c (native_mk_rational 0 1) = true ->
    native_qlt a b = true ->
    native_qlt (native_qmult c b) (native_qmult c a) = true := by
  intro hc hab
  have hc' : c < (0 : Rat) := by
    simpa [native_qlt, native_mk_rational_zero] using hc
  have hab' : a < b := by
    simpa [native_qlt] using hab
  have hres : c * b < c * a := rat_mul_lt_of_neg_left hc' hab'
  -- v4.33 `simp` rewrites inside `decide` without refreshing the instance,
  -- so the goal keeps its `decide _ = true` shape; supply it directly.
  simp only [native_qlt, native_qmult]
  exact decide_eq_true hres

theorem native_qleq_mul_of_neg_left {c a b : native_Rat} :
    native_qlt c (native_mk_rational 0 1) = true ->
    native_qleq a b = true ->
    native_qleq (native_qmult c b) (native_qmult c a) = true := by
  intro hc hab
  have hc' : c < (0 : Rat) := by
    simpa [native_qlt, native_mk_rational_zero] using hc
  have hab' : a ≤ b := by
    simpa [native_qleq] using hab
  have hres : c * b ≤ c * a := rat_mul_le_of_neg_left hc' hab'
  -- v4.33 `simp` rewrites inside `decide` without refreshing the instance,
  -- so the goal keeps its `decide _ = true` shape; supply it directly.
  simp only [native_qleq, native_qmult]
  exact decide_eq_true hres

theorem native_qeq_mul_congr_left {c a b : native_Rat} :
    native_qeq a b = true ->
    native_qeq (native_qmult c a) (native_qmult c b) = true := by
  intro hab
  have hab' : a = b := by
    simpa [native_qeq] using hab
  subst b
  simp [native_qeq]

private theorem native_to_real_zero :
    native_to_real 0 = native_mk_rational 0 1 := by
  native_decide

private theorem native_to_real_one :
    native_to_real 1 = native_mk_rational 1 1 := by
  native_decide

theorem arith_rel_op_has_bool_type_of_translation
    (r a b : Term) :
    arithRelOp r ->
    RuleProofs.eo_has_smt_translation (relTerm r a b) ->
    RuleProofs.eo_has_bool_type (relTerm r a b) := by
  intro hRel hTrans
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    · rcases eq_operands_same_smt_type_of_eq_has_smt_translation a b
          (by simpa [relTerm] using hTrans) with ⟨hTy, hNN⟩
      simpa [relTerm] using
        RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b hTy hNN
    · unfold RuleProofs.eo_has_smt_translation at hTrans
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.lt) a b) =
          SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) by rfl]
      have hNN : term_has_non_none_type (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) := by
        unfold term_has_non_none_type
        simpa [relTerm, __eo_to_smt, __smtx_typeof] using hTrans
      rcases arith_binop_ret_bool_args_of_non_none
          (op := SmtTerm.lt) (typeof_lt_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
          with hArgs | hArgs
      · rw [typeof_lt_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
      · rw [typeof_lt_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    · unfold RuleProofs.eo_has_smt_translation at hTrans
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.leq) a b) =
          SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) by rfl]
      have hNN : term_has_non_none_type (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) := by
        unfold term_has_non_none_type
        simpa [relTerm, __eo_to_smt, __smtx_typeof] using hTrans
      rcases arith_binop_ret_bool_args_of_non_none
          (op := SmtTerm.leq) (typeof_leq_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
          with hArgs | hArgs
      · rw [typeof_leq_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
      · rw [typeof_leq_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    · unfold RuleProofs.eo_has_smt_translation at hTrans
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.gt) a b) =
          SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
      have hNN : term_has_non_none_type (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) := by
        unfold term_has_non_none_type
        simpa [relTerm, __eo_to_smt, __smtx_typeof] using hTrans
      rcases arith_binop_ret_bool_args_of_non_none
          (op := SmtTerm.gt) (typeof_gt_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
          with hArgs | hArgs
      · rw [typeof_gt_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
      · rw [typeof_gt_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    · unfold RuleProofs.eo_has_smt_translation at hTrans
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.geq) a b) =
          SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
      have hNN : term_has_non_none_type (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) := by
        unfold term_has_non_none_type
        simpa [relTerm, __eo_to_smt, __smtx_typeof] using hTrans
      rcases arith_binop_ret_bool_args_of_non_none
          (op := SmtTerm.geq) (typeof_geq_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
          with hArgs | hArgs
      · rw [typeof_geq_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
      · rw [typeof_geq_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]

theorem arith_rel_args_have_translation
    (r a b : Term) :
    arithRelOp r ->
    RuleProofs.eo_has_smt_translation (relTerm r a b) ->
    RuleProofs.eo_has_smt_translation a ∧
      RuleProofs.eo_has_smt_translation b := by
  intro hRel hTrans
  have hBool := arith_rel_op_has_bool_type_of_translation r a b hRel hTrans
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    · simpa [relTerm] using
        CnfSupport.eq_args_have_translation_of_translation a b (by simpa [relTerm] using hTrans)
    · rcases rel_operands_arith_type_of_lt_has_bool_type a b
          (by simpa [relTerm] using hBool) with hArgs | hArgs
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
    · rcases rel_operands_arith_type_of_leq_has_bool_type a b
          (by simpa [relTerm] using hBool) with hArgs | hArgs
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
    · rcases rel_operands_arith_type_of_gt_has_bool_type a b
          (by simpa [relTerm] using hBool) with hArgs | hArgs
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
    · rcases rel_operands_arith_type_of_geq_has_bool_type a b
          (by simpa [relTerm] using hBool) with hArgs | hArgs
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone

theorem arith_atom_denote_real_of_smt_arith_type
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) ->
    ∃ q : native_Rat, arith_atom_denote_real M t = SmtValue.Rational q := by
  intro hTy
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM t hTy with ⟨n, hEval⟩
    refine ⟨native_to_real n, ?_⟩
    unfold arith_atom_denote_real
    rw [hEval]
    simp [__smtx_to_real_coerce]
  · rcases smt_eval_real_of_type M hM t hTy with ⟨q, hEval⟩
    refine ⟨q, ?_⟩
    unfold arith_atom_denote_real
    rw [hEval]
    simp [__smtx_to_real_coerce]

private theorem smt_type_of_eo_arith
    (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    (__eo_typeof t = Term.UOp UserOp.Int ∨ __eo_typeof t = Term.UOp UserOp.Real) ->
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) := by
  intro hTrans hTy
  have hPres :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (__eo_typeof t) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (__eo_typeof t) (__eo_to_smt t) rfl hTrans rfl
  rcases hTy with hTy | hTy
  · left
    simpa [hTy] using hPres
  · right
    simpa [hTy] using hPres

private theorem smt_type_of_eo_int
    (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof t = Term.UOp UserOp.Int ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  intro hTrans hTy
  have hPres :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (__eo_typeof t) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (__eo_typeof t) (__eo_to_smt t) rfl hTrans rfl
  simpa [hTy] using hPres

private theorem smt_type_of_eo_real
    (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof t = Term.UOp UserOp.Real ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
  intro hTrans hTy
  have hPres :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (__eo_typeof t) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (__eo_typeof t) (__eo_to_smt t) rfl hTrans rfl
  simpa [hTy] using hPres

private theorem arith_one_denote
    (M : SmtModel) (m : Term) :
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    arith_atom_denote_real M (arithOne m) =
      SmtValue.Rational (native_mk_rational 1 1) := by
  intro hTy
  rcases hTy with hTy | hTy
  · have hToQ :
        __eo_to_q (arithOne m) = Term.Rational (native_mk_rational 1 1) := by
      simp [arithOne, __eo_nil, __eo_nil_mult, __arith_mk_one, hTy,
        __eo_to_q, native_to_real_one]
    exact arith_atom_denote_real_of_to_q M (arithOne m)
      (native_mk_rational 1 1) hToQ
  · have hToQ :
        __eo_to_q (arithOne m) = Term.Rational (native_mk_rational 1 1) := by
      simp [arithOne, __eo_nil, __eo_nil_mult, __arith_mk_one, hTy, __eo_to_q]
    exact arith_atom_denote_real_of_to_q M (arithOne m)
      (native_mk_rational 1 1) hToQ

private theorem arith_zero_denote
    (M : SmtModel) (m : Term) :
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    arith_atom_denote_real M (arithZero m) =
      SmtValue.Rational (native_mk_rational 0 1) := by
  intro hTy
  rcases hTy with hTy | hTy
  · have hToQ :
        __eo_to_q (arithZero m) = Term.Rational (native_mk_rational 0 1) := by
      simp [arithZero, __arith_mk_zero, hTy, __eo_to_q, native_to_real_zero]
    exact arith_atom_denote_real_of_to_q M (arithZero m)
      (native_mk_rational 0 1) hToQ
  · have hToQ :
        __eo_to_q (arithZero m) = Term.Rational (native_mk_rational 0 1) := by
      simp [arithZero, __arith_mk_zero, hTy, __eo_to_q]
    exact arith_atom_denote_real_of_to_q M (arithZero m)
      (native_mk_rational 0 1) hToQ

private theorem typeof_plus_int_int :
    __eo_typeof_plus (Term.UOp UserOp.Int) (Term.UOp UserOp.Int) =
      Term.UOp UserOp.Int := by
  simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type, native_teq,
    native_ite, native_not, SmtEval.native_not]

private theorem typeof_plus_real_real :
    __eo_typeof_plus (Term.UOp UserOp.Real) (Term.UOp UserOp.Real) =
      Term.UOp UserOp.Real := by
  simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type, native_teq,
    native_ite, native_not, SmtEval.native_not]

private theorem typeof_plus_arg_int_of_nonstuck (T : Term) :
    __eo_typeof_plus T (Term.UOp UserOp.Int) ≠ Term.Stuck ->
    T = Term.UOp UserOp.Int := by
  intro h
  cases T <;> simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
    native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

private theorem typeof_plus_arg_real_of_nonstuck (T : Term) :
    __eo_typeof_plus T (Term.UOp UserOp.Real) ≠ Term.Stuck ->
    T = Term.UOp UserOp.Real := by
  intro h
  cases T <;> simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
    native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

private theorem typeof_plus_left_arith_of_nonstuck (T U : Term) :
    __eo_typeof_plus T U ≠ Term.Stuck ->
    T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real := by
  intro h
  cases T <;> cases U <;>
    simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
      native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢
  case UOp.UOp opT opU =>
    cases opT <;> cases opU <;>
      simp at h ⊢

private theorem scale_m_eo_arith_of_scale_not_stuck
    (m x : Term) :
    __eo_typeof (scale m x) ≠ Term.Stuck ->
    __eo_typeof m = Term.UOp UserOp.Int ∨
      __eo_typeof m = Term.UOp UserOp.Real := by
  intro hScale
  change __eo_typeof_plus (__eo_typeof m)
      (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) ≠
    Term.Stuck at hScale
  exact typeof_plus_left_arith_of_nonstuck (__eo_typeof m)
    (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) hScale

private theorem scale_arg_eo_type_of_scale_not_stuck
    (m x : Term) :
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof (scale m x) ≠ Term.Stuck ->
    __eo_typeof x = __eo_typeof m ∧
      __eo_typeof (scale m x) = __eo_typeof m := by
  intro hM hScale
  rcases hM with hM | hM
  · have hOneTy : __eo_typeof (arithOne m) = Term.UOp UserOp.Int := by
      change __eo_typeof (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)) =
        Term.UOp UserOp.Int
      rw [hM]
      rfl
    have hScale' :
        __eo_typeof_plus (Term.UOp UserOp.Int)
            (__eo_typeof_plus (__eo_typeof x) (Term.UOp UserOp.Int)) ≠
          Term.Stuck := by
      change __eo_typeof_plus (__eo_typeof m)
          (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) ≠
        Term.Stuck at hScale
      rw [hM, hOneTy] at hScale
      exact hScale
    have hInner :
        __eo_typeof_plus (__eo_typeof x) (Term.UOp UserOp.Int) ≠ Term.Stuck := by
      intro hInner
      exact hScale' (by rw [hInner]; rfl)
    have hxTy : __eo_typeof x = Term.UOp UserOp.Int :=
      typeof_plus_arg_int_of_nonstuck (__eo_typeof x) hInner
    constructor
    · rw [hxTy, hM]
    · rw [hM]
      change
        __eo_typeof_plus (__eo_typeof m)
          (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) =
        Term.UOp UserOp.Int
      rw [hM, hxTy, hOneTy, typeof_plus_int_int, typeof_plus_int_int]
  · have hOneTy : __eo_typeof (arithOne m) = Term.UOp UserOp.Real := by
      change __eo_typeof (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)) =
        Term.UOp UserOp.Real
      rw [hM]
      rfl
    have hScale' :
        __eo_typeof_plus (Term.UOp UserOp.Real)
            (__eo_typeof_plus (__eo_typeof x) (Term.UOp UserOp.Real)) ≠
          Term.Stuck := by
      change __eo_typeof_plus (__eo_typeof m)
          (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) ≠
        Term.Stuck at hScale
      rw [hM, hOneTy] at hScale
      exact hScale
    have hInner :
        __eo_typeof_plus (__eo_typeof x) (Term.UOp UserOp.Real) ≠ Term.Stuck := by
      intro hInner
      exact hScale' (by rw [hInner]; rfl)
    have hxTy : __eo_typeof x = Term.UOp UserOp.Real :=
      typeof_plus_arg_real_of_nonstuck (__eo_typeof x) hInner
    constructor
    · rw [hxTy, hM]
    · rw [hM]
      change
        __eo_typeof_plus (__eo_typeof m)
          (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) =
        Term.UOp UserOp.Real
      rw [hM, hxTy, hOneTy, typeof_plus_real_real, typeof_plus_real_real]

private theorem scale_smt_type_of_eo_type
    (m x : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation x ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof x = __eo_typeof m ->
    (__smtx_typeof (__eo_to_smt (scale m x)) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (scale m x)) = SmtType.Real) := by
  intro hmTrans hxTrans hM hxTy
  have hmSmt := smt_type_of_eo_arith m hmTrans hM
  have hxSmt : __smtx_typeof (__eo_to_smt x) =
      __smtx_typeof (__eo_to_smt m) := by
    have hmPres :
        __smtx_typeof (__eo_to_smt m) =
          __eo_to_smt_type (__eo_typeof m) :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        m (__eo_typeof m) (__eo_to_smt m) rfl hmTrans rfl
    have hxPres :
        __smtx_typeof (__eo_to_smt x) =
          __eo_to_smt_type (__eo_typeof x) :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        x (__eo_typeof x) (__eo_to_smt x) rfl hxTrans rfl
    rw [hxPres, hmPres, hxTy]
  rcases hM with hM | hM
  · have hmSmtInt : __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
      rcases hmSmt with hmSmt | hmSmt
      · exact hmSmt
      · simpa [hM] using
          (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
            m (__eo_typeof m) (__eo_to_smt m) rfl hmTrans rfl)
    left
    rw [show __eo_to_smt (scale m x) =
        SmtTerm.mult (__eo_to_smt m)
          (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt (arithOne m))) by rfl]
    rw [typeof_mult_eq]
    have hOne : __smtx_typeof (__eo_to_smt (arithOne m)) = SmtType.Int := by
      rw [show arithOne m = Term.Numeral 1 by
        simp [arithOne, __eo_nil, __eo_nil_mult, __arith_mk_one, hM]]
      rw [eo_to_smt_numeral_eq, __smtx_typeof.eq_2]
    have hxSmtInt : __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
      rw [hxSmt, hmSmtInt]
    have hInner :
        __smtx_typeof (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt (arithOne m))) =
          SmtType.Int := by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hxSmtInt, hOne]
    simp [__smtx_typeof_arith_overload_op_2, hmSmtInt, hInner]
  · have hmSmtReal : __smtx_typeof (__eo_to_smt m) = SmtType.Real := by
      rcases hmSmt with hmSmt | hmSmt
      · simpa [hM] using
          (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
            m (__eo_typeof m) (__eo_to_smt m) rfl hmTrans rfl)
      · exact hmSmt
    right
    rw [show __eo_to_smt (scale m x) =
        SmtTerm.mult (__eo_to_smt m)
          (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt (arithOne m))) by rfl]
    rw [typeof_mult_eq]
    have hOne : __smtx_typeof (__eo_to_smt (arithOne m)) = SmtType.Real := by
      rw [show arithOne m = Term.Rational (native_mk_rational 1 1) by
        simp [arithOne, __eo_nil, __eo_nil_mult, __arith_mk_one, hM]]
      rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3]
    have hxSmtReal : __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
      rw [hxSmt, hmSmtReal]
    have hInner :
        __smtx_typeof (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt (arithOne m))) =
          SmtType.Real := by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hxSmtReal, hOne]
    simp [__smtx_typeof_arith_overload_op_2, hmSmtReal, hInner]

private theorem scale_denote
    (M : SmtModel) (hM : model_wf M) (m x : Term)
    (qm qx : native_Rat) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation x ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof x = __eo_typeof m ->
    arith_atom_denote_real M m = SmtValue.Rational qm ->
    arith_atom_denote_real M x = SmtValue.Rational qx ->
    arith_atom_denote_real M (scale m x) =
      SmtValue.Rational (native_qmult qm qx) := by
  intro hmTrans hxTrans hMArith hxTy hmDen hxDen
  have hScaleTy :=
    scale_smt_type_of_eo_type m x hmTrans hxTrans hMArith hxTy
  exact arith_atom_denote_real_of_scaled_factor M hM m x (arithOne m) qm qx
    (by simpa [scale] using hScaleTy) hmDen hxDen (arith_one_denote M m hMArith)

private theorem scale_eo_type_of_eo_type
    (m x : Term) :
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof x = __eo_typeof m ->
    __eo_typeof (scale m x) = __eo_typeof m := by
  intro hM hxTy
  rcases hM with hM | hM
  · have hOneTy : __eo_typeof (arithOne m) = Term.UOp UserOp.Int := by
      change __eo_typeof (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)) =
        Term.UOp UserOp.Int
      rw [hM]
      rfl
    rw [hM]
    change
      __eo_typeof_plus (__eo_typeof m)
        (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) =
      Term.UOp UserOp.Int
    rw [hxTy, hM, hOneTy, typeof_plus_int_int, typeof_plus_int_int]
  · have hOneTy : __eo_typeof (arithOne m) = Term.UOp UserOp.Real := by
      change __eo_typeof (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)) =
        Term.UOp UserOp.Real
      rw [hM]
      rfl
    rw [hM]
    change
      __eo_typeof_plus (__eo_typeof m)
        (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) =
      Term.UOp UserOp.Real
    rw [hxTy, hM, hOneTy, typeof_plus_real_real, typeof_plus_real_real]

private theorem scale_smt_type_eq_m
    (m x : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation x ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof x = __eo_typeof m ->
    __smtx_typeof (__eo_to_smt (scale m x)) =
      __smtx_typeof (__eo_to_smt m) := by
  intro hmTrans hxTrans hMArith hxTy
  have hScaleArith :=
    scale_smt_type_of_eo_type m x hmTrans hxTrans hMArith hxTy
  have hScaleTrans : RuleProofs.eo_has_smt_translation (scale m x) := by
    unfold RuleProofs.eo_has_smt_translation
    rcases hScaleArith with hTy | hTy <;> rw [hTy] <;> simp
  have hScalePres :
      __smtx_typeof (__eo_to_smt (scale m x)) =
        __eo_to_smt_type (__eo_typeof (scale m x)) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (scale m x) (__eo_typeof (scale m x)) (__eo_to_smt (scale m x))
      rfl hScaleTrans rfl
  have hmPres :
      __smtx_typeof (__eo_to_smt m) =
        __eo_to_smt_type (__eo_typeof m) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      m (__eo_typeof m) (__eo_to_smt m) rfl hmTrans rfl
  rw [hScalePres, hmPres, scale_eo_type_of_eo_type m x hMArith hxTy]

private theorem pair_smt_type_of_eo_match
    (m a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    ((__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) := by
  intro _hmTrans haTrans hbTrans hMArith haTy hbTy
  rcases hMArith with hMInt | hMReal
  · left
    exact ⟨smt_type_of_eo_int a haTrans (by rw [haTy, hMInt]),
      smt_type_of_eo_int b hbTrans (by rw [hbTy, hMInt])⟩
  · right
    exact ⟨smt_type_of_eo_real a haTrans (by rw [haTy, hMReal]),
      smt_type_of_eo_real b hbTrans (by rw [hbTy, hMReal])⟩

private theorem scale_pair_smt_type
    (m a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    ((__smtx_typeof (__eo_to_smt (scale m a)) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt (scale m b)) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt (scale m a)) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt (scale m b)) = SmtType.Real)) := by
  intro hmTrans haTrans hbTrans hMArith haTy hbTy
  have hScaleA := scale_smt_type_eq_m m a hmTrans haTrans hMArith haTy
  have hScaleB := scale_smt_type_eq_m m b hmTrans hbTrans hMArith hbTy
  rcases hMArith with hMInt | hMReal
  · have hmInt := smt_type_of_eo_int m hmTrans hMInt
    left
    exact ⟨by rw [hScaleA, hmInt], by rw [hScaleB, hmInt]⟩
  · have hmReal := smt_type_of_eo_real m hmTrans hMReal
    right
    exact ⟨by rw [hScaleA, hmReal], by rw [hScaleB, hmReal]⟩

private theorem bool_of_true_eval
    {M : SmtModel} {t : Term} {b : Bool} :
    eo_interprets M t true ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
    b = true := by
  intro hTrue hEval
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue
  cases hTrue with
  | intro_true _ hEvalTrue =>
      rw [hEval] at hEvalTrue
      cases b <;> simp at hEvalTrue ⊢

private theorem eval_lt_of_denotes
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.lt) a b)) =
      SmtValue.Boolean (native_qlt qa qb) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.lt) a b) =
        SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_17, hEvalA, hEvalB]
    simp [__smtx_model_eval_lt, hqa, hqb, native_to_real_lt_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.lt) a b) =
        SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_17, hEvalA, hEvalB]
    simp [__smtx_model_eval_lt, hqa, hqb]

private theorem eval_leq_of_denotes
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.leq) a b)) =
      SmtValue.Boolean (native_qleq qa qb) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.leq) a b) =
        SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_18, hEvalA, hEvalB]
    simp [__smtx_model_eval_leq, hqa, hqb, native_to_real_leq_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.leq) a b) =
        SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_18, hEvalA, hEvalB]
    simp [__smtx_model_eval_leq, hqa, hqb]

private theorem eval_eq_of_denotes
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.eq) a b)) =
      SmtValue.Boolean (native_qeq qa qb) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.eq) a b) =
        SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [smtx_eval_eq_term_eq, hEvalA, hEvalB]
    simp [__smtx_model_eval_eq, native_veq, native_zeq, hqa, hqb,
      native_to_real_qeq_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.eq) a b) =
        SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [smtx_eval_eq_term_eq, hEvalA, hEvalB]
    simp [__smtx_model_eval_eq, native_veq, native_qeq, hqa, hqb]

private theorem eval_gt_of_denotes
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.gt) a b)) =
      SmtValue.Boolean (native_qlt qb qa) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.gt) a b) =
        SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_19, hEvalA, hEvalB]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, hqa, hqb,
      native_to_real_lt_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.gt) a b) =
        SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_19, hEvalA, hEvalB]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, hqa, hqb]

private theorem eval_geq_of_denotes
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.geq) a b)) =
      SmtValue.Boolean (native_qleq qb qa) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.geq) a b) =
        SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_20, hEvalA, hEvalB]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hqa, hqb,
      native_to_real_leq_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_to_real_coerce]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_to_real_coerce]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.geq) a b) =
        SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_20, hEvalA, hEvalB]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hqa, hqb]

private theorem rel_bool_of_pair_type
    (r a b : Term) :
    arithRelOp r ->
    ((__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) ->
    RuleProofs.eo_has_bool_type (relTerm r a b) := by
  intro hRel hTy
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    · rcases hTy with hTy | hTy
      · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
          (by rw [hTy.1, hTy.2])
          (by rw [hTy.1]; simp)
      · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
          (by rw [hTy.1, hTy.2])
          (by rw [hTy.1]; simp)
    · unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.lt) a b) =
          SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) by rfl]
      rcases hTy with hTy | hTy <;>
        rw [typeof_lt_eq] <;>
        simp [__smtx_typeof_arith_overload_op_2_ret, hTy.1, hTy.2]
    · unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.leq) a b) =
          SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) by rfl]
      rcases hTy with hTy | hTy <;>
        rw [typeof_leq_eq] <;>
        simp [__smtx_typeof_arith_overload_op_2_ret, hTy.1, hTy.2]
    · unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.gt) a b) =
          SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
      rcases hTy with hTy | hTy <;>
        rw [typeof_gt_eq] <;>
        simp [__smtx_typeof_arith_overload_op_2_ret, hTy.1, hTy.2]
    · unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.geq) a b) =
          SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
      rcases hTy with hTy | hTy <;>
        rw [typeof_geq_eq] <;>
        simp [__smtx_typeof_arith_overload_op_2_ret, hTy.1, hTy.2]

private theorem sign_pair_smt_type
    (m : Term) :
    RuleProofs.eo_has_smt_translation m ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    ((__smtx_typeof (__eo_to_smt m) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt (arithZero m)) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt m) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt (arithZero m)) = SmtType.Real)) := by
  intro hmTrans hMArith
  rcases hMArith with hMInt | hMReal
  · left
    constructor
    · exact smt_type_of_eo_int m hmTrans hMInt
    · rw [show arithZero m = Term.Numeral 0 by
        simp [arithZero, __arith_mk_zero, hMInt]]
      rw [eo_to_smt_numeral_eq, __smtx_typeof.eq_2]
  · right
    constructor
    · exact smt_type_of_eo_real m hmTrans hMReal
    · rw [show arithZero m = Term.Rational (native_mk_rational 0 1) by
        simp [arithZero, __arith_mk_zero, hMReal]]
      rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3]

private theorem neg_conclusion_bool_of_pair_type
    (r m a b : Term) :
    arithRelOp r ->
    ((__smtx_typeof (__eo_to_smt (scale m a)) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt (scale m b)) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt (scale m a)) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt (scale m b)) = SmtType.Real)) ->
    RuleProofs.eo_has_bool_type (negConclusion r m a b) := by
  intro hRel hTy
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.eq) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.gt) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.geq) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.lt) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.leq) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy

private theorem pos_conclusion_true
    (M : SmtModel) (hM : model_wf M)
    (m r a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    arithRelOp r ->
    eo_interprets M (relTerm (Term.UOp UserOp.gt) m (arithZero m)) true ->
    eo_interprets M (relTerm r a b) true ->
    eo_interprets M (posConclusion r m a b) true := by
  intro hmTrans haTrans hbTrans hMArith haTy hbTy hRel hSignTrue hFTrue
  have hPair := pair_smt_type_of_eo_match m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hScalePair := scale_pair_smt_type m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hConclBool : RuleProofs.eo_has_bool_type (posConclusion r m a b) := by
    simpa [posConclusion] using
      rel_bool_of_pair_type r (scale m a) (scale m b) hRel hScalePair
  have hmSmtArith := smt_type_of_eo_arith m hmTrans hMArith
  have haSmtArith : __smtx_typeof (__eo_to_smt a) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt a) = SmtType.Real := by
    rcases hPair with hPair | hPair
    · exact Or.inl hPair.1
    · exact Or.inr hPair.1
  have hbSmtArith : __smtx_typeof (__eo_to_smt b) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt b) = SmtType.Real := by
    rcases hPair with hPair | hPair
    · exact Or.inl hPair.2
    · exact Or.inr hPair.2
  rcases arith_atom_denote_real_of_smt_arith_type M hM m hmSmtArith with ⟨qm, hmDen⟩
  rcases arith_atom_denote_real_of_smt_arith_type M hM a haSmtArith with ⟨qa, haDen⟩
  rcases arith_atom_denote_real_of_smt_arith_type M hM b hbSmtArith with ⟨qb, hbDen⟩
  have hScaleADen := scale_denote M hM m a qm qa hmTrans haTrans
    hMArith haTy hmDen haDen
  have hScaleBDen := scale_denote M hM m b qm qb hmTrans hbTrans
    hMArith hbTy hmDen hbDen
  have hSignEval := eval_gt_of_denotes M hM m (arithZero m) qm
    (native_mk_rational 0 1) (sign_pair_smt_type m hmTrans hMArith)
    hmDen (arith_zero_denote M m hMArith)
  have hPos : native_qlt (native_mk_rational 0 1) qm = true :=
    bool_of_true_eval hSignTrue hSignEval
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    · have hFEval := eval_eq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qeq qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_eq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by
          simpa [posConclusion, relTerm] using
            (by rw [hEval, native_qeq_mul_congr_left hOrig] : __smtx_model_eval M
              (__eo_to_smt (relTerm (Term.UOp UserOp.eq) (scale m a) (scale m b))) =
                SmtValue.Boolean true))
    · have hFEval := eval_lt_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qlt qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_lt_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qlt_mul_of_pos_left hPos hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by simpa [posConclusion, relTerm, hScaled] using hEval)
    · have hFEval := eval_leq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qleq qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_leq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qleq_mul_of_pos_left hPos hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by simpa [posConclusion, relTerm, hScaled] using hEval)
    · have hFEval := eval_gt_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qlt qb qa = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_gt_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qlt_mul_of_pos_left hPos hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by simpa [posConclusion, relTerm, hScaled] using hEval)
    · have hFEval := eval_geq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qleq qb qa = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_geq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qleq_mul_of_pos_left hPos hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by simpa [posConclusion, relTerm, hScaled] using hEval)

private theorem neg_conclusion_true
    (M : SmtModel) (hM : model_wf M)
    (m r a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    arithRelOp r ->
    eo_interprets M (relTerm (Term.UOp UserOp.lt) m (arithZero m)) true ->
    eo_interprets M (relTerm r a b) true ->
    eo_interprets M (negConclusion r m a b) true := by
  intro hmTrans haTrans hbTrans hMArith haTy hbTy hRel hSignTrue hFTrue
  have hPair := pair_smt_type_of_eo_match m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hScalePair := scale_pair_smt_type m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hConclBool : RuleProofs.eo_has_bool_type (negConclusion r m a b) :=
    neg_conclusion_bool_of_pair_type r m a b hRel hScalePair
  have hmSmtArith := smt_type_of_eo_arith m hmTrans hMArith
  have haSmtArith : __smtx_typeof (__eo_to_smt a) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt a) = SmtType.Real := by
    rcases hPair with hPair | hPair
    · exact Or.inl hPair.1
    · exact Or.inr hPair.1
  have hbSmtArith : __smtx_typeof (__eo_to_smt b) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt b) = SmtType.Real := by
    rcases hPair with hPair | hPair
    · exact Or.inl hPair.2
    · exact Or.inr hPair.2
  rcases arith_atom_denote_real_of_smt_arith_type M hM m hmSmtArith with ⟨qm, hmDen⟩
  rcases arith_atom_denote_real_of_smt_arith_type M hM a haSmtArith with ⟨qa, haDen⟩
  rcases arith_atom_denote_real_of_smt_arith_type M hM b hbSmtArith with ⟨qb, hbDen⟩
  have hScaleADen := scale_denote M hM m a qm qa hmTrans haTrans
    hMArith haTy hmDen haDen
  have hScaleBDen := scale_denote M hM m b qm qb hmTrans hbTrans
    hMArith hbTy hmDen hbDen
  have hSignEval := eval_lt_of_denotes M hM m (arithZero m) qm
    (native_mk_rational 0 1) (sign_pair_smt_type m hmTrans hMArith)
    hmDen (arith_zero_denote M m hMArith)
  have hNeg : native_qlt qm (native_mk_rational 0 1) = true :=
    bool_of_true_eval hSignTrue hSignEval
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    · have hFEval := eval_eq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qeq qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_eq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hEvalTrue :
          __smtx_model_eval M
            (__eo_to_smt (relTerm (Term.UOp UserOp.eq) (scale m a) (scale m b))) =
              SmtValue.Boolean true := by
        rw [hEval, native_qeq_mul_congr_left hOrig]
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hEvalTrue)
    · have hFEval := eval_lt_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qlt qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_gt_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qlt_mul_of_neg_left hNeg hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale, hScaled] using hEval)
    · have hFEval := eval_leq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qleq qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_geq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qleq_mul_of_neg_left hNeg hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale, hScaled] using hEval)
    · have hFEval := eval_gt_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qlt qb qa = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_lt_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled :
          native_qlt (native_qmult qm qa) (native_qmult qm qb) = true :=
        native_qlt_mul_of_neg_left (c := qm) (a := qb) (b := qa) hNeg hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale, hScaled] using hEval)
    · have hFEval := eval_geq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qleq qb qa = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_leq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled :
          native_qleq (native_qmult qm qa) (native_qmult qm qb) = true :=
        native_qleq_mul_of_neg_left (c := qm) (a := qb) (b := qa) hNeg hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale, hScaled] using hEval)

private theorem and_true_bool
    (F : Term) :
    RuleProofs.eo_has_bool_type F ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (Term.Boolean true)) := by
  intro hF
  exact RuleProofs.eo_has_bool_type_and_of_bool_args F (Term.Boolean true)
    hF RuleProofs.eo_has_bool_type_true

private theorem facts_arith_mult_pos_rel
    (M : SmtModel) (hM : model_wf M)
    (m r a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation (relTerm r a b) ->
    arithRelOp r ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    __eo_typeof (__eo_prog_arith_mult_pos m (relTerm r a b)) = Term.Bool ->
    eo_interprets M (__eo_prog_arith_mult_pos m (relTerm r a b)) true := by
  intro hmTrans hFTrans hRel hMArith haTy hbTy hResultTy
  have hProgNe :
      __eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck :=
    by simpa [relTerm] using term_ne_stuck_of_typeof_bool hResultTy
  have hProgEq := prog_arith_mult_pos_eq_of_ne_stuck m r a b hRel hProgNe
  have hArgs := arith_rel_args_have_translation r a b hRel hFTrans
  have haTrans := hArgs.1
  have hbTrans := hArgs.2
  have hPair := pair_smt_type_of_eo_match m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hScalePair := scale_pair_smt_type m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hSignBool :
      RuleProofs.eo_has_bool_type
        (relTerm (Term.UOp UserOp.gt) m (arithZero m)) :=
    rel_bool_of_pair_type (Term.UOp UserOp.gt) m (arithZero m)
      (by simp [arithRelOp]) (sign_pair_smt_type m hmTrans hMArith)
  have hFBool : RuleProofs.eo_has_bool_type (relTerm r a b) :=
    rel_bool_of_pair_type r a b hRel hPair
  have hConclBool : RuleProofs.eo_has_bool_type (posConclusion r m a b) := by
    simpa [posConclusion] using
      rel_bool_of_pair_type r (scale m a) (scale m b) hRel hScalePair
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true)) :=
    and_true_bool (relTerm r a b) hFBool
  have hAnteBool :
      RuleProofs.eo_has_bool_type
        (posAntecedent m (relTerm r a b)) := by
    simpa [posAntecedent, relTerm] using
      RuleProofs.eo_has_bool_type_and_of_bool_args
        (relTerm (Term.UOp UserOp.gt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        hSignBool hTailBool
  change eo_interprets M
    (__eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b)) true
  rw [hProgEq]
  rcases CnfSupport.eo_interprets_bool_cases M hM
      (posAntecedent m (relTerm r a b)) hAnteBool with hAnteTrue | hAnteFalse
  · have hSignTrue :
        eo_interprets M (relTerm (Term.UOp UserOp.gt) m (arithZero m)) true :=
      RuleProofs.eo_interprets_and_left M
        (relTerm (Term.UOp UserOp.gt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        (by simpa [posAntecedent, relTerm] using hAnteTrue)
    have hTailTrue :
        eo_interprets M
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
            (Term.Boolean true)) true :=
      RuleProofs.eo_interprets_and_right M
        (relTerm (Term.UOp UserOp.gt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        (by simpa [posAntecedent, relTerm] using hAnteTrue)
    have hFTrue : eo_interprets M (relTerm r a b) true :=
      RuleProofs.eo_interprets_and_left M (relTerm r a b) (Term.Boolean true)
        hTailTrue
    exact CnfSupport.eo_interprets_imp_true_of_right_true M hM
      (posAntecedent m (relTerm r a b)) (posConclusion r m a b)
      hAnteBool
      (pos_conclusion_true M hM m r a b hmTrans haTrans hbTrans
        hMArith haTy hbTy hRel hSignTrue hFTrue)
  · exact CnfSupport.eo_interprets_imp_true_of_left_false M hM
      (posAntecedent m (relTerm r a b)) (posConclusion r m a b)
      hAnteFalse hConclBool

private theorem facts_arith_mult_neg_rel
    (M : SmtModel) (hM : model_wf M)
    (m r a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation (relTerm r a b) ->
    arithRelOp r ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    __eo_typeof (__eo_prog_arith_mult_neg m (relTerm r a b)) = Term.Bool ->
    eo_interprets M (__eo_prog_arith_mult_neg m (relTerm r a b)) true := by
  intro hmTrans hFTrans hRel hMArith haTy hbTy hResultTy
  have hProgNe :
      __eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck :=
    by simpa [relTerm] using term_ne_stuck_of_typeof_bool hResultTy
  have hProgEq := prog_arith_mult_neg_eq_of_ne_stuck m r a b hProgNe
  have hArgs := arith_rel_args_have_translation r a b hRel hFTrans
  have haTrans := hArgs.1
  have hbTrans := hArgs.2
  have hPair := pair_smt_type_of_eo_match m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hScalePair := scale_pair_smt_type m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hSignBool :
      RuleProofs.eo_has_bool_type
        (relTerm (Term.UOp UserOp.lt) m (arithZero m)) :=
    rel_bool_of_pair_type (Term.UOp UserOp.lt) m (arithZero m)
      (by simp [arithRelOp]) (sign_pair_smt_type m hmTrans hMArith)
  have hFBool : RuleProofs.eo_has_bool_type (relTerm r a b) :=
    rel_bool_of_pair_type r a b hRel hPair
  have hConclBool : RuleProofs.eo_has_bool_type (negConclusion r m a b) :=
    neg_conclusion_bool_of_pair_type r m a b hRel hScalePair
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true)) :=
    and_true_bool (relTerm r a b) hFBool
  have hAnteBool :
      RuleProofs.eo_has_bool_type
        (negAntecedent m (relTerm r a b)) := by
    simpa [negAntecedent, relTerm] using
      RuleProofs.eo_has_bool_type_and_of_bool_args
        (relTerm (Term.UOp UserOp.lt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        hSignBool hTailBool
  change eo_interprets M
    (__eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b)) true
  rw [hProgEq]
  rcases CnfSupport.eo_interprets_bool_cases M hM
      (negAntecedent m (relTerm r a b)) hAnteBool with hAnteTrue | hAnteFalse
  · have hSignTrue :
        eo_interprets M (relTerm (Term.UOp UserOp.lt) m (arithZero m)) true :=
      RuleProofs.eo_interprets_and_left M
        (relTerm (Term.UOp UserOp.lt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        (by simpa [negAntecedent, relTerm] using hAnteTrue)
    have hTailTrue :
        eo_interprets M
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
            (Term.Boolean true)) true :=
      RuleProofs.eo_interprets_and_right M
        (relTerm (Term.UOp UserOp.lt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        (by simpa [negAntecedent, relTerm] using hAnteTrue)
    have hFTrue : eo_interprets M (relTerm r a b) true :=
      RuleProofs.eo_interprets_and_left M (relTerm r a b) (Term.Boolean true)
        hTailTrue
    exact CnfSupport.eo_interprets_imp_true_of_right_true M hM
      (negAntecedent m (relTerm r a b)) (negConclusion r m a b)
      hAnteBool
      (neg_conclusion_true M hM m r a b hmTrans haTrans hbTrans
        hMArith haTy hbTy hRel hSignTrue hFTrue)
  · exact CnfSupport.eo_interprets_imp_true_of_left_false M hM
      (negAntecedent m (relTerm r a b)) (negConclusion r m a b)
      hAnteFalse hConclBool

private theorem prog_arith_mult_pos_mk_ne_stuck
    (m F : Term) :
    __eo_prog_arith_mult_pos m F ≠ Term.Stuck ->
    __mk_arith_mult_pos m F ≠ Term.Stuck := by
  intro hProg
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__eo_prog_arith_mult_pos] at hProg
  have hF : F ≠ Term.Stuck := by
    intro hF
    subst F
    cases m <;> simp [__eo_prog_arith_mult_pos] at hProg
  simp [__eo_prog_arith_mult_pos] at hProg
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hProg

private theorem prog_arith_mult_neg_mk_ne_stuck
    (m F : Term) :
    __eo_prog_arith_mult_neg m F ≠ Term.Stuck ->
    __mk_arith_mult_neg m F ≠ Term.Stuck := by
  intro hProg
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__eo_prog_arith_mult_neg] at hProg
  have hF : F ≠ Term.Stuck := by
    intro hF
    subst F
    cases m <;> simp [__eo_prog_arith_mult_neg] at hProg
  simp [__eo_prog_arith_mult_neg] at hProg
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hProg

private theorem mk_arith_mult_pos_stuck_of_not_rel
    (m r a b : Term) :
    m ≠ Term.Stuck ->
    ¬ arithRelOp r ->
    __mk_arith_mult_pos m (relTerm r a b) = Term.Stuck := by
  intro hM hRel
  rw [__mk_arith_mult_pos.eq_7]
  · exact hM
  all_goals
    intro a' b' hEq
    apply hRel
    cases r <;> simp [relTerm, arithRelOp] at hEq ⊢
    case UOp op =>
      cases op <;> simp at hEq ⊢

private theorem mk_arith_mult_pos_rel_of_ne_stuck
    (m r a b : Term) :
    __mk_arith_mult_pos m (relTerm r a b) ≠ Term.Stuck ->
    arithRelOp r := by
  intro hMk
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__mk_arith_mult_pos] at hMk
  by_cases hRel : arithRelOp r
  · exact hRel
  · exact False.elim (hMk (mk_arith_mult_pos_stuck_of_not_rel m r a b hM hRel))

private theorem arith_rel_inv_stuck_of_not_rel
    (r x y : Term) :
    ¬ arithRelOp r ->
    __arith_rel_inv r x y = Term.Stuck := by
  intro hRel
  cases r <;> simp [arithRelOp] at hRel ⊢
  case UOp op =>
    cases op <;> simp at hRel ⊢
    all_goals
      cases x <;> cases y <;> simp [__arith_rel_inv] at hRel ⊢
  all_goals
    cases x <;> cases y <;> simp [__arith_rel_inv] at hRel ⊢

private theorem arith_rel_inv_rel_of_ne_stuck
    (r x y : Term) :
    __arith_rel_inv r x y ≠ Term.Stuck ->
    arithRelOp r := by
  intro hInv
  by_cases hRel : arithRelOp r
  · exact hRel
  · exact False.elim (hInv (arith_rel_inv_stuck_of_not_rel r x y hRel))

private theorem mk_arith_mult_neg_rel_of_ne_stuck
    (m r a b : Term) :
    __mk_arith_mult_neg m (relTerm r a b) ≠ Term.Stuck ->
    arithRelOp r := by
  intro hMk
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__mk_arith_mult_neg] at hMk
  exact arith_rel_inv_rel_of_ne_stuck r
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a) (arithOne m)))
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b) (arithOne m)))
    (by simpa [relTerm, __mk_arith_mult_neg, hM, arithOne] using hMk)

private theorem pos_mk_ne_stuck_args
    (m F : Term) :
    __mk_arith_mult_pos m F ≠ Term.Stuck ->
    ∃ r a b, F = relTerm r a b ∧ arithRelOp r := by
  intro hMk
  have hMkOrig := hMk
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__mk_arith_mult_pos] at hMk
  cases F <;> simp [__mk_arith_mult_pos] at hMk
  case Apply f b =>
    cases f <;> try
      (exfalso; apply hMk; simp)
    case Apply r a =>
      refine ⟨r, a, b, ?_, ?_⟩
      · rfl
      · exact mk_arith_mult_pos_rel_of_ne_stuck m r a b
          (by simpa [relTerm] using hMkOrig)

private theorem neg_mk_ne_stuck_args
    (m F : Term) :
    __mk_arith_mult_neg m F ≠ Term.Stuck ->
    ∃ r a b, F = relTerm r a b ∧ arithRelOp r := by
  intro hMk
  have hMkOrig := hMk
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__mk_arith_mult_neg] at hMk
  cases F <;> simp [__mk_arith_mult_neg] at hMk
  case Apply f b =>
    cases f <;> simp at hMk
    case Apply r a =>
      refine ⟨r, a, b, ?_, ?_⟩
      · rfl
      · exact mk_arith_mult_neg_rel_of_ne_stuck m r a b
          (by simpa [relTerm] using hMkOrig)

private theorem eo_typeof_lt_bool_operands_not_stuck (A B : Term)
    (h : __eo_typeof_lt A B = Term.Bool) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  cases A <;> cases B <;>
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type, native_teq,
      native_ite, native_not, SmtEval.native_not] at h ⊢

private theorem pos_conclusion_scale_not_stuck
    (r m a b : Term) :
    arithRelOp r ->
    __eo_typeof (posConclusion r m a b) = Term.Bool ->
    __eo_typeof (scale m a) ≠ Term.Stuck ∧
      __eo_typeof (scale m b) ≠ Term.Stuck := by
  intro hRel hTy
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    · change __eo_typeof_eq (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
    · change __eo_typeof_lt (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact eo_typeof_lt_bool_operands_not_stuck _ _ hTy
    · change __eo_typeof_lt (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact eo_typeof_lt_bool_operands_not_stuck _ _ hTy
    · change __eo_typeof_lt (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact eo_typeof_lt_bool_operands_not_stuck _ _ hTy
    · change __eo_typeof_lt (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact eo_typeof_lt_bool_operands_not_stuck _ _ hTy

private theorem neg_conclusion_scale_not_stuck
    (r m a b : Term) :
    arithRelOp r ->
    __eo_typeof (negConclusion r m a b) = Term.Bool ->
    __eo_typeof (scale m a) ≠ Term.Stuck ∧
      __eo_typeof (scale m b) ≠ Term.Stuck := by
  intro hRel hTy
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp at hRel
    · change __eo_typeof_eq (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
    · change __eo_typeof_lt (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact eo_typeof_lt_bool_operands_not_stuck _ _ hTy
    · change __eo_typeof_lt (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact eo_typeof_lt_bool_operands_not_stuck _ _ hTy
    · change __eo_typeof_lt (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact eo_typeof_lt_bool_operands_not_stuck _ _ hTy
    · change __eo_typeof_lt (__eo_typeof (scale m a)) (__eo_typeof (scale m b)) =
        Term.Bool at hTy
      exact eo_typeof_lt_bool_operands_not_stuck _ _ hTy

private theorem pos_type_facts_of_result_ty
    (m r a b : Term) :
    arithRelOp r ->
    __eo_typeof (__eo_prog_arith_mult_pos m (relTerm r a b)) = Term.Bool ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨
        __eo_typeof m = Term.UOp UserOp.Real) ∧
      __eo_typeof a = __eo_typeof m ∧
      __eo_typeof b = __eo_typeof m := by
  intro hRel hResultTy
  have hProgNe :
      __eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠
        Term.Stuck := by
    simpa [relTerm] using term_ne_stuck_of_typeof_bool hResultTy
  have hProgEq := prog_arith_mult_pos_eq_of_ne_stuck m r a b hRel hProgNe
  have hTyData :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (posAntecedent m (relTerm r a b))) (posConclusion r m a b)) =
        Term.Bool := by
    change __eo_typeof
      (__eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b)) =
        Term.Bool at hResultTy
    rw [hProgEq] at hResultTy
    simpa [relTerm] using hResultTy
  change __eo_typeof_or (__eo_typeof (posAntecedent m (relTerm r a b)))
    (__eo_typeof (posConclusion r m a b)) = Term.Bool at hTyData
  have hConclTy := CnfSupport.typeof_or_eq_bool_right hTyData
  have hScaleTy := pos_conclusion_scale_not_stuck r m a b hRel hConclTy
  have hMArith := scale_m_eo_arith_of_scale_not_stuck m a hScaleTy.1
  have haTy :=
    (scale_arg_eo_type_of_scale_not_stuck m a hMArith hScaleTy.1).1
  have hbTy :=
    (scale_arg_eo_type_of_scale_not_stuck m b hMArith hScaleTy.2).1
  exact ⟨hMArith, haTy, hbTy⟩

private theorem neg_type_facts_of_result_ty
    (m r a b : Term) :
    arithRelOp r ->
    __eo_typeof (__eo_prog_arith_mult_neg m (relTerm r a b)) = Term.Bool ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨
        __eo_typeof m = Term.UOp UserOp.Real) ∧
      __eo_typeof a = __eo_typeof m ∧
      __eo_typeof b = __eo_typeof m := by
  intro hRel hResultTy
  have hProgNe :
      __eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠
        Term.Stuck := by
    simpa [relTerm] using term_ne_stuck_of_typeof_bool hResultTy
  have hProgEq := prog_arith_mult_neg_eq_of_ne_stuck m r a b hProgNe
  have hTyData :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (negAntecedent m (relTerm r a b))) (negConclusion r m a b)) =
        Term.Bool := by
    change __eo_typeof
      (__eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b)) =
        Term.Bool at hResultTy
    rw [hProgEq] at hResultTy
    simpa [relTerm] using hResultTy
  change __eo_typeof_or (__eo_typeof (negAntecedent m (relTerm r a b)))
    (__eo_typeof (negConclusion r m a b)) = Term.Bool at hTyData
  have hConclTy := CnfSupport.typeof_or_eq_bool_right hTyData
  have hScaleTy := neg_conclusion_scale_not_stuck r m a b hRel hConclTy
  have hMArith := scale_m_eo_arith_of_scale_not_stuck m a hScaleTy.1
  have haTy :=
    (scale_arg_eo_type_of_scale_not_stuck m a hMArith hScaleTy.1).1
  have hbTy :=
    (scale_arg_eo_type_of_scale_not_stuck m b hMArith hScaleTy.2).1
  exact ⟨hMArith, haTy, hbTy⟩

private theorem pos_prog_args_of_typeof_bool
    (m F : Term) :
    __eo_typeof (__eo_prog_arith_mult_pos m F) = Term.Bool ->
    ∃ r a b,
      F = relTerm r a b ∧
        arithRelOp r ∧
        (__eo_typeof m = Term.UOp UserOp.Int ∨
          __eo_typeof m = Term.UOp UserOp.Real) ∧
        __eo_typeof a = __eo_typeof m ∧
        __eo_typeof b = __eo_typeof m := by
  intro hResultTy
  have hProgNe := term_ne_stuck_of_typeof_bool hResultTy
  have hMkNe := prog_arith_mult_pos_mk_ne_stuck m F hProgNe
  rcases pos_mk_ne_stuck_args m F hMkNe with ⟨r, a, b, hF, hRel⟩
  subst F
  have hTypeFacts :=
    pos_type_facts_of_result_ty m r a b hRel (by simpa [relTerm] using hResultTy)
  exact ⟨r, a, b, rfl, hRel, hTypeFacts.1, hTypeFacts.2.1, hTypeFacts.2.2⟩

private theorem neg_prog_args_of_typeof_bool
    (m F : Term) :
    __eo_typeof (__eo_prog_arith_mult_neg m F) = Term.Bool ->
    ∃ r a b,
      F = relTerm r a b ∧
        arithRelOp r ∧
        (__eo_typeof m = Term.UOp UserOp.Int ∨
          __eo_typeof m = Term.UOp UserOp.Real) ∧
        __eo_typeof a = __eo_typeof m ∧
        __eo_typeof b = __eo_typeof m := by
  intro hResultTy
  have hProgNe := term_ne_stuck_of_typeof_bool hResultTy
  have hMkNe := prog_arith_mult_neg_mk_ne_stuck m F hProgNe
  rcases neg_mk_ne_stuck_args m F hMkNe with ⟨r, a, b, hF, hRel⟩
  subst F
  have hTypeFacts :=
    neg_type_facts_of_result_ty m r a b hRel (by simpa [relTerm] using hResultTy)
  exact ⟨r, a, b, rfl, hRel, hTypeFacts.1, hTypeFacts.2.1, hTypeFacts.2.2⟩

theorem facts_arith_mult_pos
    (M : SmtModel) (hM : model_wf M)
    (m F : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation F ->
    __eo_typeof (__eo_prog_arith_mult_pos m F) = Term.Bool ->
    eo_interprets M (__eo_prog_arith_mult_pos m F) true := by
  intro hmTrans hFTrans hResultTy
  rcases pos_prog_args_of_typeof_bool m F hResultTy with
    ⟨r, a, b, hF, hRel, hMArith, haTy, hbTy⟩
  subst F
  exact facts_arith_mult_pos_rel M hM m r a b hmTrans
    (by simpa [relTerm] using hFTrans) hRel hMArith haTy hbTy
    (by simpa [relTerm] using hResultTy)

theorem facts_arith_mult_neg
    (M : SmtModel) (hM : model_wf M)
    (m F : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation F ->
    __eo_typeof (__eo_prog_arith_mult_neg m F) = Term.Bool ->
    eo_interprets M (__eo_prog_arith_mult_neg m F) true := by
  intro hmTrans hFTrans hResultTy
  rcases neg_prog_args_of_typeof_bool m F hResultTy with
    ⟨r, a, b, hF, hRel, hMArith, haTy, hbTy⟩
  subst F
  exact facts_arith_mult_neg_rel M hM m r a b hmTrans
    (by simpa [relTerm] using hFTrans) hRel hMArith haTy hbTy
    (by simpa [relTerm] using hResultTy)

private abbrev absTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.abs) t

private abbrev multOp : Term :=
  Term.UOp UserOp.mult

private abbrev multSingleton (t : Term) : Term :=
  __eo_mk_apply (Term.Apply multOp t)
    (__eo_nil multOp (__eo_typeof t))

private theorem false_of_typeof_stuck_bool :
    __eo_typeof Term.Stuck = Term.Bool -> False := by
  intro h
  change Term.Stuck = Term.Bool at h
  cases h

private theorem get_nil_ne_of_is_list_true (f xs : Term) :
    __eo_is_list f xs = Term.Boolean true ->
    __eo_get_nil_rec f xs ≠ Term.Stuck := by
  intro h hs
  cases f <;> cases xs <;>
    simp [__eo_is_list, __eo_is_ok, hs, native_teq, native_not,
      SmtEval.native_not] at h

private theorem list_concat_rec_nil_of_ne_stuck {b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Numeral 1) b = b := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

private theorem list_concat_rec_real_nil_of_ne_stuck {b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Rational (native_mk_rational 1 1)) b = b := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

private theorem list_concat_rec_cons_of_ne_stuck {f x xs b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) xs) b =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec xs b) := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

private theorem eo_type_int_of_smt_type_int (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __eo_typeof t = Term.UOp UserOp.Int := by
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation t
    (by rw [hTy]; simp)
  have hEoSmt : __eo_to_smt_type (__eo_typeof t) = SmtType.Int := by
    rw [← hMatch, hTy]
  exact TranslationProofs.eo_to_smt_type_eq_int hEoSmt

private theorem eo_type_real_of_smt_type_real (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __eo_typeof t = Term.UOp UserOp.Real := by
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation t
    (by rw [hTy]; simp)
  have hEoSmt : __eo_to_smt_type (__eo_typeof t) = SmtType.Real := by
    rw [← hMatch, hTy]
  exact TranslationProofs.eo_to_smt_type_eq_real hEoSmt

private theorem eq_of_eo_eq_true {a b : Term} :
    __eo_eq a b = Term.Boolean true -> a = b := by
  intro h
  have hba : b = a := by
    cases a <;> cases b <;> simpa [__eo_eq, native_teq] using h
  exact hba.symm

private theorem eo_eq_self_of_ne_stuck {t : Term} (h : t ≠ Term.Stuck) :
    __eo_eq t t = Term.Boolean true := by
  cases t <;> simp [__eo_eq, native_teq] at h ⊢

private theorem bool_of_false_eval
    {M : SmtModel} {t : Term} {b : Bool} :
    eo_interprets M t false ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
    b = false := by
  intro hFalse hEval
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hFalse
  cases hFalse with
  | intro_false _ hEvalFalse =>
      rw [hEval] at hEvalFalse
      cases b <;> simp at hEvalFalse ⊢

/- BEGIN: superseded integer-only abs-comparison machinery.
   Retained temporarily while the generic arithmetic-product proof is brought up.
private abbrev intAbs (n : native_Int) : native_Int :=
  ((Int.natAbs n : Nat) : Int)

private inductive MultListEval (M : SmtModel) : Term -> native_Int -> Prop
  | nil : MultListEval M (Term.Numeral 1) 1
  | cons {x xs : Term} {nx nxs : native_Int} :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int ->
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral nx ->
      MultListEval M xs nxs ->
      MultListEval M (Term.Apply (Term.Apply multOp x) xs) (nx * nxs)

private theorem false_of_typeof_stuck_bool :
    __eo_typeof Term.Stuck = Term.Bool -> False := by
  intro h
  change Term.Stuck = Term.Bool at h
  cases h

private theorem MultListEval.ne_stuck
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MultListEval M xs n) : xs ≠ Term.Stuck := by
  cases h <;> simp

private theorem MultListEval.type_int
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MultListEval M xs n) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.Int := by
  induction h with
  | nil =>
      rw [eo_to_smt_numeral_eq, __smtx_typeof.eq_2]
  | cons hxTy _ _ ih =>
      change __smtx_typeof (SmtTerm.mult _ _) = SmtType.Int
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hxTy, ih]

private theorem MultListEval.eval
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MultListEval M xs n) :
    __smtx_model_eval M (__eo_to_smt xs) = SmtValue.Numeral n := by
  induction h with
  | nil =>
      rw [eo_to_smt_numeral_eq, __smtx_model_eval.eq_2]
  | cons _ hxEval _ ih =>
      change __smtx_model_eval M (SmtTerm.mult _ _) = _
      rw [__smtx_model_eval.eq_16, hxEval, ih]
      simp [__smtx_model_eval_mult, native_zmult]

private theorem get_nil_ne_of_is_list_true (f xs : Term) :
    __eo_is_list f xs = Term.Boolean true ->
    __eo_get_nil_rec f xs ≠ Term.Stuck := by
  intro h hs
  cases f <;> cases xs <;>
    simp [__eo_is_list, __eo_is_ok, hs, native_teq, native_not,
      SmtEval.native_not] at h

private theorem MultListEval.is_list
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MultListEval M xs n) :
    __eo_is_list multOp xs = Term.Boolean true := by
  induction h with
  | nil =>
      native_decide
  | cons _ _ _ ih =>
      unfold __eo_is_list __eo_is_ok
      have hne := get_nil_ne_of_is_list_true _ _ ih
      simp [__eo_get_nil_rec, __eo_requires, hne, native_ite, native_teq,
        native_not, SmtEval.native_not, multOp]

private theorem list_concat_rec_nil_of_ne_stuck {b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Numeral 1) b = b := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

private theorem list_concat_rec_cons_of_ne_stuck {f x xs b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) xs) b =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec xs b) := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

private theorem MultListEval.concat_rec
    {M : SmtModel} {a b : Term} {na nb : native_Int}
    (ha : MultListEval M a na) (hb : MultListEval M b nb) :
    MultListEval M (__eo_list_concat_rec a b) (na * nb) := by
  induction ha generalizing b nb with
  | nil =>
      rw [list_concat_rec_nil_of_ne_stuck (MultListEval.ne_stuck hb)]
      simpa using hb
  | cons hxTy hxEval _ ih =>
      have hTail := ih hb
      have hTailNe := MultListEval.ne_stuck hTail
      rw [list_concat_rec_cons_of_ne_stuck (MultListEval.ne_stuck hb)]
      simpa [__eo_mk_apply, hTailNe, Int.mul_assoc, multOp] using
        (MultListEval.cons hxTy hxEval hTail)

private theorem MultListEval.concat
    {M : SmtModel} {a b : Term} {na nb : native_Int}
    (ha : MultListEval M a na) (hb : MultListEval M b nb) :
    MultListEval M (__eo_list_concat multOp a b) (na * nb) := by
  have haList := MultListEval.is_list ha
  have hbList := MultListEval.is_list hb
  simpa [__eo_list_concat, haList, hbList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not, multOp] using
    MultListEval.concat_rec ha hb

private theorem eo_type_int_of_smt_type_int (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __eo_typeof t = Term.UOp UserOp.Int := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t
      (by rw [hTy]; simp)
  have hEoSmt : __eo_to_smt_type (__eo_typeof t) = SmtType.Int := by
    rw [← hMatch, hTy]
  exact TranslationProofs.eo_to_smt_type_eq_int hEoSmt

private theorem MultListEval.singleton
    (M : SmtModel) (t : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral n) :
    MultListEval M (multSingleton t) n := by
  have hEoTy := eo_type_int_of_smt_type_int t hTy
  have hCons :
      MultListEval M (Term.Apply (Term.Apply multOp t) (Term.Numeral 1))
        (n * 1) :=
    MultListEval.cons hTy hEval MultListEval.nil
  simpa [multSingleton, multOp, __eo_nil, __eo_nil_mult, __arith_mk_one,
    hEoTy, __eo_mk_apply] using hCons

private theorem intAbs_neg_case (n : native_Int) (h : n < 0) :
    intAbs n = -n := by
  let m : Int := n
  have hm : m < 0 := h
  change ((Int.natAbs m : Nat) : Int) = -m
  have hnon : 0 ≤ -m := by omega
  have h1 : ↑(-m).natAbs = -m := Int.natAbs_of_nonneg hnon
  simpa [Int.natAbs_neg] using h1

private theorem intAbs_nonneg_case (n : native_Int) (h : ¬ n < 0) :
    intAbs n = n := by
  let m : Int := n
  have hm : ¬ m < 0 := h
  change ((Int.natAbs m : Nat) : Int) = m
  have hnon : 0 ≤ m := by omega
  exact Int.natAbs_of_nonneg hnon

private theorem model_eval_abs_int
    (M : SmtModel) (x : Term) (n : native_Int)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral n) :
    __smtx_model_eval M (__eo_to_smt (absTerm x)) =
      SmtValue.Numeral (intAbs n) := by
  rw [show __eo_to_smt (absTerm x) = SmtTerm.abs (__eo_to_smt x) by rfl]
  rw [__smtx_model_eval.eq_24, hx]
  unfold __smtx_model_eval_abs
  by_cases hneg : n < 0
  · have hNat := intAbs_neg_case n hneg
    simp [__smtx_model_eval_lt, __smtx_model_eval_ite, __smtx_model_eval__,
      native_zlt, native_zplus, native_zneg, hneg, hNat, intAbs]
  · have hNat := intAbs_nonneg_case n hneg
    simp [__smtx_model_eval_lt, __smtx_model_eval_ite, native_zlt, hneg,
      hNat, intAbs]

private theorem native_zlt_intAbs_true_iff
    (a b : native_Int) :
    native_zlt (intAbs a) (intAbs b) = true ↔
      Int.natAbs a < Int.natAbs b := by
  unfold native_zlt intAbs
  simp

private theorem native_zeq_intAbs_true_iff
    (a b : native_Int) :
    native_zeq (intAbs a) (intAbs b) = true ↔
      Int.natAbs a = Int.natAbs b := by
  unfold native_zeq intAbs
  simp [Int.ofNat_inj]

private theorem intAbs_eq_of_natAbs_eq
    {a b : native_Int} (h : Int.natAbs a = Int.natAbs b) :
    intAbs a = intAbs b := by
  simpa [intAbs, h]

private theorem eq_of_eo_eq_true {a b : Term} :
    __eo_eq a b = Term.Boolean true -> a = b := by
  intro h
  have hba : b = a := by
    cases a <;> cases b <;> simpa [__eo_eq, native_teq] using h
  exact hba.symm

private theorem eo_eq_self_of_ne_stuck {t : Term} (h : t ≠ Term.Stuck) :
    __eo_eq t t = Term.Boolean true := by
  cases t <;> simp [__eo_eq, native_teq] at h ⊢

private theorem bool_of_false_eval
    {M : SmtModel} {t : Term} {b : Bool} :
    eo_interprets M t false ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
    b = false := by
  intro hFalse hEval
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hFalse
  cases hFalse with
  | intro_false _ hEvalFalse =>
      rw [hEval] at hEvalFalse
      cases b <;> simp at hEvalFalse ⊢

private theorem smt_type_int_of_abs_non_none (t : Term)
    (h : __smtx_typeof (__eo_to_smt (absTerm t)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl] at h
  rw [typeof_abs_eq] at h
  cases ht : __smtx_typeof (__eo_to_smt t) <;>
    simp [native_Teq, native_ite, ht] at h ⊢

private theorem gt_abs_operands_smt_int_of_bool (t u : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u))) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Int := by
  rcases rel_operands_arith_type_of_gt_has_bool_type (absTerm t) (absTerm u)
      (by simpa [relTerm, absTerm] using hBool) with hInt | hReal
  · exact ⟨smt_type_int_of_abs_non_none t (by rw [hInt.1]; simp),
      smt_type_int_of_abs_non_none u (by rw [hInt.2]; simp)⟩
  · have hAbsT := smt_type_int_of_abs_non_none t (by rw [hReal.1]; simp)
    have hAbsType : __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Int := by
      rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl]
      rw [typeof_abs_eq, hAbsT]
      simp [native_Teq, native_ite]
    rw [hAbsType] at hReal
    simp at hReal

private theorem eq_abs_operands_smt_int_of_bool (t u : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u))) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Int := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (absTerm t) (absTerm u) (by simpa [relTerm, absTerm] using hBool)
    with ⟨hSame, hNN⟩
  have ht := smt_type_int_of_abs_non_none t hNN
  have huNN : __smtx_typeof (__eo_to_smt (absTerm u)) ≠ SmtType.None := by
    intro hNone
    apply hNN
    rw [hSame, hNone]
  exact ⟨ht, smt_type_int_of_abs_non_none u huNN⟩

private theorem abs_gt_factor
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    eo_interprets M (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) true ->
    ∃ nt nu : native_Int,
      MultListEval M (multSingleton t) nt ∧
      MultListEval M (multSingleton u) nu ∧
      Int.natAbs nu < Int.natAbs nt := by
  intro hTrue
  have hBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue
  have hTy := gt_abs_operands_smt_int_of_bool t u hBool
  rcases smt_eval_int_of_type M hM t hTy.1 with ⟨nt, htEval⟩
  rcases smt_eval_int_of_type M hM u hTy.2 with ⟨nu, huEval⟩
  have htAbs := model_eval_abs_int M t nt htEval
  have huAbs := model_eval_abs_int M u nu huEval
  have hRelEval :
      __smtx_model_eval M
        (__eo_to_smt (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u))) =
        SmtValue.Boolean (native_zlt (intAbs nu) (intAbs nt)) := by
    rw [show __eo_to_smt
        (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) =
        SmtTerm.gt (__eo_to_smt (absTerm t)) (__eo_to_smt (absTerm u)) by rfl]
    rw [__smtx_model_eval.eq_19, htAbs, huAbs]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt]
  have hLtBool := bool_of_true_eval hTrue hRelEval
  exact ⟨nt, nu, MultListEval.singleton M t nt hTy.1 htEval,
    MultListEval.singleton M u nu hTy.2 huEval,
    (native_zlt_intAbs_true_iff nu nt).mp hLtBool⟩

private theorem abs_eq_factor
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    eo_interprets M (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) true ->
    ∃ nt nu : native_Int,
      __smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral nt ∧
      MultListEval M (multSingleton t) nt ∧
      MultListEval M (multSingleton u) nu ∧
      Int.natAbs nt = Int.natAbs nu := by
  intro hTrue
  have hBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue
  have hTy := eq_abs_operands_smt_int_of_bool t u hBool
  rcases smt_eval_int_of_type M hM t hTy.1 with ⟨nt, htEval⟩
  rcases smt_eval_int_of_type M hM u hTy.2 with ⟨nu, huEval⟩
  have htAbs := model_eval_abs_int M t nt htEval
  have huAbs := model_eval_abs_int M u nu huEval
  have hRelEval :
      __smtx_model_eval M
        (__eo_to_smt (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u))) =
        SmtValue.Boolean (native_zeq (intAbs nt) (intAbs nu)) := by
    rw [show __eo_to_smt
        (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) =
        SmtTerm.eq (__eo_to_smt (absTerm t)) (__eo_to_smt (absTerm u)) by rfl]
    rw [smtx_eval_eq_term_eq, htAbs, huAbs]
    simp [__smtx_model_eval_eq, native_veq, native_zeq]
  have hEqBool := bool_of_true_eval hTrue hRelEval
  exact ⟨nt, nu, hTy.1, htEval, MultListEval.singleton M t nt hTy.1 htEval,
    MultListEval.singleton M u nu hTy.2 huEval,
    (native_zeq_intAbs_true_iff nt nu).mp hEqBool⟩

private theorem numeral_zero_of_to_real_zero {n : native_Int} :
    native_to_real n = native_mk_rational 0 1 -> n = 0 := by
  intro h
  have h' : ((n : Rat) / (1 : Rat)) = ((0 : Rat) / (1 : Rat)) := by
    simpa [native_to_real, native_mk_rational] using h
  rw [rat_div_one_intCast n, rat_zero_div_one] at h'
  exact Rat.intCast_inj.mp h'

private theorem eval_zero_of_to_q_zero_and_smt_int
    (M : SmtModel) (z : Term)
    (hToQ : __eo_to_q z = Term.Rational (native_mk_rational 0 1))
    (hTy : __smtx_typeof (__eo_to_smt z) = SmtType.Int) :
    __smtx_model_eval M (__eo_to_smt z) = SmtValue.Numeral 0 := by
  cases z <;> simp [__eo_to_q] at hToQ
  case Numeral n =>
    have hn : n = 0 := numeral_zero_of_to_real_zero hToQ
    subst n
    rw [eo_to_smt_numeral_eq, __smtx_model_eval.eq_2]
  case Rational q =>
    subst q
    rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3] at hTy
    simp at hTy

private theorem eq_rhs_smt_int_of_bool_left_int (t z : Term)
    (hTyT : __smtx_typeof (__eo_to_smt t) = SmtType.Int)
    (hBool : RuleProofs.eo_has_bool_type (relTerm (Term.UOp UserOp.eq) t z)) :
    __smtx_typeof (__eo_to_smt z) = SmtType.Int := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t z
      (by simpa [relTerm] using hBool) with ⟨hSame, _⟩
  rw [← hSame, hTyT]

private theorem natAbs_pos_of_native_zeq_zero_false
    (n : native_Int) :
    native_zeq n 0 = false -> 0 < Int.natAbs n := by
  intro h
  unfold native_zeq at h
  by_cases hn : n = 0
  · simp [hn] at h
  · exact Int.natAbs_pos.mpr hn

private theorem abs_factor_nonzero
    (M : SmtModel) (t z : Term) (nt : native_Int)
    (hTyT : __smtx_typeof (__eo_to_smt t) = SmtType.Int)
    (htEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral nt)
    (hToQ : __eo_to_q z = Term.Rational (native_mk_rational 0 1)) :
    eo_interprets M (Term.Apply (Term.UOp UserOp.not)
      (relTerm (Term.UOp UserOp.eq) t z)) true ->
    0 < Int.natAbs nt := by
  intro hNotTrue
  have hEqFalse :=
    RuleProofs.eo_interprets_not_true_implies_false M
      (relTerm (Term.UOp UserOp.eq) t z) hNotTrue
  have hNotBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hNotTrue
  have hEqBool :=
    RuleProofs.eo_has_bool_type_not_arg (relTerm (Term.UOp UserOp.eq) t z)
      (by simpa [relTerm] using hNotBool)
  have hTyZ := eq_rhs_smt_int_of_bool_left_int t z hTyT hEqBool
  have hzEval := eval_zero_of_to_q_zero_and_smt_int M z hToQ hTyZ
  have hEqEval :
      __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.eq) t z)) =
        SmtValue.Boolean (native_zeq nt 0) := by
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.eq) t z) =
        SmtTerm.eq (__eo_to_smt t) (__eo_to_smt z) by rfl]
    rw [smtx_eval_eq_term_eq, htEval, hzEval]
    simp [__smtx_model_eval_eq, native_veq, native_zeq]
  have hEqFalseBool := bool_of_false_eval hEqFalse hEqEval
  exact natAbs_pos_of_native_zeq_zero_false nt hEqFalseBool

private theorem natAbs_mul_lt_mul_of_lt_lt
    {a b c d : native_Int}
    (hAB : Int.natAbs b < Int.natAbs a)
    (hCD : Int.natAbs d < Int.natAbs c) :
    Int.natAbs (b * d) < Int.natAbs (a * c) := by
  rw [Int.natAbs_mul, Int.natAbs_mul]
  have hCpos : 0 < Int.natAbs c := Nat.lt_of_le_of_lt (Nat.zero_le _) hCD
  have hDleC : Int.natAbs d ≤ Int.natAbs c := Nat.le_of_lt hCD
  have h1 :
      Int.natAbs b * Int.natAbs d ≤
        Int.natAbs b * Int.natAbs c :=
    Nat.mul_le_mul_left _ hDleC
  have h2 :
      Int.natAbs b * Int.natAbs c <
        Int.natAbs a * Int.natAbs c :=
    Nat.mul_lt_mul_of_pos_right hAB hCpos
  exact Nat.lt_of_le_of_lt h1 h2

private theorem natAbs_mul_eq_of_eq_eq
    {a b c d : native_Int}
    (hAB : Int.natAbs a = Int.natAbs b)
    (hCD : Int.natAbs c = Int.natAbs d) :
    Int.natAbs (a * c) = Int.natAbs (b * d) := by
  rw [Int.natAbs_mul, Int.natAbs_mul, hAB, hCD]

private theorem natAbs_mul_lt_mul_of_lt_eq_pos
    {a b c d : native_Int}
    (hAB : Int.natAbs b < Int.natAbs a)
    (hCD : Int.natAbs c = Int.natAbs d)
    (hPos : 0 < Int.natAbs c) :
    Int.natAbs (b * d) < Int.natAbs (a * c) := by
  rw [Int.natAbs_mul, Int.natAbs_mul, ← hCD]
  exact Nat.mul_lt_mul_of_pos_right hAB hPos

-/

/- Superseded aggregate-product experiment.
private inductive MultListProduct (M : SmtModel) : Term -> ArithProduct -> Prop
  | nilInt : MultListProduct M (Term.Numeral 1) (some (.int 1))
  | nilReal :
      MultListProduct M (Term.Rational (native_mk_rational 1 1)) (some (.real 1))
  | cons {x xs : Term} {vx : ArithValue} {vxs : ArithProduct} :
      __smtx_typeof (__eo_to_smt x) = vx.smtType ->
      __smtx_model_eval M (__eo_to_smt x) = vx.smtValue ->
      MultListProduct M xs vxs ->
      MultListProduct M (Term.Apply (Term.Apply multOp x) xs)
        (ArithProduct.mul (some vx) vxs)

private theorem MultListProduct.ne_stuck
    {M : SmtModel} {xs : Term} {v : ArithProduct}
    (h : MultListProduct M xs v) : xs ≠ Term.Stuck := by
  cases h <;> simp

private theorem MultListProduct.smt_type
    {M : SmtModel} {xs : Term} {v : ArithProduct}
    (h : MultListProduct M xs v) :
    __smtx_typeof (__eo_to_smt xs) = v.smtType := by
  induction h with
  | nilInt => rw [eo_to_smt_numeral_eq, __smtx_typeof.eq_2]
  | nilReal => rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3]
  | cons hxTy _ _ ih =>
      change __smtx_typeof (SmtTerm.mult _ _) = _
      rw [typeof_mult_eq, hxTy, ih, ArithProduct.smtType_mul]

private theorem MultListProduct.eval
    {M : SmtModel} {xs : Term} {v : ArithProduct}
    (h : MultListProduct M xs v) :
    __smtx_model_eval M (__eo_to_smt xs) = v.smtValue := by
  induction h with
  | nilInt => rw [eo_to_smt_numeral_eq, __smtx_model_eval.eq_2]
  | nilReal => rw [eo_to_smt_rational_eq, __smtx_model_eval.eq_3]
  | cons _ hxEval _ ih =>
      change __smtx_model_eval M (SmtTerm.mult _ _) = _
      rw [__smtx_model_eval.eq_16, hxEval, ih]
      exact ArithProduct.modelEval_mul _ _

private theorem MultListProduct.is_list
    {M : SmtModel} {xs : Term} {v : ArithProduct}
    (h : MultListProduct M xs v) :
    __eo_is_list multOp xs = Term.Boolean true := by
  induction h with
  | nilInt => native_decide
  | nilReal => native_decide
  | cons _ _ _ ih =>
      unfold __eo_is_list __eo_is_ok
      have hne := get_nil_ne_of_is_list_true _ _ ih
      simp [__eo_get_nil_rec, __eo_requires, hne, native_ite, native_teq,
        native_not, SmtEval.native_not, multOp]

private theorem list_concat_rec_real_nil_of_ne_stuck {b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Rational (native_mk_rational 1 1)) b = b := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

private theorem MultListProduct.concat_rec
    {M : SmtModel} {a b : Term} {va vb : ArithProduct}
    (ha : MultListProduct M a va) (hb : MultListProduct M b vb) :
    MultListProduct M (__eo_list_concat_rec a b) (ArithProduct.mul va vb) := by
  induction ha generalizing b vb with
  | nilInt =>
      rw [list_concat_rec_nil_of_ne_stuck (MultListProduct.ne_stuck hb)]
      simpa [ArithProduct.mul] using hb
  | nilReal =>
      rw [list_concat_rec_real_nil_of_ne_stuck (MultListProduct.ne_stuck hb)]
      simpa [ArithProduct.mul] using hb
  | @cons x xs vx vxs hxTy hxEval _ ih =>
      have hTail := ih hb
      have hTailNe := MultListProduct.ne_stuck hTail
      rw [list_concat_rec_cons_of_ne_stuck (MultListProduct.ne_stuck hb)]
      rw [ArithProduct.mul_assoc]
      simpa [__eo_mk_apply, hTailNe, multOp] using
        (MultListProduct.cons hxTy hxEval hTail)

private theorem MultListProduct.concat
    {M : SmtModel} {a b : Term} {va vb : ArithProduct}
    (ha : MultListProduct M a va) (hb : MultListProduct M b vb) :
    MultListProduct M (__eo_list_concat multOp a b) (ArithProduct.mul va vb) := by
  have haList := MultListProduct.is_list ha
  have hbList := MultListProduct.is_list hb
  simpa [__eo_list_concat, haList, hbList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not, multOp] using
    MultListProduct.concat_rec ha hb

private theorem eo_type_real_of_smt_type_real (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __eo_typeof t = Term.UOp UserOp.Real := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t
      (by rw [hTy]; simp)
  have hEoSmt : __eo_to_smt_type (__eo_typeof t) = SmtType.Real := by
    rw [← hMatch, hTy]
  exact TranslationProofs.eo_to_smt_type_eq_real hEoSmt

private theorem MultListProduct.singleton
    (M : SmtModel) (t : Term) (v : ArithValue)
    (hTy : __smtx_typeof (__eo_to_smt t) = v.smtType)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = v.smtValue) :
    MultListProduct M (multSingleton t) (some v) := by
  cases v with
  | int n =>
      have hEoTy := eo_type_int_of_smt_type_int t hTy
      have hCons := MultListProduct.cons hTy hEval (MultListProduct.nilInt (M := M))
      simpa [multSingleton, multOp, __eo_nil, __eo_nil_mult, __arith_mk_one,
        hEoTy, __eo_mk_apply, ArithProduct.mul, ArithValue.kind,
        ArithValue.mul] using hCons
  | real q =>
      have hEoTy := eo_type_real_of_smt_type_real t hTy
      have hCons := MultListProduct.cons hTy hEval (MultListProduct.nilReal (M := M))
      simpa [multSingleton, multOp, __eo_nil, __eo_nil_mult, __arith_mk_one,
        hEoTy, __eo_mk_apply, ArithProduct.mul, ArithValue.kind,
        ArithValue.mul, native_mk_rational] using hCons

private theorem model_eval_abs_arith
    (M : SmtModel) (x : Term) (v : ArithValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = v.smtValue) :
    __smtx_model_eval M (__eo_to_smt (absTerm x)) = v.abs.smtValue := by
  rw [show __eo_to_smt (absTerm x) = SmtTerm.abs (__eo_to_smt x) by rfl]
  rw [__smtx_model_eval.eq_24, hx]
  cases v <;> simp [__smtx_model_eval_abs, ArithValue.abs,
    ArithValue.smtValue]

private theorem smt_type_of_abs_eq_int (t : Term)
    (h : __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl,
    typeof_abs_eq] at h
  cases ht : __smtx_typeof (__eo_to_smt t) <;>
    simp [__smtx_typeof_arith_overload_op_1, ht] at h ⊢

private theorem smt_type_of_abs_eq_real (t : Term)
    (h : __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
  rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl,
    typeof_abs_eq] at h
  cases ht : __smtx_typeof (__eo_to_smt t) <;>
    simp [__smtx_typeof_arith_overload_op_1, ht] at h ⊢

private theorem gt_abs_operands_smt_arith_of_bool (t u : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u))) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt t) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Real) := by
  rcases rel_operands_arith_type_of_gt_has_bool_type (absTerm t) (absTerm u)
      (by simpa [relTerm, absTerm] using hBool) with hInt | hReal
  · exact Or.inl ⟨smt_type_of_abs_eq_int t hInt.1,
      smt_type_of_abs_eq_int u hInt.2⟩
  · exact Or.inr ⟨smt_type_of_abs_eq_real t hReal.1,
      smt_type_of_abs_eq_real u hReal.2⟩

private theorem eq_abs_operands_smt_arith_of_bool (t u : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u))) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt t) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Real) := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (absTerm t) (absTerm u) (by simpa [relTerm, absTerm] using hBool)
    with ⟨hSame, hNN⟩
  cases ht : __smtx_typeof (__eo_to_smt t) <;>
    simp [absTerm, typeof_abs_eq, __smtx_typeof_arith_overload_op_1, ht] at hNN
  · have htAbs : __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Int := by
      simp [absTerm, typeof_abs_eq, __smtx_typeof_arith_overload_op_1, ht]
    have huAbs : __smtx_typeof (__eo_to_smt (absTerm u)) = SmtType.Int := by
      rw [← hSame, htAbs]
    exact Or.inl ⟨ht, smt_type_of_abs_eq_int u huAbs⟩
  · have htAbs : __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Real := by
      simp [absTerm, typeof_abs_eq, __smtx_typeof_arith_overload_op_1, ht]
    have huAbs : __smtx_typeof (__eo_to_smt (absTerm u)) = SmtType.Real := by
      rw [← hSame, htAbs]
    exact Or.inr ⟨ht, smt_type_of_abs_eq_real u huAbs⟩

private theorem eval_gt_abs_values (M : SmtModel) (t u : Term)
    (vt vu : ArithValue)
    (hKind : vt.kind = vu.kind)
    (ht : __smtx_model_eval M (__eo_to_smt (absTerm t)) = vt.abs.smtValue)
    (hu : __smtx_model_eval M (__eo_to_smt (absTerm u)) = vu.abs.smtValue) :
    __smtx_model_eval M
        (__eo_to_smt (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u))) =
      SmtValue.Boolean (ArithValue.ltBool vu.abs vt.abs) := by
  rw [show __eo_to_smt
      (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) =
      SmtTerm.gt (__eo_to_smt (absTerm t)) (__eo_to_smt (absTerm u)) by rfl]
  rw [__smtx_model_eval.eq_19, ht, hu]
  cases vt <;> cases vu <;>
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, ArithValue.abs,
      ArithValue.smtValue, ArithValue.ltBool, ArithValue.kind] at hKind ⊢

private theorem eval_eq_abs_values (M : SmtModel) (t u : Term)
    (vt vu : ArithValue)
    (hKind : vt.kind = vu.kind)
    (ht : __smtx_model_eval M (__eo_to_smt (absTerm t)) = vt.abs.smtValue)
    (hu : __smtx_model_eval M (__eo_to_smt (absTerm u)) = vu.abs.smtValue) :
    __smtx_model_eval M
        (__eo_to_smt (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u))) =
      SmtValue.Boolean (ArithValue.eqBool vt.abs vu.abs) := by
  rw [show __eo_to_smt
      (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) =
      SmtTerm.eq (__eo_to_smt (absTerm t)) (__eo_to_smt (absTerm u)) by rfl]
  rw [smtx_eval_eq_term_eq, ht, hu]
  cases vt <;> cases vu <;>
    simp [__smtx_model_eval_eq, native_veq, ArithValue.abs,
      ArithValue.smtValue, ArithValue.eqBool, ArithValue.kind,
      native_zeq, native_qeq] at hKind ⊢

private theorem abs_gt_factor_product
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    eo_interprets M (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) true ->
    ∃ vt vu : ArithValue,
      MultListProduct M (multSingleton t) (some vt) ∧
      MultListProduct M (multSingleton u) (some vu) ∧
      ArithProduct.Greater (some vt) (some vu) := by
  intro hTrue
  have hBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue
  rcases gt_abs_operands_smt_arith_of_bool t u hBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM t hInt.1 with ⟨nt, htEval⟩
    rcases smt_eval_int_of_type M hM u hInt.2 with ⟨nu, huEval⟩
    let vt : ArithValue := .int nt
    let vu : ArithValue := .int nu
    have htAbs := model_eval_abs_arith M t vt htEval
    have huAbs := model_eval_abs_arith M u vu huEval
    have hLt := bool_of_true_eval hTrue
      (eval_gt_abs_values M t u vt vu rfl htAbs huAbs)
    exact ⟨vt, vu, MultListProduct.singleton M t vt hInt.1 htEval,
      MultListProduct.singleton M u vu hInt.2 huEval,
      ⟨rfl, (ArithValue.ltBool_abs_true_iff_same_kind (a := vu) (b := vt) rfl).mp hLt⟩⟩
  · rcases smt_eval_real_of_type M hM t hReal.1 with ⟨qt, htEval⟩
    rcases smt_eval_real_of_type M hM u hReal.2 with ⟨qu, huEval⟩
    let vt : ArithValue := .real qt
    let vu : ArithValue := .real qu
    have htAbs := model_eval_abs_arith M t vt htEval
    have huAbs := model_eval_abs_arith M u vu huEval
    have hLt := bool_of_true_eval hTrue
      (eval_gt_abs_values M t u vt vu rfl htAbs huAbs)
    exact ⟨vt, vu, MultListProduct.singleton M t vt hReal.1 htEval,
      MultListProduct.singleton M u vu hReal.2 huEval,
      ⟨rfl, (ArithValue.ltBool_abs_true_iff_same_kind (a := vu) (b := vt) rfl).mp hLt⟩⟩

private theorem abs_eq_factor_product
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    eo_interprets M (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) true ->
    ∃ vt vu : ArithValue,
      __smtx_typeof (__eo_to_smt t) = vt.smtType ∧
      __smtx_model_eval M (__eo_to_smt t) = vt.smtValue ∧
      MultListProduct M (multSingleton t) (some vt) ∧
      MultListProduct M (multSingleton u) (some vu) ∧
      ArithProduct.EqualMagnitude (some vt) (some vu) := by
  intro hTrue
  have hBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue
  rcases eq_abs_operands_smt_arith_of_bool t u hBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM t hInt.1 with ⟨nt, htEval⟩
    rcases smt_eval_int_of_type M hM u hInt.2 with ⟨nu, huEval⟩
    let vt : ArithValue := .int nt
    let vu : ArithValue := .int nu
    have htAbs := model_eval_abs_arith M t vt htEval
    have huAbs := model_eval_abs_arith M u vu huEval
    have hEq := bool_of_true_eval hTrue
      (eval_eq_abs_values M t u vt vu rfl htAbs huAbs)
    exact ⟨vt, vu, hInt.1, htEval,
      MultListProduct.singleton M t vt hInt.1 htEval,
      MultListProduct.singleton M u vu hInt.2 huEval,
      ⟨rfl, (ArithValue.eqBool_abs_true_iff_same_kind (a := vt) (b := vu) rfl).mp hEq⟩⟩
  · rcases smt_eval_real_of_type M hM t hReal.1 with ⟨qt, htEval⟩
    rcases smt_eval_real_of_type M hM u hReal.2 with ⟨qu, huEval⟩
    let vt : ArithValue := .real qt
    let vu : ArithValue := .real qu
    have htAbs := model_eval_abs_arith M t vt htEval
    have huAbs := model_eval_abs_arith M u vu huEval
    have hEq := bool_of_true_eval hTrue
      (eval_eq_abs_values M t u vt vu rfl htAbs huAbs)
    exact ⟨vt, vu, hReal.1, htEval,
      MultListProduct.singleton M t vt hReal.1 htEval,
      MultListProduct.singleton M u vu hReal.2 huEval,
      ⟨rfl, (ArithValue.eqBool_abs_true_iff_same_kind (a := vt) (b := vu) rfl).mp hEq⟩⟩

private theorem eval_zero_of_to_q_zero_and_smt_arith
    (M : SmtModel) (z : Term) (v : ArithValue)
    (hToQ : __eo_to_q z = Term.Rational (native_mk_rational 0 1))
    (hTy : __smtx_typeof (__eo_to_smt z) = v.smtType) :
    __smtx_model_eval M (__eo_to_smt z) = (ArithValue.zero v.kind).smtValue := by
  cases v with
  | int n =>
      simpa [ArithValue.zero, ArithValue.kind, ArithValue.smtValue] using
        eval_zero_of_to_q_zero_and_smt_int M z hToQ hTy
  | real q =>
      cases z <;> simp [__eo_to_q] at hToQ
      case Rational r =>
        subst r
        rw [eo_to_smt_rational_eq, __smtx_model_eval.eq_3]
        simp [ArithValue.zero, ArithValue.kind, ArithValue.smtValue,
          native_mk_rational]

private theorem eq_rhs_smt_type_of_bool_left_arith (t z : Term) (v : ArithValue)
    (hTyT : __smtx_typeof (__eo_to_smt t) = v.smtType)
    (hBool : RuleProofs.eo_has_bool_type (relTerm (Term.UOp UserOp.eq) t z)) :
    __smtx_typeof (__eo_to_smt z) = v.smtType := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t z
      (by simpa [relTerm] using hBool) with ⟨hSame, _⟩
  rw [← hSame, hTyT]

private theorem eval_eq_value_zero (M : SmtModel) (t z : Term) (v : ArithValue)
    (htEval : __smtx_model_eval M (__eo_to_smt t) = v.smtValue)
    (hzEval : __smtx_model_eval M (__eo_to_smt z) = (ArithValue.zero v.kind).smtValue) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.eq) t z)) =
      SmtValue.Boolean (ArithValue.eqBool v (ArithValue.zero v.kind)) := by
  rw [show __eo_to_smt (relTerm (Term.UOp UserOp.eq) t z) =
      SmtTerm.eq (__eo_to_smt t) (__eo_to_smt z) by rfl]
  rw [smtx_eval_eq_term_eq, htEval, hzEval]
  cases v <;> simp [__smtx_model_eval_eq, native_veq, ArithValue.smtValue,
    ArithValue.eqBool, ArithValue.zero, ArithValue.kind]

private theorem abs_factor_nonzero_product
    (M : SmtModel) (t z : Term) (v : ArithValue)
    (hTyT : __smtx_typeof (__eo_to_smt t) = v.smtType)
    (htEval : __smtx_model_eval M (__eo_to_smt t) = v.smtValue)
    (hToQ : __eo_to_q z = Term.Rational (native_mk_rational 0 1)) :
    eo_interprets M (Term.Apply (Term.UOp UserOp.not)
      (relTerm (Term.UOp UserOp.eq) t z)) true ->
    ArithProduct.Positive (some v) := by
  intro hNotTrue
  have hEqFalse := RuleProofs.eo_interprets_not_true_implies_false M
    (relTerm (Term.UOp UserOp.eq) t z) hNotTrue
  have hNotBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hNotTrue
  have hEqBool := RuleProofs.eo_has_bool_type_not_arg
    (relTerm (Term.UOp UserOp.eq) t z) (by simpa [relTerm] using hNotBool)
  have hTyZ := eq_rhs_smt_type_of_bool_left_arith t z v hTyT hEqBool
  have hzEval := eval_zero_of_to_q_zero_and_smt_arith M z v hToQ hTyZ
  have hEqFalseBool := bool_of_false_eval hEqFalse
    (eval_eq_value_zero M t z v htEval hzEval)
  exact ArithValue.magnitude_pos_of_eqBool_zero_false hEqFalseBool

-/

private inductive MultListFactors (M : SmtModel) :
    Term -> ArithKind -> List ArithValue -> Prop
  | nilInt : MultListFactors M (Term.Numeral 1) .int []
  | nilReal :
      MultListFactors M (Term.Rational (native_mk_rational 1 1)) .real []
  | cons {x xs : Term} {k : ArithKind} {vx : ArithValue}
      {vxs : List ArithValue} :
      __smtx_typeof (__eo_to_smt x) = vx.smtType ->
      __smtx_model_eval M (__eo_to_smt x) = vx.smtValue ->
      MultListFactors M xs k vxs ->
      MultListFactors M (Term.Apply (Term.Apply multOp x) xs) k (vx :: vxs)

private theorem MultListFactors.ne_stuck
    {M : SmtModel} {xs : Term} {k : ArithKind} {vs : List ArithValue}
    (h : MultListFactors M xs k vs) : xs ≠ Term.Stuck := by
  cases h <;> simp

private theorem MultListFactors.is_list
    {M : SmtModel} {xs : Term} {k : ArithKind} {vs : List ArithValue}
    (h : MultListFactors M xs k vs) :
    __eo_is_list multOp xs = Term.Boolean true := by
  induction h with
  | nilInt => native_decide
  | nilReal => native_decide
  | cons _ _ _ ih =>
      unfold __eo_is_list __eo_is_ok
      have hne := get_nil_ne_of_is_list_true _ _ ih
      simp [__eo_get_nil_rec, __eo_requires, hne, native_ite, native_teq,
        native_not, SmtEval.native_not, multOp]

private theorem MultListFactors.concat_rec
    {M : SmtModel} {a b : Term} {ka kb : ArithKind}
    {va vb : List ArithValue}
    (ha : MultListFactors M a ka va) (hb : MultListFactors M b kb vb) :
    MultListFactors M (__eo_list_concat_rec a b) kb (va ++ vb) := by
  induction ha with
  | nilInt =>
      rw [list_concat_rec_nil_of_ne_stuck (MultListFactors.ne_stuck hb)]
      simpa using hb
  | nilReal =>
      rw [list_concat_rec_real_nil_of_ne_stuck (MultListFactors.ne_stuck hb)]
      simpa using hb
  | cons hxTy hxEval _ ih =>
      have hTailNe := MultListFactors.ne_stuck ih
      rw [list_concat_rec_cons_of_ne_stuck (MultListFactors.ne_stuck hb)]
      simpa [__eo_mk_apply, hTailNe, multOp] using
        (MultListFactors.cons hxTy hxEval ih)

private theorem MultListFactors.concat
    {M : SmtModel} {a b : Term} {ka kb : ArithKind}
    {va vb : List ArithValue}
    (ha : MultListFactors M a ka va) (hb : MultListFactors M b kb vb) :
    MultListFactors M (__eo_list_concat multOp a b) kb (va ++ vb) := by
  have haList := MultListFactors.is_list ha
  have hbList := MultListFactors.is_list hb
  simpa [__eo_list_concat, haList, hbList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not, multOp] using
    MultListFactors.concat_rec ha hb

private theorem MultListFactors.singleton
    (M : SmtModel) (t : Term) (v : ArithValue)
    (hTy : __smtx_typeof (__eo_to_smt t) = v.smtType)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = v.smtValue) :
    MultListFactors M (multSingleton t) v.kind [v] := by
  cases v with
  | int n =>
      have hEoTy := eo_type_int_of_smt_type_int t hTy
      have hCons := MultListFactors.cons hTy hEval
        (MultListFactors.nilInt (M := M))
      simpa [multSingleton, multOp, __eo_nil, __eo_nil_mult, __arith_mk_one,
        hEoTy, __eo_mk_apply, ArithValue.kind] using hCons
  | real q =>
      have hEoTy := eo_type_real_of_smt_type_real t hTy
      have hCons := MultListFactors.cons hTy hEval
        (MultListFactors.nilReal (M := M))
      simpa [multSingleton, multOp, __eo_nil, __eo_nil_mult, __arith_mk_one,
        hEoTy, __eo_mk_apply, ArithValue.kind, native_mk_rational] using hCons

private theorem eo_typeof_plus_eq_int_args (A B : Term) :
    __eo_typeof_plus A B = Term.Int -> A = Term.Int ∧ B = Term.Int := by
  exact RuleProofs.eo_typeof_plus_int_args A B

private theorem eo_typeof_plus_eq_real_args (A B : Term) :
    __eo_typeof_plus A B = Term.Real -> A = Term.Real ∧ B = Term.Real := by
  exact RuleProofs.eo_typeof_plus_real_args A B

private theorem MultListFactors.all_kind_of_eo_type
    {M : SmtModel} {xs : Term} {tailKind targetKind : ArithKind}
    {vs : List ArithValue}
    (h : MultListFactors M xs tailKind vs)
    (hTy : __eo_typeof xs = (ArithValue.one targetKind).eoType) :
    tailKind = targetKind ∧ allFactorKind targetKind vs := by
  induction h with
  | nilInt =>
      cases targetKind with
      | int => exact ⟨rfl, trivial⟩
      | real =>
          change Term.Int = Term.Real at hTy
          contradiction
  | nilReal =>
      cases targetKind with
      | int =>
          change Term.Real = Term.Int at hTy
          contradiction
      | real => exact ⟨rfl, trivial⟩
  | @cons x xs tailKind vx vxs hxTy _ _ ih =>
      change __eo_typeof_plus (__eo_typeof x) (__eo_typeof xs) = _ at hTy
      cases targetKind with
      | int =>
          have hArgs := eo_typeof_plus_eq_int_args _ _ hTy
          have hxMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x
            (by rw [hxTy]; cases vx <;> simp [ArithValue.smtType])
          have hxSmt : __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
            simpa [hArgs.1] using hxMatch
          have hvKind : vx.kind = .int := by
            rw [hxTy] at hxSmt
            cases vx <;> simp [ArithValue.kind, ArithValue.smtType] at hxSmt ⊢
          rcases ih hArgs.2 with ⟨hTail, hAll⟩
          exact ⟨hTail, hvKind, hAll⟩
      | real =>
          have hArgs := eo_typeof_plus_eq_real_args _ _ hTy
          have hxMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x
            (by rw [hxTy]; cases vx <;> simp [ArithValue.smtType])
          have hxSmt : __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
            simpa [hArgs.1] using hxMatch
          have hvKind : vx.kind = .real := by
            rw [hxTy] at hxSmt
            cases vx <;> simp [ArithValue.kind, ArithValue.smtType] at hxSmt ⊢
          rcases ih hArgs.2 with ⟨hTail, hAll⟩
          exact ⟨hTail, hvKind, hAll⟩

private theorem MultListFactors.smt_type_of_all_kind
    {M : SmtModel} {xs : Term} {k : ArithKind} {vs : List ArithValue}
    (h : MultListFactors M xs k vs) (hAll : allFactorKind k vs) :
    __smtx_typeof (__eo_to_smt xs) = (ArithValue.one k).smtType := by
  induction h with
  | nilInt =>
      rw [eo_to_smt_numeral_eq, __smtx_typeof.eq_2]
      rfl
  | nilReal =>
      rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3]
      rfl
  | @cons x xs k vx vxs hxTy _ _ ih =>
      rcases hAll with ⟨hv, hvs⟩
      change __smtx_typeof (SmtTerm.mult _ _) = _
      rw [typeof_mult_eq, hxTy, ih hvs]
      cases k <;> cases vx <;>
        simp [ArithValue.kind, ArithValue.smtType, ArithValue.one,
          __smtx_typeof_arith_overload_op_2] at hv ⊢

private theorem MultListFactors.eval_of_all_kind
    {M : SmtModel} {xs : Term} {k : ArithKind} {vs : List ArithValue}
    (h : MultListFactors M xs k vs) (hAll : allFactorKind k vs) :
    __smtx_model_eval M (__eo_to_smt xs) = (factorProduct k vs).smtValue := by
  induction h with
  | nilInt =>
      rw [eo_to_smt_numeral_eq, __smtx_model_eval.eq_2]
      rfl
  | nilReal =>
      rw [eo_to_smt_rational_eq, __smtx_model_eval.eq_3]
      simp [factorProduct, ArithValue.one, ArithValue.smtValue,
        native_mk_rational_one]
  | @cons x xs k vx vxs _ hxEval _ ih =>
      rcases hAll with ⟨hv, hvs⟩
      change __smtx_model_eval M (SmtTerm.mult _ _) = _
      rw [__smtx_model_eval.eq_16, hxEval, ih hvs]
      simpa [factorProduct] using
        ArithValue.modelEval_mul_of_same_kind
          (hv.trans (factorProduct_kind hvs).symm)

private theorem eo_typeof_abs_nonstuck_arg_arith (A : Term) :
    __eo_typeof_abs A ≠ Term.Stuck ->
    A = Term.Int ∨ A = Term.Real := by
  intro h
  have hA : A ≠ Term.Stuck := by
    intro hStuck
    subst A
    exact h rfl
  have hReq :
      __eo_requires (__is_arith_type A) (Term.Boolean true) A ≠ Term.Stuck := by
    simpa [__eo_typeof_abs, hA] using h
  have hArith : __is_arith_type A = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReq
  exact RuleProofs.is_arith_type_true_cases A hArith

private theorem eo_typeof_lt_bool_abs_args (A B : Term) :
    __eo_typeof_lt (__eo_typeof_abs A) (__eo_typeof_abs B) = Term.Bool ->
    (A = Term.Int ∧ B = Term.Int) ∨ (A = Term.Real ∧ B = Term.Real) := by
  intro h
  have hANe : __eo_typeof_abs A ≠ Term.Stuck := by
    intro ha
    rw [ha] at h
    simp [__eo_typeof_lt] at h
  have hBNe : __eo_typeof_abs B ≠ Term.Stuck := by
    intro hb
    rw [hb] at h
    cases __eo_typeof_abs A <;> simp [__eo_typeof_lt] at h
  rcases eo_typeof_abs_nonstuck_arg_arith A hANe with rfl | rfl <;>
    rcases eo_typeof_abs_nonstuck_arg_arith B hBNe with rfl | rfl <;>
      simp [__eo_typeof_abs, __eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq, native_not,
        SmtEval.native_not] at h ⊢

private theorem eo_abs_rel_args_of_typeof_bool (r a b : Term)
    (hr : r = Term.UOp UserOp.gt ∨ r = Term.UOp UserOp.eq)
    (hTy : __eo_typeof (relTerm r (absTerm a) (absTerm b)) = Term.Bool) :
    (__eo_typeof a = Term.Int ∧ __eo_typeof b = Term.Int) ∨
      (__eo_typeof a = Term.Real ∧ __eo_typeof b = Term.Real) := by
  rcases hr with rfl | rfl
  · exact eo_typeof_lt_bool_abs_args (__eo_typeof a) (__eo_typeof b)
      (by simpa [relTerm, absTerm, __eo_typeof, __eo_typeof_abs, __eo_typeof_lt] using hTy)
  · have hEq : __eo_typeof_abs (__eo_typeof a) =
        __eo_typeof_abs (__eo_typeof b) :=
      RuleProofs.eo_typeof_eq_bool_operands_eq _ _
        (by simpa [relTerm, absTerm, __eo_typeof, __eo_typeof_abs, __eo_typeof_eq] using hTy)
    have hANe : __eo_typeof_abs (__eo_typeof a) ≠ Term.Stuck :=
      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
        (by simpa [relTerm, absTerm, __eo_typeof, __eo_typeof_abs, __eo_typeof_eq] using hTy)).1
    have hBNe : __eo_typeof_abs (__eo_typeof b) ≠ Term.Stuck :=
      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
        (by simpa [relTerm, absTerm, __eo_typeof, __eo_typeof_abs, __eo_typeof_eq] using hTy)).2
    rcases eo_typeof_abs_nonstuck_arg_arith (__eo_typeof a) hANe with ha | ha <;>
      rcases eo_typeof_abs_nonstuck_arg_arith (__eo_typeof b) hBNe with hb | hb
    · exact Or.inl ⟨ha, hb⟩
    · rw [ha, hb] at hEq
      simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
        native_teq, native_not, SmtEval.native_not] at hEq
    · rw [ha, hb] at hEq
      simp [__eo_typeof_abs, __eo_requires, __is_arith_type, native_ite,
        native_teq, native_not, SmtEval.native_not] at hEq
    · exact Or.inr ⟨ha, hb⟩

private theorem model_eval_abs_arith
    (M : SmtModel) (x : Term) (v : ArithValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = v.smtValue) :
    __smtx_model_eval M (__eo_to_smt (absTerm x)) = v.abs.smtValue := by
  rw [show __eo_to_smt (absTerm x) = SmtTerm.abs (__eo_to_smt x) by rfl]
  rw [__smtx_model_eval.eq_24, hx]
  cases v <;> simp [__smtx_model_eval_abs, ArithValue.abs,
    ArithValue.smtValue]

private theorem smt_type_of_abs_eq_int (t : Term)
    (h : __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl,
    typeof_abs_eq] at h
  cases ht : __smtx_typeof (__eo_to_smt t) <;>
    simp [__smtx_typeof_arith_overload_op_1, ht] at h ⊢

private theorem smt_type_of_abs_eq_real (t : Term)
    (h : __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
  rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl,
    typeof_abs_eq] at h
  cases ht : __smtx_typeof (__eo_to_smt t) <;>
    simp [__smtx_typeof_arith_overload_op_1, ht] at h ⊢

private theorem gt_abs_operands_smt_arith_of_bool (t u : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u))) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt t) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Real) := by
  rcases rel_operands_arith_type_of_gt_has_bool_type (absTerm t) (absTerm u)
      (by simpa [relTerm, absTerm] using hBool) with hInt | hReal
  · exact Or.inl ⟨smt_type_of_abs_eq_int t hInt.1,
      smt_type_of_abs_eq_int u hInt.2⟩
  · exact Or.inr ⟨smt_type_of_abs_eq_real t hReal.1,
      smt_type_of_abs_eq_real u hReal.2⟩

private theorem eq_abs_operands_smt_arith_of_bool (t u : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u))) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt t) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Real) := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (absTerm t) (absTerm u) (by simpa [relTerm, absTerm] using hBool)
    with ⟨hSame, hNN⟩
  have htArith :
      __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Real := by
    rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl,
      typeof_abs_eq] at hNN ⊢
    cases ht : __smtx_typeof (__eo_to_smt t) <;>
      simp [__smtx_typeof_arith_overload_op_1, ht] at hNN ⊢
  rcases htArith with htInt | htReal
  · have huInt : __smtx_typeof (__eo_to_smt (absTerm u)) = SmtType.Int := by
      rw [← hSame, htInt]
    exact Or.inl ⟨smt_type_of_abs_eq_int t htInt,
      smt_type_of_abs_eq_int u huInt⟩
  · have huReal : __smtx_typeof (__eo_to_smt (absTerm u)) = SmtType.Real := by
      rw [← hSame, htReal]
    exact Or.inr ⟨smt_type_of_abs_eq_real t htReal,
      smt_type_of_abs_eq_real u huReal⟩

private theorem eval_gt_abs_values (M : SmtModel) (t u : Term)
    (vt vu : ArithValue)
    (hKind : vt.kind = vu.kind)
    (ht : __smtx_model_eval M (__eo_to_smt (absTerm t)) = vt.abs.smtValue)
    (hu : __smtx_model_eval M (__eo_to_smt (absTerm u)) = vu.abs.smtValue) :
    __smtx_model_eval M
        (__eo_to_smt (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u))) =
      SmtValue.Boolean (ArithValue.ltBool vu.abs vt.abs) := by
  rw [show __eo_to_smt
      (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) =
      SmtTerm.gt (__eo_to_smt (absTerm t)) (__eo_to_smt (absTerm u)) by rfl]
  rw [__smtx_model_eval.eq_19, ht, hu]
  cases vt <;> cases vu <;>
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, ArithValue.abs,
      ArithValue.smtValue, ArithValue.ltBool, ArithValue.kind] at hKind ⊢

private theorem eval_eq_abs_values (M : SmtModel) (t u : Term)
    (vt vu : ArithValue)
    (hKind : vt.kind = vu.kind)
    (ht : __smtx_model_eval M (__eo_to_smt (absTerm t)) = vt.abs.smtValue)
    (hu : __smtx_model_eval M (__eo_to_smt (absTerm u)) = vu.abs.smtValue) :
    __smtx_model_eval M
        (__eo_to_smt (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u))) =
      SmtValue.Boolean (ArithValue.eqBool vt.abs vu.abs) := by
  rw [show __eo_to_smt
      (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) =
      SmtTerm.eq (__eo_to_smt (absTerm t)) (__eo_to_smt (absTerm u)) by rfl]
  rw [smtx_eval_eq_term_eq, ht, hu]
  cases vt <;> cases vu <;>
    simp [__smtx_model_eval_eq, native_veq, ArithValue.abs,
      ArithValue.smtValue, ArithValue.eqBool, ArithValue.kind,
      native_zeq, native_qeq] at hKind ⊢

private theorem abs_gt_factor_factors
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    eo_interprets M (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) true ->
    ∃ vt vu : ArithValue,
      MultListFactors M (multSingleton t) vt.kind [vt] ∧
      MultListFactors M (multSingleton u) vu.kind [vu] ∧
      factorMagnitude [vu] < factorMagnitude [vt] := by
  intro hTrue
  have hBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue
  rcases gt_abs_operands_smt_arith_of_bool t u hBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM t hInt.1 with ⟨nt, htEval⟩
    rcases smt_eval_int_of_type M hM u hInt.2 with ⟨nu, huEval⟩
    let vt : ArithValue := .int nt
    let vu : ArithValue := .int nu
    have htAbs := model_eval_abs_arith M t vt htEval
    have huAbs := model_eval_abs_arith M u vu huEval
    have hLt := bool_of_true_eval hTrue
      (eval_gt_abs_values M t u vt vu rfl htAbs huAbs)
    have hMag := (ArithValue.ltBool_abs_true_iff_same_kind
      (a := vu) (b := vt) rfl).mp hLt
    exact ⟨vt, vu, MultListFactors.singleton M t vt hInt.1 htEval,
      MultListFactors.singleton M u vu hInt.2 huEval, by
        simpa [factorMagnitude] using hMag⟩
  · rcases smt_eval_real_of_type M hM t hReal.1 with ⟨qt, htEval⟩
    rcases smt_eval_real_of_type M hM u hReal.2 with ⟨qu, huEval⟩
    let vt : ArithValue := .real qt
    let vu : ArithValue := .real qu
    have htAbs := model_eval_abs_arith M t vt htEval
    have huAbs := model_eval_abs_arith M u vu huEval
    have hLt := bool_of_true_eval hTrue
      (eval_gt_abs_values M t u vt vu rfl htAbs huAbs)
    have hMag := (ArithValue.ltBool_abs_true_iff_same_kind
      (a := vu) (b := vt) rfl).mp hLt
    exact ⟨vt, vu, MultListFactors.singleton M t vt hReal.1 htEval,
      MultListFactors.singleton M u vu hReal.2 huEval, by
        simpa [factorMagnitude] using hMag⟩

private theorem abs_eq_factor_factors
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    eo_interprets M (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) true ->
    ∃ vt vu : ArithValue,
      __smtx_typeof (__eo_to_smt t) = vt.smtType ∧
      __smtx_model_eval M (__eo_to_smt t) = vt.smtValue ∧
      MultListFactors M (multSingleton t) vt.kind [vt] ∧
      MultListFactors M (multSingleton u) vu.kind [vu] ∧
      factorMagnitude [vt] = factorMagnitude [vu] := by
  intro hTrue
  have hBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue
  rcases eq_abs_operands_smt_arith_of_bool t u hBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM t hInt.1 with ⟨nt, htEval⟩
    rcases smt_eval_int_of_type M hM u hInt.2 with ⟨nu, huEval⟩
    let vt : ArithValue := .int nt
    let vu : ArithValue := .int nu
    have htAbs := model_eval_abs_arith M t vt htEval
    have huAbs := model_eval_abs_arith M u vu huEval
    have hEq := bool_of_true_eval hTrue
      (eval_eq_abs_values M t u vt vu rfl htAbs huAbs)
    have hMag := (ArithValue.eqBool_abs_true_iff_same_kind
      (a := vt) (b := vu) rfl).mp hEq
    exact ⟨vt, vu, hInt.1, htEval,
      MultListFactors.singleton M t vt hInt.1 htEval,
      MultListFactors.singleton M u vu hInt.2 huEval, by
        simpa [factorMagnitude] using hMag⟩
  · rcases smt_eval_real_of_type M hM t hReal.1 with ⟨qt, htEval⟩
    rcases smt_eval_real_of_type M hM u hReal.2 with ⟨qu, huEval⟩
    let vt : ArithValue := .real qt
    let vu : ArithValue := .real qu
    have htAbs := model_eval_abs_arith M t vt htEval
    have huAbs := model_eval_abs_arith M u vu huEval
    have hEq := bool_of_true_eval hTrue
      (eval_eq_abs_values M t u vt vu rfl htAbs huAbs)
    have hMag := (ArithValue.eqBool_abs_true_iff_same_kind
      (a := vt) (b := vu) rfl).mp hEq
    exact ⟨vt, vu, hReal.1, htEval,
      MultListFactors.singleton M t vt hReal.1 htEval,
      MultListFactors.singleton M u vu hReal.2 huEval, by
        simpa [factorMagnitude] using hMag⟩

private theorem numeral_zero_of_to_real_zero {n : native_Int} :
    native_to_real n = native_mk_rational 0 1 -> n = 0 := by
  intro h
  have h' : ((n : Rat) / (1 : Rat)) = ((0 : Rat) / (1 : Rat)) := by
    simpa [native_to_real, native_mk_rational] using h
  rw [rat_div_one_intCast n, rat_zero_div_one] at h'
  exact Rat.intCast_inj.mp h'

private theorem eval_zero_of_to_q_zero_and_smt_arith
    (M : SmtModel) (z : Term) (v : ArithValue)
    (hToQ : __eo_to_q z = Term.Rational (native_mk_rational 0 1))
    (hTy : __smtx_typeof (__eo_to_smt z) = v.smtType) :
    __smtx_model_eval M (__eo_to_smt z) = (ArithValue.zero v.kind).smtValue := by
  cases v with
  | int n =>
      cases z <;> simp [__eo_to_q] at hToQ
      case Numeral m =>
        have hm : m = 0 := numeral_zero_of_to_real_zero hToQ
        subst m
        rw [eo_to_smt_numeral_eq, __smtx_model_eval.eq_2]
        simp [ArithValue.zero, ArithValue.kind, ArithValue.smtValue]
      case Rational q =>
        subst q
        rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3] at hTy
        simp [ArithValue.smtType] at hTy
  | real q =>
      cases z <;> simp [__eo_to_q] at hToQ
      case Numeral n =>
        rw [eo_to_smt_numeral_eq, __smtx_typeof.eq_2] at hTy
        simp [ArithValue.smtType] at hTy
      case Rational r =>
        subst r
        rw [eo_to_smt_rational_eq, __smtx_model_eval.eq_3]
        have hz : native_mk_rational 0 1 = (0 : native_Rat) := by native_decide
        simp [ArithValue.zero, ArithValue.kind, ArithValue.smtValue, hz]

private theorem eq_rhs_smt_type_of_bool_left_arith (t z : Term) (v : ArithValue)
    (hTyT : __smtx_typeof (__eo_to_smt t) = v.smtType)
    (hBool : RuleProofs.eo_has_bool_type (relTerm (Term.UOp UserOp.eq) t z)) :
    __smtx_typeof (__eo_to_smt z) = v.smtType := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t z
      (by simpa [relTerm] using hBool) with ⟨hSame, _⟩
  rw [← hSame, hTyT]

private theorem eval_eq_value_zero (M : SmtModel) (t z : Term) (v : ArithValue)
    (htEval : __smtx_model_eval M (__eo_to_smt t) = v.smtValue)
    (hzEval : __smtx_model_eval M (__eo_to_smt z) = (ArithValue.zero v.kind).smtValue) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.eq) t z)) =
      SmtValue.Boolean (ArithValue.eqBool v (ArithValue.zero v.kind)) := by
  rw [show __eo_to_smt (relTerm (Term.UOp UserOp.eq) t z) =
      SmtTerm.eq (__eo_to_smt t) (__eo_to_smt z) by rfl]
  rw [smtx_eval_eq_term_eq, htEval, hzEval]
  cases v <;> simp [__smtx_model_eval_eq, native_veq, ArithValue.smtValue,
    ArithValue.eqBool, ArithValue.zero, ArithValue.kind,
    native_zeq, native_qeq]

private theorem abs_factor_nonzero_factors
    (M : SmtModel) (t z : Term) (v : ArithValue)
    (hTyT : __smtx_typeof (__eo_to_smt t) = v.smtType)
    (htEval : __smtx_model_eval M (__eo_to_smt t) = v.smtValue)
    (hToQ : __eo_to_q z = Term.Rational (native_mk_rational 0 1)) :
    eo_interprets M (Term.Apply (Term.UOp UserOp.not)
      (relTerm (Term.UOp UserOp.eq) t z)) true ->
    0 < factorMagnitude [v] := by
  intro hNotTrue
  have hEqFalse := RuleProofs.eo_interprets_not_true_implies_false M
    (relTerm (Term.UOp UserOp.eq) t z) hNotTrue
  have hNotBool := RuleProofs.eo_has_bool_type_of_interprets_true M _ hNotTrue
  have hEqBool := RuleProofs.eo_has_bool_type_not_arg
    (relTerm (Term.UOp UserOp.eq) t z) (by simpa [relTerm] using hNotBool)
  have hTyZ := eq_rhs_smt_type_of_bool_left_arith t z v hTyT hEqBool
  have hzEval := eval_zero_of_to_q_zero_and_smt_arith M z v hToQ hTyZ
  have hEqFalseBool := bool_of_false_eval hEqFalse
    (eval_eq_value_zero M t z v htEval hzEval)
  have hPos := ArithValue.magnitude_pos_of_eqBool_zero_false hEqFalseBool
  simpa [factorMagnitude] using hPos

private inductive AbsCmpAcc (M : SmtModel) : Term -> Prop
  | gt (a b : Term) (ka kb : ArithKind) (va vb : List ArithValue) :
      MultListFactors M a ka va ->
      MultListFactors M b kb vb ->
      factorMagnitude vb < factorMagnitude va ->
      AbsCmpAcc M (relTerm (Term.UOp UserOp.gt) a b)
  | eq (a b : Term) (ka kb : ArithKind) (va vb : List ArithValue) :
      MultListFactors M a ka va ->
      MultListFactors M b kb vb ->
      factorMagnitude va = factorMagnitude vb ->
      AbsCmpAcc M (relTerm (Term.UOp UserOp.eq) a b)

/- Superseded integer-only final accumulator proof.
private theorem AbsCmpAcc.final_true
    {M : SmtModel} {rel : Term} :
    AbsCmpAcc M rel ->
    eo_interprets M
      (match rel with
       | Term.Apply (Term.Apply r a) b =>
           relTerm r (absTerm a) (absTerm b)
       | _ => Term.Stuck) true := by
  intro hAcc
  cases hAcc with
  | gt a b ka kb va vb ha hb hLt =>
      have hAbsA := model_eval_abs_int M a na (MultListEval.eval ha)
      have hAbsB := model_eval_abs_int M b nb (MultListEval.eval hb)
      have hBool : RuleProofs.eo_has_bool_type
          (relTerm (Term.UOp UserOp.gt) (absTerm a) (absTerm b)) := by
        have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Int := by
          rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl]
          rw [typeof_abs_eq, MultListEval.type_int ha]
          simp [native_Teq, native_ite]
        have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Int := by
          rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl]
          rw [typeof_abs_eq, MultListEval.type_int hb]
          simp [native_Teq, native_ite]
        exact rel_bool_of_pair_type (Term.UOp UserOp.gt) (absTerm a) (absTerm b)
          (by simp [arithRelOp]) (Or.inl ⟨haAbsTy, hbAbsTy⟩)
      simpa [relTerm] using
        RuleProofs.eo_interprets_of_bool_eval M _ true hBool (by
        rw [show __eo_to_smt
            (relTerm (Term.UOp UserOp.gt) (absTerm a) (absTerm b)) =
            SmtTerm.gt (__eo_to_smt (absTerm a)) (__eo_to_smt (absTerm b)) by rfl]
        rw [__smtx_model_eval.eq_19, hAbsA, hAbsB]
        simp [__smtx_model_eval_gt, __smtx_model_eval_lt,
          (native_zlt_intAbs_true_iff nb na).mpr hLt])
  | eq a b na nb ha hb hEq =>
      have hAbsA := model_eval_abs_int M a na (MultListEval.eval ha)
      have hAbsB := model_eval_abs_int M b nb (MultListEval.eval hb)
      have hIntAbsEq : intAbs na = intAbs nb :=
        intAbs_eq_of_natAbs_eq hEq
      have hBool : RuleProofs.eo_has_bool_type
          (relTerm (Term.UOp UserOp.eq) (absTerm a) (absTerm b)) := by
        have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Int := by
          rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl]
          rw [typeof_abs_eq, MultListEval.type_int ha]
          simp [native_Teq, native_ite]
        have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Int := by
          rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl]
          rw [typeof_abs_eq, MultListEval.type_int hb]
          simp [native_Teq, native_ite]
        exact rel_bool_of_pair_type (Term.UOp UserOp.eq) (absTerm a) (absTerm b)
          (by simp [arithRelOp]) (Or.inl ⟨haAbsTy, hbAbsTy⟩)
      simpa [relTerm] using
        RuleProofs.eo_interprets_of_bool_eval M _ true hBool (by
        rw [show __eo_to_smt
            (relTerm (Term.UOp UserOp.eq) (absTerm a) (absTerm b)) =
            SmtTerm.eq (__eo_to_smt (absTerm a)) (__eo_to_smt (absTerm b)) by rfl]
        rw [smtx_eval_eq_term_eq, hAbsA, hAbsB]
        simp [__smtx_model_eval_eq, native_veq, hIntAbsEq])
-/

private theorem AbsCmpAcc.final_true
    {M : SmtModel} {rel : Term} (hAcc : AbsCmpAcc M rel)
    (hTy : __eo_typeof
      (match rel with
       | Term.Apply (Term.Apply r a) b => relTerm r (absTerm a) (absTerm b)
       | _ => Term.Stuck) = Term.Bool) :
    eo_interprets M
      (match rel with
       | Term.Apply (Term.Apply r a) b => relTerm r (absTerm a) (absTerm b)
       | _ => Term.Stuck) true := by
  cases hAcc with
  | gt a b ka kb va vb ha hb hLt =>
      have hEo := eo_abs_rel_args_of_typeof_bool (Term.UOp UserOp.gt) a b
        (Or.inl rfl) (by simpa [relTerm] using hTy)
      rcases hEo with hInt | hReal
      · rcases MultListFactors.all_kind_of_eo_type (targetKind := .int) ha hInt.1 with
          ⟨rfl, haAll⟩
        rcases MultListFactors.all_kind_of_eo_type (targetKind := .int) hb hInt.2 with
          ⟨rfl, hbAll⟩
        have haEval := MultListFactors.eval_of_all_kind ha haAll
        have hbEval := MultListFactors.eval_of_all_kind hb hbAll
        have haAbs := model_eval_abs_arith M a (factorProduct .int va) haEval
        have hbAbs := model_eval_abs_arith M b (factorProduct .int vb) hbEval
        have hKinds : (factorProduct .int vb).kind =
            (factorProduct .int va).kind :=
          (factorProduct_kind hbAll).trans (factorProduct_kind haAll).symm
        have hMagnitudes : (factorProduct .int vb).magnitude <
            (factorProduct .int va).magnitude := by
          simpa [factorProduct_magnitude hbAll, factorProduct_magnitude haAll]
            using hLt
        have hEval := eval_gt_abs_values M a b
          (factorProduct .int va) (factorProduct .int vb) hKinds.symm haAbs hbAbs
        have hBool : RuleProofs.eo_has_bool_type
            (relTerm (Term.UOp UserOp.gt) (absTerm a) (absTerm b)) := by
          have haSmt := MultListFactors.smt_type_of_all_kind ha haAll
          have hbSmt := MultListFactors.smt_type_of_all_kind hb hbAll
          have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Int := by
            rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl,
              typeof_abs_eq, haSmt]
            simp [ArithValue.one, ArithValue.smtType,
              __smtx_typeof_arith_overload_op_1]
          have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Int := by
            rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl,
              typeof_abs_eq, hbSmt]
            simp [ArithValue.one, ArithValue.smtType,
              __smtx_typeof_arith_overload_op_1]
          exact rel_bool_of_pair_type _ _ _ (by simp [arithRelOp])
            (Or.inl ⟨haAbsTy, hbAbsTy⟩)
        simpa [relTerm] using RuleProofs.eo_interprets_of_bool_eval M _ true hBool (by
          rw [hEval]
          exact congrArg SmtValue.Boolean
            ((ArithValue.ltBool_abs_true_iff_same_kind hKinds).mpr hMagnitudes))
      · rcases MultListFactors.all_kind_of_eo_type (targetKind := .real) ha hReal.1 with
          ⟨rfl, haAll⟩
        rcases MultListFactors.all_kind_of_eo_type (targetKind := .real) hb hReal.2 with
          ⟨rfl, hbAll⟩
        have haEval := MultListFactors.eval_of_all_kind ha haAll
        have hbEval := MultListFactors.eval_of_all_kind hb hbAll
        have haAbs := model_eval_abs_arith M a (factorProduct .real va) haEval
        have hbAbs := model_eval_abs_arith M b (factorProduct .real vb) hbEval
        have hKinds : (factorProduct .real vb).kind =
            (factorProduct .real va).kind :=
          (factorProduct_kind hbAll).trans (factorProduct_kind haAll).symm
        have hMagnitudes : (factorProduct .real vb).magnitude <
            (factorProduct .real va).magnitude := by
          simpa [factorProduct_magnitude hbAll, factorProduct_magnitude haAll]
            using hLt
        have hEval := eval_gt_abs_values M a b
          (factorProduct .real va) (factorProduct .real vb) hKinds.symm haAbs hbAbs
        have hBool : RuleProofs.eo_has_bool_type
            (relTerm (Term.UOp UserOp.gt) (absTerm a) (absTerm b)) := by
          have haSmt := MultListFactors.smt_type_of_all_kind ha haAll
          have hbSmt := MultListFactors.smt_type_of_all_kind hb hbAll
          have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Real := by
            rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl,
              typeof_abs_eq, haSmt]
            simp [ArithValue.one, ArithValue.smtType,
              __smtx_typeof_arith_overload_op_1]
          have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Real := by
            rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl,
              typeof_abs_eq, hbSmt]
            simp [ArithValue.one, ArithValue.smtType,
              __smtx_typeof_arith_overload_op_1]
          exact rel_bool_of_pair_type _ _ _ (by simp [arithRelOp])
            (Or.inr ⟨haAbsTy, hbAbsTy⟩)
        simpa [relTerm] using RuleProofs.eo_interprets_of_bool_eval M _ true hBool (by
          rw [hEval]
          exact congrArg SmtValue.Boolean
            ((ArithValue.ltBool_abs_true_iff_same_kind hKinds).mpr hMagnitudes))
  | eq a b ka kb va vb ha hb hEq =>
      have hEo := eo_abs_rel_args_of_typeof_bool (Term.UOp UserOp.eq) a b
        (Or.inr rfl) (by simpa [relTerm] using hTy)
      rcases hEo with hInt | hReal
      · rcases MultListFactors.all_kind_of_eo_type (targetKind := .int) ha hInt.1 with
          ⟨rfl, haAll⟩
        rcases MultListFactors.all_kind_of_eo_type (targetKind := .int) hb hInt.2 with
          ⟨rfl, hbAll⟩
        have haEval := MultListFactors.eval_of_all_kind ha haAll
        have hbEval := MultListFactors.eval_of_all_kind hb hbAll
        have haAbs := model_eval_abs_arith M a (factorProduct .int va) haEval
        have hbAbs := model_eval_abs_arith M b (factorProduct .int vb) hbEval
        have hKinds := (factorProduct_kind haAll).trans (factorProduct_kind hbAll).symm
        have hMagnitudes : (factorProduct .int va).magnitude =
            (factorProduct .int vb).magnitude := by
          simpa [factorProduct_magnitude haAll, factorProduct_magnitude hbAll]
            using hEq
        have hEval := eval_eq_abs_values M a b
          (factorProduct .int va) (factorProduct .int vb) hKinds haAbs hbAbs
        have hBool : RuleProofs.eo_has_bool_type
            (relTerm (Term.UOp UserOp.eq) (absTerm a) (absTerm b)) := by
          have haSmt := MultListFactors.smt_type_of_all_kind ha haAll
          have hbSmt := MultListFactors.smt_type_of_all_kind hb hbAll
          have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Int := by
            rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl,
              typeof_abs_eq, haSmt]
            simp [ArithValue.one, ArithValue.smtType,
              __smtx_typeof_arith_overload_op_1]
          have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Int := by
            rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl,
              typeof_abs_eq, hbSmt]
            simp [ArithValue.one, ArithValue.smtType,
              __smtx_typeof_arith_overload_op_1]
          exact rel_bool_of_pair_type _ _ _ (by simp [arithRelOp])
            (Or.inl ⟨haAbsTy, hbAbsTy⟩)
        simpa [relTerm] using RuleProofs.eo_interprets_of_bool_eval M _ true hBool (by
          rw [hEval]
          exact congrArg SmtValue.Boolean
            ((ArithValue.eqBool_abs_true_iff_same_kind hKinds).mpr hMagnitudes))
      · rcases MultListFactors.all_kind_of_eo_type (targetKind := .real) ha hReal.1 with
          ⟨rfl, haAll⟩
        rcases MultListFactors.all_kind_of_eo_type (targetKind := .real) hb hReal.2 with
          ⟨rfl, hbAll⟩
        have haEval := MultListFactors.eval_of_all_kind ha haAll
        have hbEval := MultListFactors.eval_of_all_kind hb hbAll
        have haAbs := model_eval_abs_arith M a (factorProduct .real va) haEval
        have hbAbs := model_eval_abs_arith M b (factorProduct .real vb) hbEval
        have hKinds := (factorProduct_kind haAll).trans (factorProduct_kind hbAll).symm
        have hMagnitudes : (factorProduct .real va).magnitude =
            (factorProduct .real vb).magnitude := by
          simpa [factorProduct_magnitude haAll, factorProduct_magnitude hbAll]
            using hEq
        have hEval := eval_eq_abs_values M a b
          (factorProduct .real va) (factorProduct .real vb) hKinds haAbs hbAbs
        have hBool : RuleProofs.eo_has_bool_type
            (relTerm (Term.UOp UserOp.eq) (absTerm a) (absTerm b)) := by
          have haSmt := MultListFactors.smt_type_of_all_kind ha haAll
          have hbSmt := MultListFactors.smt_type_of_all_kind hb hbAll
          have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Real := by
            rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl,
              typeof_abs_eq, haSmt]
            simp [ArithValue.one, ArithValue.smtType,
              __smtx_typeof_arith_overload_op_1]
          have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Real := by
            rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl,
              typeof_abs_eq, hbSmt]
            simp [ArithValue.one, ArithValue.smtType,
              __smtx_typeof_arith_overload_op_1]
          exact rel_bool_of_pair_type _ _ _ (by simp [arithRelOp])
            (Or.inr ⟨haAbsTy, hbAbsTy⟩)
        simpa [relTerm] using RuleProofs.eo_interprets_of_bool_eval M _ true hBool (by
          rw [hEval]
          exact congrArg SmtValue.Boolean
            ((ArithValue.eqBool_abs_true_iff_same_kind hKinds).mpr hMagnitudes))

private theorem mk_rel_eq_relTerm_gt
    {M : SmtModel} {a b : Term} {ka kb : ArithKind}
    {va vb : List ArithValue}
    (ha : MultListFactors M a ka va) (hb : MultListFactors M b kb vb) :
    __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.gt) a) b =
      relTerm (Term.UOp UserOp.gt) a b := by
  simp [__eo_mk_apply, MultListFactors.ne_stuck ha, MultListFactors.ne_stuck hb,
    relTerm]

private theorem mk_rel_eq_relTerm_eq
    {M : SmtModel} {a b : Term} {ka kb : ArithKind}
    {va vb : List ArithValue}
    (ha : MultListFactors M a ka va) (hb : MultListFactors M b kb vb) :
    __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) a) b =
      relTerm (Term.UOp UserOp.eq) a b := by
  simp [__eo_mk_apply, MultListFactors.ne_stuck ha, MultListFactors.ne_stuck hb,
    relTerm]

private inductive AbsCmpTypeAcc (M : SmtModel) : Term -> Prop
  | gt (a b : Term) (ka kb : ArithKind) (va vb : List ArithValue) :
      MultListFactors M a ka va ->
      MultListFactors M b kb vb ->
      AbsCmpTypeAcc M (relTerm (Term.UOp UserOp.gt) a b)
  | eq (a b : Term) (ka kb : ArithKind) (va vb : List ArithValue) :
      MultListFactors M a ka va ->
      MultListFactors M b kb vb ->
      AbsCmpTypeAcc M (relTerm (Term.UOp UserOp.eq) a b)

/- Superseded integer-only type-accumulator finalization.
private theorem AbsCmpTypeAcc.final_bool
    {M : SmtModel} {rel : Term} :
    AbsCmpTypeAcc M rel ->
    RuleProofs.eo_has_bool_type
      (match rel with
       | Term.Apply (Term.Apply r a) b =>
           relTerm r (absTerm a) (absTerm b)
       | _ => Term.Stuck) := by
  intro hAcc
  cases hAcc with
  | gt a b ka kb va vb ha hb =>
      have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Int := by
        rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl]
        rw [typeof_abs_eq, MultListEval.type_int ha]
        simp [native_Teq, native_ite]
      have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Int := by
        rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl]
        rw [typeof_abs_eq, MultListEval.type_int hb]
        simp [native_Teq, native_ite]
      simpa [relTerm] using
        rel_bool_of_pair_type (Term.UOp UserOp.gt) (absTerm a) (absTerm b)
          (by simp [arithRelOp]) (Or.inl ⟨haAbsTy, hbAbsTy⟩)
-/

private theorem factor_lists_abs_rel_has_bool
    {M : SmtModel} (r a b : Term)
    (hr : r = Term.UOp UserOp.gt ∨ r = Term.UOp UserOp.eq)
    {ka kb : ArithKind} {va vb : List ArithValue}
    (ha : MultListFactors M a ka va) (hb : MultListFactors M b kb vb)
    (hTy : __eo_typeof (relTerm r (absTerm a) (absTerm b)) = Term.Bool) :
    RuleProofs.eo_has_bool_type (relTerm r (absTerm a) (absTerm b)) := by
  have hEo := eo_abs_rel_args_of_typeof_bool r a b hr hTy
  rcases hEo with hInt | hReal
  · rcases MultListFactors.all_kind_of_eo_type (targetKind := .int) ha hInt.1 with
      ⟨rfl, haAll⟩
    rcases MultListFactors.all_kind_of_eo_type (targetKind := .int) hb hInt.2 with
      ⟨rfl, hbAll⟩
    have haSmt := MultListFactors.smt_type_of_all_kind ha haAll
    have hbSmt := MultListFactors.smt_type_of_all_kind hb hbAll
    have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Int := by
      rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl,
        typeof_abs_eq, haSmt]
      simp [ArithValue.one, ArithValue.smtType,
        __smtx_typeof_arith_overload_op_1]
    have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Int := by
      rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl,
        typeof_abs_eq, hbSmt]
      simp [ArithValue.one, ArithValue.smtType,
        __smtx_typeof_arith_overload_op_1]
    rcases hr with rfl | rfl
    · exact rel_bool_of_pair_type _ _ _ (by simp [arithRelOp])
        (Or.inl ⟨haAbsTy, hbAbsTy⟩)
    · exact rel_bool_of_pair_type _ _ _ (by simp [arithRelOp])
        (Or.inl ⟨haAbsTy, hbAbsTy⟩)
  · rcases MultListFactors.all_kind_of_eo_type (targetKind := .real) ha hReal.1 with
      ⟨rfl, haAll⟩
    rcases MultListFactors.all_kind_of_eo_type (targetKind := .real) hb hReal.2 with
      ⟨rfl, hbAll⟩
    have haSmt := MultListFactors.smt_type_of_all_kind ha haAll
    have hbSmt := MultListFactors.smt_type_of_all_kind hb hbAll
    have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Real := by
      rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl,
        typeof_abs_eq, haSmt]
      simp [ArithValue.one, ArithValue.smtType,
        __smtx_typeof_arith_overload_op_1]
    have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Real := by
      rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl,
        typeof_abs_eq, hbSmt]
      simp [ArithValue.one, ArithValue.smtType,
        __smtx_typeof_arith_overload_op_1]
    rcases hr with rfl | rfl
    · exact rel_bool_of_pair_type _ _ _ (by simp [arithRelOp])
        (Or.inr ⟨haAbsTy, hbAbsTy⟩)
    · exact rel_bool_of_pair_type _ _ _ (by simp [arithRelOp])
        (Or.inr ⟨haAbsTy, hbAbsTy⟩)

private theorem AbsCmpTypeAcc.final_bool
    {M : SmtModel} {rel : Term} (hAcc : AbsCmpTypeAcc M rel)
    (hTy : __eo_typeof
      (match rel with
       | Term.Apply (Term.Apply r a) b => relTerm r (absTerm a) (absTerm b)
       | _ => Term.Stuck) = Term.Bool) :
    RuleProofs.eo_has_bool_type
      (match rel with
       | Term.Apply (Term.Apply r a) b => relTerm r (absTerm a) (absTerm b)
       | _ => Term.Stuck) := by
  cases hAcc with
  | gt a b ka kb va vb ha hb =>
      exact factor_lists_abs_rel_has_bool _ _ _ (Or.inl rfl) ha hb
        (by simpa [relTerm] using hTy)
  | eq a b ka kb va vb ha hb =>
      exact factor_lists_abs_rel_has_bool _ _ _ (Or.inr rfl) ha hb
        (by simpa [relTerm] using hTy)

private theorem AbsCmpAcc.toTypeAcc
    {M : SmtModel} {rel : Term} : AbsCmpAcc M rel -> AbsCmpTypeAcc M rel := by
  intro h
  cases h with
  | gt a b ka kb va vb ha hb _ => exact AbsCmpTypeAcc.gt a b ka kb va vb ha hb
  | eq a b ka kb va vb ha hb _ => exact AbsCmpTypeAcc.eq a b ka kb va vb ha hb
/- Remainder of superseded integer-only finalization.
  | eq a b na nb ha hb =>
      have haAbsTy : __smtx_typeof (__eo_to_smt (absTerm a)) = SmtType.Int := by
        rw [show __eo_to_smt (absTerm a) = SmtTerm.abs (__eo_to_smt a) by rfl]
        rw [typeof_abs_eq, MultListEval.type_int ha]
        simp [native_Teq, native_ite]
      have hbAbsTy : __smtx_typeof (__eo_to_smt (absTerm b)) = SmtType.Int := by
        rw [show __eo_to_smt (absTerm b) = SmtTerm.abs (__eo_to_smt b) by rfl]
        rw [typeof_abs_eq, MultListEval.type_int hb]
        simp [native_Teq, native_ite]
      simpa [relTerm] using
        rel_bool_of_pair_type (Term.UOp UserOp.eq) (absTerm a) (absTerm b)
          (by simp [arithRelOp]) (Or.inl ⟨haAbsTy, hbAbsTy⟩)
-/

/- Superseded integer-only factor typing.
private theorem abs_gt_factor_type
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) ->
    ∃ nt nu : native_Int,
      MultListEval M (multSingleton t) nt ∧
      MultListEval M (multSingleton u) nu := by
  intro hBool
  have hTy := gt_abs_operands_smt_int_of_bool t u hBool
  rcases smt_eval_int_of_type M hM t hTy.1 with ⟨nt, htEval⟩
  rcases smt_eval_int_of_type M hM u hTy.2 with ⟨nu, huEval⟩
  exact ⟨nt, nu, MultListEval.singleton M t nt hTy.1 htEval,
    MultListEval.singleton M u nu hTy.2 huEval⟩
-/

private theorem abs_gt_factor_type
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) ->
    ∃ vt vu : ArithValue,
      MultListFactors M (multSingleton t) vt.kind [vt] ∧
      MultListFactors M (multSingleton u) vu.kind [vu] := by
  intro hBool
  rcases gt_abs_operands_smt_arith_of_bool t u hBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM t hInt.1 with ⟨nt, htEval⟩
    rcases smt_eval_int_of_type M hM u hInt.2 with ⟨nu, huEval⟩
    exact ⟨.int nt, .int nu,
      MultListFactors.singleton M t (.int nt) hInt.1 htEval,
      MultListFactors.singleton M u (.int nu) hInt.2 huEval⟩
  · rcases smt_eval_real_of_type M hM t hReal.1 with ⟨qt, htEval⟩
    rcases smt_eval_real_of_type M hM u hReal.2 with ⟨qu, huEval⟩
    exact ⟨.real qt, .real qu,
      MultListFactors.singleton M t (.real qt) hReal.1 htEval,
      MultListFactors.singleton M u (.real qu) hReal.2 huEval⟩

private theorem abs_eq_factor_type
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) ->
    ∃ vt vu : ArithValue,
      MultListFactors M (multSingleton t) vt.kind [vt] ∧
      MultListFactors M (multSingleton u) vu.kind [vu] := by
  intro hBool
  rcases eq_abs_operands_smt_arith_of_bool t u hBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM t hInt.1 with ⟨nt, htEval⟩
    rcases smt_eval_int_of_type M hM u hInt.2 with ⟨nu, huEval⟩
    exact ⟨.int nt, .int nu,
      MultListFactors.singleton M t (.int nt) hInt.1 htEval,
      MultListFactors.singleton M u (.int nu) hInt.2 huEval⟩
  · rcases smt_eval_real_of_type M hM t hReal.1 with ⟨qt, htEval⟩
    rcases smt_eval_real_of_type M hM u hReal.2 with ⟨qu, huEval⟩
    exact ⟨.real qt, .real qu,
      MultListFactors.singleton M t (.real qt) hReal.1 htEval,
      MultListFactors.singleton M u (.real qu) hReal.2 huEval⟩

/- Superseded integer-only equality factor typing.
private theorem abs_eq_factor_type
    (M : SmtModel) (hM : model_wf M) (t u : Term) :
    RuleProofs.eo_has_bool_type
      (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) ->
    ∃ nt nu : native_Int,
      MultListEval M (multSingleton t) nt ∧
      MultListEval M (multSingleton u) nu := by
  intro hBool
  have hTy := eq_abs_operands_smt_int_of_bool t u hBool
  rcases smt_eval_int_of_type M hM t hTy.1 with ⟨nt, htEval⟩
  rcases smt_eval_int_of_type M hM u hTy.2 with ⟨nu, huEval⟩
  exact ⟨nt, nu, MultListEval.singleton M t nt hTy.1 htEval,
    MultListEval.singleton M u nu hTy.2 huEval⟩
-/

private theorem l2_abs_comparison_has_bool_type
    (M : SmtModel) (F rel : Term) :
    RuleProofs.eo_has_bool_type F ->
    AbsCmpTypeAcc M rel ->
    __eo_typeof (__eo_l_2___mk_arith_mult_abs_comparison_rec F rel) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (__eo_l_2___mk_arith_mult_abs_comparison_rec F rel) := by
  intro _hFType hAcc hTy
  cases hAcc with
  | gt a b ka kb va vb ha hb =>
      cases F <;> try
        exact False.elim (false_of_typeof_stuck_bool
          (by simpa [__eo_l_2___mk_arith_mult_abs_comparison_rec] using hTy))
      case Boolean b =>
        cases b
        · exact False.elim (false_of_typeof_stuck_bool
            (by simpa [__eo_l_2___mk_arith_mult_abs_comparison_rec] using hTy))
        · simpa [relTerm, __eo_l_2___mk_arith_mult_abs_comparison_rec] using
            (AbsCmpTypeAcc.final_bool (M := M)
              (AbsCmpTypeAcc.gt a b ka kb va vb ha hb)
              (by simpa [relTerm, __eo_l_2___mk_arith_mult_abs_comparison_rec]
                using hTy))
  | eq a b ka kb va vb ha hb =>
      cases F <;> try
        exact False.elim (false_of_typeof_stuck_bool
          (by simpa [__eo_l_2___mk_arith_mult_abs_comparison_rec] using hTy))
      case Boolean b =>
        cases b
        · exact False.elim (false_of_typeof_stuck_bool
            (by simpa [__eo_l_2___mk_arith_mult_abs_comparison_rec] using hTy))
        · simpa [relTerm, __eo_l_2___mk_arith_mult_abs_comparison_rec] using
            (AbsCmpTypeAcc.final_bool (M := M)
              (AbsCmpTypeAcc.eq a b ka kb va vb ha hb)
              (by simpa [relTerm, __eo_l_2___mk_arith_mult_abs_comparison_rec]
                using hTy))

private theorem arith_mult_abs_comparison_rec_has_bool_type
    (M : SmtModel) (hM : model_wf M)
    (F rel : Term) :
    RuleProofs.eo_has_bool_type F ->
    AbsCmpTypeAcc M rel ->
    __eo_typeof (__mk_arith_mult_abs_comparison_rec F rel) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__mk_arith_mult_abs_comparison_rec F rel) := by
  let motive1 := fun F rel =>
    RuleProofs.eo_has_bool_type F ->
    AbsCmpTypeAcc M rel ->
    __eo_typeof (__eo_l_1___mk_arith_mult_abs_comparison_rec F rel) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_l_1___mk_arith_mult_abs_comparison_rec F rel)
  let motive2 := fun F rel =>
    RuleProofs.eo_has_bool_type F ->
    AbsCmpTypeAcc M rel ->
    __eo_typeof (__mk_arith_mult_abs_comparison_rec F rel) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__mk_arith_mult_abs_comparison_rec F rel)
  exact __mk_arith_mult_abs_comparison_rec.induct motive1 motive2
    (by
      intro x _hFType _hAcc hTy
      exact False.elim (false_of_typeof_stuck_bool
        (by simpa [__eo_l_1___mk_arith_mult_abs_comparison_rec] using hTy)))
    (by
      intro x hx _hFType _hAcc hTy
      exact False.elim (false_of_typeof_stuck_bool
        (by
          rw [__eo_l_1___mk_arith_mult_abs_comparison_rec.eq_2 x hx] at hTy
          simpa using hTy)))
    (by
      intro t u tv z B a b ih hFType hAcc hTy
      rw [__eo_l_1___mk_arith_mult_abs_comparison_rec.eq_3] at hTy ⊢
      by_cases hSame : t = tv
      · subst tv
        by_cases hZero :
            __eo_to_q z = Term.Rational (native_mk_rational 0 1)
        · simp [__eo_ite, __eo_requires, hZero, native_teq,
            native_ite, native_not, SmtEval.native_not] at hTy ⊢
          have hLeftType :
              RuleProofs.eo_has_bool_type
                (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                  (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)))
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                    (Term.Apply (Term.UOp UserOp.not)
                      (relTerm (Term.UOp UserOp.eq) t z)))
                    (Term.Boolean true))) := by
            simpa [relTerm, absTerm] using
              RuleProofs.eo_has_bool_type_and_left _ _ hFType
          have hBType : RuleProofs.eo_has_bool_type B := by
            simpa [relTerm, absTerm] using
              RuleProofs.eo_has_bool_type_and_right _ _ hFType
          have hEqAbsType :
              RuleProofs.eo_has_bool_type
                (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) := by
            simpa [relTerm, absTerm] using
              RuleProofs.eo_has_bool_type_and_left _ _ hLeftType
          have htArith := eq_abs_operands_smt_arith_of_bool t u hEqAbsType
          have htNe : t ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_smt_translation t
              (by
                unfold RuleProofs.eo_has_smt_translation
                rcases htArith with hInt | hReal
                · rw [hInt.1]; simp
                · rw [hReal.1]; simp)
          -- state this in the folded shape: v4.33 keeps `__eo_eq` folded in the
          -- `ite` guard, and the unfolded `match` form is a distinct (dependent)
          -- matcher that no longer converts.
          have hEqSelfRaw : __eo_eq t t = Term.Boolean true :=
            RuleProofs.eo_eq_self_of_ne_stuck t htNe
          rcases abs_eq_factor_type M hM t u hEqAbsType with
            ⟨nt, nu, htList, huList⟩
          cases hAcc with
          | gt _ _ ka kb va vb ha hb =>
              have hLeft := MultListFactors.concat ha htList
              have hRight := MultListFactors.concat hb huList
              have hRelEq :
                  __eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.gt)
                      (__eo_list_concat multOp a (multSingleton t)))
                    (__eo_list_concat multOp b (multSingleton u)) =
                    relTerm (Term.UOp UserOp.gt)
                      (__eo_list_concat multOp a (multSingleton t))
                      (__eo_list_concat multOp b (multSingleton u)) :=
                mk_rel_eq_relTerm_gt hLeft hRight
              have hAccNew : AbsCmpTypeAcc M
                  (__eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.gt)
                      (__eo_list_concat multOp a (multSingleton t)))
                    (__eo_list_concat multOp b (multSingleton u))) := by
                rw [hRelEq]
                exact AbsCmpTypeAcc.gt _ _ _ _ _ _ hLeft hRight
              have hRec := ih hBType hAccNew (by
                rw [if_pos hEqSelfRaw] at hTy
                exact hTy)
              rw [if_pos hEqSelfRaw]
              exact hRec
        · simp [__eo_ite, __eo_requires, hZero, native_teq,
            native_ite, __eo_l_2___mk_arith_mult_abs_comparison_rec] at hTy
          exact False.elim (false_of_typeof_stuck_bool (by simpa using hTy))
      · cases hCond : __eo_eq t tv with
        | Boolean c =>
            cases c
            · simp [hCond, __eo_ite, native_teq, native_ite,
                __eo_l_2___mk_arith_mult_abs_comparison_rec] at hTy
              exact False.elim (false_of_typeof_stuck_bool (by simpa using hTy))
            · exact False.elim (hSame (eq_of_eo_eq_true hCond))
        | _ =>
            simp [hCond, __eo_ite, native_teq, native_ite] at hTy
            exact False.elim (false_of_typeof_stuck_bool (by simpa using hTy)))
    (by
      intro dv1 dv2 h1 h2 hnot hFType hAcc hTy
      rw [__eo_l_1___mk_arith_mult_abs_comparison_rec.eq_4 dv1 dv2 h1 h2 hnot]
        at hTy ⊢
      exact l2_abs_comparison_has_bool_type M dv1 dv2 hFType hAcc hTy)
    (by
      intro x _hFType _hAcc hTy
      exact False.elim (false_of_typeof_stuck_bool
        (by simpa [__mk_arith_mult_abs_comparison_rec] using hTy)))
    (by
      intro x hx _hFType _hAcc hTy
      exact False.elim (false_of_typeof_stuck_bool
        (by
          rw [__mk_arith_mult_abs_comparison_rec.eq_2 x hx] at hTy
          simpa using hTy)))
    (by
      intro r t u B r2 a b ihRec ihL1 hFType hAcc hTy
      rw [__mk_arith_mult_abs_comparison_rec.eq_3] at hTy ⊢
      by_cases hSame : r = r2
      · subst r2
        simp [__eo_eq, __eo_ite, native_teq, native_ite] at hTy ⊢
        have hHeadType :
            RuleProofs.eo_has_bool_type (relTerm r (absTerm t) (absTerm u)) := by
          simpa [relTerm, absTerm] using
            RuleProofs.eo_has_bool_type_and_left _ _ hFType
        have hBType : RuleProofs.eo_has_bool_type B := by
          simpa [relTerm, absTerm] using
            RuleProofs.eo_has_bool_type_and_right _ _ hFType
        cases hAcc with
        | gt _ _ ka kb va vb ha hb =>
            rcases abs_gt_factor_type M hM t u (by simpa [relTerm] using hHeadType)
              with ⟨nt, nu, htList, huList⟩
            have hLeft := MultListFactors.concat ha htList
            have hRight := MultListFactors.concat hb huList
            have hRelEq :
                __eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.gt)
                    (__eo_list_concat multOp a (multSingleton t)))
                  (__eo_list_concat multOp b (multSingleton u)) =
                  relTerm (Term.UOp UserOp.gt)
                    (__eo_list_concat multOp a (multSingleton t))
                    (__eo_list_concat multOp b (multSingleton u)) :=
              mk_rel_eq_relTerm_gt hLeft hRight
            have hAccNew : AbsCmpTypeAcc M
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.gt)
                    (__eo_list_concat multOp a (multSingleton t)))
                  (__eo_list_concat multOp b (multSingleton u))) := by
              rw [hRelEq]
              exact AbsCmpTypeAcc.gt _ _ _ _ _ _ hLeft hRight
            exact ihRec hBType hAccNew hTy
        | eq _ _ ka kb va vb ha hb =>
            rcases abs_eq_factor_type M hM t u (by simpa [relTerm] using hHeadType)
              with ⟨nt, nu, htList, huList⟩
            have hLeft := MultListFactors.concat ha htList
            have hRight := MultListFactors.concat hb huList
            have hRelEq :
                __eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.eq)
                    (__eo_list_concat multOp a (multSingleton t)))
                  (__eo_list_concat multOp b (multSingleton u)) =
                  relTerm (Term.UOp UserOp.eq)
                    (__eo_list_concat multOp a (multSingleton t))
                    (__eo_list_concat multOp b (multSingleton u)) :=
              mk_rel_eq_relTerm_eq hLeft hRight
            have hAccNew : AbsCmpTypeAcc M
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.eq)
                    (__eo_list_concat multOp a (multSingleton t)))
                  (__eo_list_concat multOp b (multSingleton u))) := by
              rw [hRelEq]
              exact AbsCmpTypeAcc.eq _ _ _ _ _ _ hLeft hRight
            exact ihRec hBType hAccNew hTy
      · cases hCond : __eo_eq r r2 with
        | Boolean c =>
            cases c
            · simp [hCond, __eo_ite, native_teq, native_ite] at hTy ⊢
              exact ihL1 hFType hAcc hTy
            · exact False.elim (hSame (eq_of_eo_eq_true hCond))
        | _ =>
            simp [hCond, __eo_ite, native_teq, native_ite] at hTy
            exact False.elim (false_of_typeof_stuck_bool (by simpa using hTy)))
    (by
      intro dv1 dv2 h1 h2 hnot ihL1 hFType hAcc hTy
      rw [__mk_arith_mult_abs_comparison_rec.eq_4 dv1 dv2 h1 h2 hnot]
        at hTy ⊢
      exact ihL1 hFType hAcc hTy)
    F rel

private theorem arith_mult_abs_comparison_mk_has_bool_type
    (M : SmtModel) (hM : model_wf M) (F : Term) :
    RuleProofs.eo_has_bool_type F ->
    __eo_typeof (__mk_arith_mult_abs_comparison F) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__mk_arith_mult_abs_comparison F) := by
  intro hFType hTy
  unfold __mk_arith_mult_abs_comparison at hTy ⊢
  split at hTy
  · rename_i _ t u B
    have hHeadType :
        RuleProofs.eo_has_bool_type
          (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u)) := by
      simpa [relTerm, absTerm] using
        RuleProofs.eo_has_bool_type_and_left _ _ hFType
    have hBType : RuleProofs.eo_has_bool_type B := by
      simpa [relTerm, absTerm] using
        RuleProofs.eo_has_bool_type_and_right _ _ hFType
    rcases abs_gt_factor_type M hM t u hHeadType with
      ⟨nt, nu, htList, huList⟩
    have hRelEq :
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.gt) (multSingleton t))
          (multSingleton u) =
          relTerm (Term.UOp UserOp.gt) (multSingleton t) (multSingleton u) :=
      mk_rel_eq_relTerm_gt htList huList
    rw [hRelEq] at hTy ⊢
    exact arith_mult_abs_comparison_rec_has_bool_type M hM B
      (relTerm (Term.UOp UserOp.gt) (multSingleton t) (multSingleton u))
      hBType (AbsCmpTypeAcc.gt _ _ _ _ _ _ htList huList) hTy
  · rename_i _ t u B
    have hHeadType :
        RuleProofs.eo_has_bool_type
          (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)) := by
      simpa [relTerm, absTerm] using
        RuleProofs.eo_has_bool_type_and_left _ _ hFType
    have hBType : RuleProofs.eo_has_bool_type B := by
      simpa [relTerm, absTerm] using
        RuleProofs.eo_has_bool_type_and_right _ _ hFType
    rcases abs_eq_factor_type M hM t u hHeadType with
      ⟨nt, nu, htList, huList⟩
    have hRelEq :
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.eq) (multSingleton t))
          (multSingleton u) =
          relTerm (Term.UOp UserOp.eq) (multSingleton t) (multSingleton u) :=
      mk_rel_eq_relTerm_eq htList huList
    rw [hRelEq] at hTy ⊢
    exact arith_mult_abs_comparison_rec_has_bool_type M hM B
      (relTerm (Term.UOp UserOp.eq) (multSingleton t) (multSingleton u))
      hBType (AbsCmpTypeAcc.eq _ _ _ _ _ _ htList huList) hTy
  · exact False.elim (false_of_typeof_stuck_bool hTy)

theorem arith_mult_abs_comparison_has_smt_translation
    (M : SmtModel) (hM : model_wf M)
    (premises : List Term) :
    AllHaveBoolType premises ->
    __eo_typeof (__eo_prog_arith_mult_abs_comparison
      (Proof.pf (premiseAndFormulaList premises))) = Term.Bool ->
    RuleProofs.eo_has_smt_translation
      (__eo_prog_arith_mult_abs_comparison
        (Proof.pf (premiseAndFormulaList premises))) := by
  intro hPremisesType hTy
  have hFType := premiseAndFormulaList_has_bool_type premises hPremisesType
  change __eo_typeof
    (__mk_arith_mult_abs_comparison (premiseAndFormulaList premises)) =
      Term.Bool at hTy
  change RuleProofs.eo_has_smt_translation
    (__mk_arith_mult_abs_comparison (premiseAndFormulaList premises))
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (arith_mult_abs_comparison_mk_has_bool_type M hM
      (premiseAndFormulaList premises) hFType hTy)

private theorem l2_abs_comparison_true
    (M : SmtModel) (F rel : Term) :
    eo_interprets M F true ->
    AbsCmpAcc M rel ->
    __eo_typeof (__eo_l_2___mk_arith_mult_abs_comparison_rec F rel) = Term.Bool ->
    eo_interprets M (__eo_l_2___mk_arith_mult_abs_comparison_rec F rel) true := by
  intro _hFTrue hAcc hTy
  cases hAcc with
  | gt a b ka kb va vb ha hb hLt =>
      cases F <;> try
        exact False.elim (false_of_typeof_stuck_bool
          (by simpa [__eo_l_2___mk_arith_mult_abs_comparison_rec] using hTy))
      case Boolean b =>
        cases b
        · exact False.elim (false_of_typeof_stuck_bool
            (by simpa [__eo_l_2___mk_arith_mult_abs_comparison_rec] using hTy))
        · simpa [relTerm, __eo_l_2___mk_arith_mult_abs_comparison_rec] using
            (AbsCmpAcc.final_true (M := M)
              (AbsCmpAcc.gt a b ka kb va vb ha hb hLt)
              (by simpa [relTerm, __eo_l_2___mk_arith_mult_abs_comparison_rec]
                using hTy))
  | eq a b ka kb va vb ha hb hEq =>
      cases F <;> try
        exact False.elim (false_of_typeof_stuck_bool
          (by simpa [__eo_l_2___mk_arith_mult_abs_comparison_rec] using hTy))
      case Boolean b =>
        cases b
        · exact False.elim (false_of_typeof_stuck_bool
            (by simpa [__eo_l_2___mk_arith_mult_abs_comparison_rec] using hTy))
        · simpa [relTerm, __eo_l_2___mk_arith_mult_abs_comparison_rec] using
            (AbsCmpAcc.final_true (M := M)
              (AbsCmpAcc.eq a b ka kb va vb ha hb hEq)
              (by simpa [relTerm, __eo_l_2___mk_arith_mult_abs_comparison_rec]
                using hTy))

private theorem facts_arith_mult_abs_comparison_rec
    (M : SmtModel) (hM : model_wf M)
    (F rel : Term) :
    eo_interprets M F true ->
    AbsCmpAcc M rel ->
    __eo_typeof (__mk_arith_mult_abs_comparison_rec F rel) = Term.Bool ->
    eo_interprets M (__mk_arith_mult_abs_comparison_rec F rel) true := by
  let motive1 := fun F rel =>
    eo_interprets M F true ->
    AbsCmpAcc M rel ->
    __eo_typeof (__eo_l_1___mk_arith_mult_abs_comparison_rec F rel) = Term.Bool ->
    eo_interprets M (__eo_l_1___mk_arith_mult_abs_comparison_rec F rel) true
  let motive2 := fun F rel =>
    eo_interprets M F true ->
    AbsCmpAcc M rel ->
    __eo_typeof (__mk_arith_mult_abs_comparison_rec F rel) = Term.Bool ->
    eo_interprets M (__mk_arith_mult_abs_comparison_rec F rel) true
  exact __mk_arith_mult_abs_comparison_rec.induct motive1 motive2
    (by
      intro x _hFTrue _hAcc hTy
      exact False.elim (false_of_typeof_stuck_bool
        (by simpa [__eo_l_1___mk_arith_mult_abs_comparison_rec] using hTy)))
    (by
      intro x hx _hFTrue _hAcc hTy
      exact False.elim (false_of_typeof_stuck_bool
        (by
          rw [__eo_l_1___mk_arith_mult_abs_comparison_rec.eq_2 x hx] at hTy
          simpa using hTy)))
    (by
      intro t u tv z B a b ih hFTrue hAcc hTy
      rw [__eo_l_1___mk_arith_mult_abs_comparison_rec.eq_3] at hTy ⊢
      by_cases hSame : t = tv
      · subst tv
        by_cases hZero :
            __eo_to_q z = Term.Rational (native_mk_rational 0 1)
        · simp [__eo_ite, __eo_requires, hZero, native_teq,
            native_ite, native_not, SmtEval.native_not] at hTy ⊢
          have hLeftTrue :
              eo_interprets M
                (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                  (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u)))
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                    (Term.Apply (Term.UOp UserOp.not)
                      (relTerm (Term.UOp UserOp.eq) t z)))
                    (Term.Boolean true))) true :=
            RuleProofs.eo_interprets_and_left M _ B hFTrue
          have hBTrue : eo_interprets M B true :=
            RuleProofs.eo_interprets_and_right M _ B hFTrue
          have hEqAbsTrue :
              eo_interprets M (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u))
                true :=
            RuleProofs.eo_interprets_and_left M _ _ hLeftTrue
          have hTailTrue :
              eo_interprets M
                (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                  (Term.Apply (Term.UOp UserOp.not)
                    (relTerm (Term.UOp UserOp.eq) t z)))
                  (Term.Boolean true)) true :=
            RuleProofs.eo_interprets_and_right M _ _ hLeftTrue
          have hNotEqTrue :
              eo_interprets M
                (Term.Apply (Term.UOp UserOp.not)
                  (relTerm (Term.UOp UserOp.eq) t z)) true :=
            RuleProofs.eo_interprets_and_left M _ _ hTailTrue
          rcases abs_eq_factor_factors M hM t u hEqAbsTrue with
            ⟨nt, nu, htTy, htEval, htList, huList, hEqAbs⟩
          have htNe : t ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_smt_translation t (by
              unfold RuleProofs.eo_has_smt_translation
              rw [htTy]
              cases nt <;> simp [ArithValue.smtType])
          have hEqSelf : __eo_eq t t = Term.Boolean true :=
            eo_eq_self_of_ne_stuck htNe
          -- state this in the folded shape: v4.33 keeps `__eo_eq` folded in the
          -- `ite` guard, and the unfolded `match` form is a distinct (dependent)
          -- matcher that no longer converts.
          have hEqSelfRaw : __eo_eq t t = Term.Boolean true :=
            RuleProofs.eo_eq_self_of_ne_stuck t htNe
          cases hAcc with
          | gt _ _ ka kb va vb ha hb hLt =>
              have hPos := abs_factor_nonzero_factors M t z nt htTy htEval hZero hNotEqTrue
              have hLeft := MultListFactors.concat ha htList
              have hRight := MultListFactors.concat hb huList
              have hNewLt :
                  factorMagnitude (vb ++ [nu]) < factorMagnitude (va ++ [nt]) :=
                factorMagnitude_append_lt_append_of_lt_eq_pos hLt hEqAbs hPos
              have hRelEq :
                  __eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.gt)
                      (__eo_list_concat multOp a (multSingleton t)))
                    (__eo_list_concat multOp b (multSingleton u)) =
                    relTerm (Term.UOp UserOp.gt)
                      (__eo_list_concat multOp a (multSingleton t))
                      (__eo_list_concat multOp b (multSingleton u)) :=
                mk_rel_eq_relTerm_gt hLeft hRight
              have hAccNew : AbsCmpAcc M
                  (__eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.gt)
                      (__eo_list_concat multOp a (multSingleton t)))
                    (__eo_list_concat multOp b (multSingleton u))) := by
                rw [hRelEq]
                exact
                  AbsCmpAcc.gt _ _ _ _ _ _ hLeft hRight hNewLt
              have hRec := ih hBTrue hAccNew (by
                rw [if_pos hEqSelfRaw] at hTy
                exact hTy)
              rw [if_pos hEqSelfRaw]
              exact hRec
        · simp [__eo_ite, __eo_requires, hZero, native_teq,
            native_ite, __eo_l_2___mk_arith_mult_abs_comparison_rec] at hTy
          exact False.elim (false_of_typeof_stuck_bool (by simpa using hTy))
      · cases hCond : __eo_eq t tv with
        | Boolean c =>
            cases c
            · simp [hCond, __eo_ite, native_teq, native_ite,
                __eo_l_2___mk_arith_mult_abs_comparison_rec] at hTy
              exact False.elim (false_of_typeof_stuck_bool (by simpa using hTy))
            · exact False.elim (hSame (eq_of_eo_eq_true hCond))
        | _ =>
            simp [hCond, __eo_ite, native_teq, native_ite] at hTy
            exact False.elim (false_of_typeof_stuck_bool (by simpa using hTy)))
    (by
      intro dv1 dv2 h1 h2 hnot hFTrue hAcc hTy
      rw [__eo_l_1___mk_arith_mult_abs_comparison_rec.eq_4 dv1 dv2 h1 h2 hnot]
        at hTy ⊢
      exact l2_abs_comparison_true M dv1 dv2 hFTrue hAcc hTy)
    (by
      intro x _hFTrue _hAcc hTy
      exact False.elim (false_of_typeof_stuck_bool
        (by simpa [__mk_arith_mult_abs_comparison_rec] using hTy)))
    (by
      intro x hx _hFTrue _hAcc hTy
      exact False.elim (false_of_typeof_stuck_bool
        (by
          rw [__mk_arith_mult_abs_comparison_rec.eq_2 x hx] at hTy
          simpa using hTy)))
    (by
      intro r t u B r2 a b ihRec ihL1 hFTrue hAcc hTy
      rw [__mk_arith_mult_abs_comparison_rec.eq_3] at hTy ⊢
      by_cases hSame : r = r2
      · subst r2
        simp [__eo_eq, __eo_ite, native_teq, native_ite] at hTy ⊢
        have hHeadTrue :
            eo_interprets M (relTerm r (absTerm t) (absTerm u)) true :=
          RuleProofs.eo_interprets_and_left M _ B hFTrue
        have hBTrue : eo_interprets M B true :=
          RuleProofs.eo_interprets_and_right M _ B hFTrue
        cases hAcc with
        | gt _ _ ka kb va vb ha hb hLt =>
            rcases abs_gt_factor_factors M hM t u (by simpa [relTerm] using hHeadTrue)
              with ⟨nt, nu, htList, huList, hGt⟩
            have hLeft := MultListFactors.concat ha htList
            have hRight := MultListFactors.concat hb huList
            have hNewLt :
                factorMagnitude (vb ++ [nu]) < factorMagnitude (va ++ [nt]) :=
              factorMagnitude_append_lt_append_of_lt_lt hLt hGt
            have hRelEq :
                __eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.gt)
                    (__eo_list_concat multOp a (multSingleton t)))
                  (__eo_list_concat multOp b (multSingleton u)) =
                  relTerm (Term.UOp UserOp.gt)
                    (__eo_list_concat multOp a (multSingleton t))
                    (__eo_list_concat multOp b (multSingleton u)) :=
              mk_rel_eq_relTerm_gt hLeft hRight
            have hAccNew : AbsCmpAcc M
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.gt)
                    (__eo_list_concat multOp a (multSingleton t)))
                  (__eo_list_concat multOp b (multSingleton u))) := by
              rw [hRelEq]
              exact
                AbsCmpAcc.gt _ _ _ _ _ _ hLeft hRight hNewLt
            exact ihRec hBTrue
              hAccNew hTy
        | eq _ _ ka kb va vb ha hb hEq =>
            rcases abs_eq_factor_factors M hM t u (by simpa [relTerm] using hHeadTrue)
              with ⟨nt, nu, _htTy, _htEval, htList, huList, hEqPrem⟩
            have hLeft := MultListFactors.concat ha htList
            have hRight := MultListFactors.concat hb huList
            have hNewEq :
                factorMagnitude (va ++ [nt]) = factorMagnitude (vb ++ [nu]) :=
              factorMagnitude_append_eq_append_of_eq_eq hEq hEqPrem
            have hRelEq :
                __eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.eq)
                    (__eo_list_concat multOp a (multSingleton t)))
                  (__eo_list_concat multOp b (multSingleton u)) =
                  relTerm (Term.UOp UserOp.eq)
                    (__eo_list_concat multOp a (multSingleton t))
                    (__eo_list_concat multOp b (multSingleton u)) :=
              mk_rel_eq_relTerm_eq hLeft hRight
            have hAccNew : AbsCmpAcc M
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.eq)
                    (__eo_list_concat multOp a (multSingleton t)))
                  (__eo_list_concat multOp b (multSingleton u))) := by
              rw [hRelEq]
              exact
                AbsCmpAcc.eq _ _ _ _ _ _ hLeft hRight hNewEq
            exact ihRec hBTrue
              hAccNew hTy
      · cases hCond : __eo_eq r r2 with
        | Boolean c =>
            cases c
            · simp [hCond, __eo_ite, native_teq, native_ite] at hTy ⊢
              exact ihL1 hFTrue hAcc hTy
            · exact False.elim (hSame (eq_of_eo_eq_true hCond))
        | _ =>
            simp [hCond, __eo_ite, native_teq, native_ite] at hTy
            exact False.elim (false_of_typeof_stuck_bool (by simpa using hTy)))
    (by
      intro dv1 dv2 h1 h2 hnot ihL1 hFTrue hAcc hTy
      rw [__mk_arith_mult_abs_comparison_rec.eq_4 dv1 dv2 h1 h2 hnot]
        at hTy ⊢
      exact ihL1 hFTrue hAcc hTy)
    F rel

private theorem facts_arith_mult_abs_comparison_mk
    (M : SmtModel) (hM : model_wf M) (F : Term) :
    eo_interprets M F true ->
    __eo_typeof (__mk_arith_mult_abs_comparison F) = Term.Bool ->
    eo_interprets M (__mk_arith_mult_abs_comparison F) true := by
  intro hFTrue hTy
  unfold __mk_arith_mult_abs_comparison at hTy ⊢
  split at hTy
  · rename_i _ t u B
    have hHeadTrue :
        eo_interprets M (relTerm (Term.UOp UserOp.gt) (absTerm t) (absTerm u))
          true :=
      RuleProofs.eo_interprets_and_left M _ B hFTrue
    have hBTrue : eo_interprets M B true :=
      RuleProofs.eo_interprets_and_right M _ B hFTrue
    rcases abs_gt_factor_factors M hM t u hHeadTrue with
      ⟨nt, nu, htList, huList, hGt⟩
    have hRelEq :
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.gt) (multSingleton t))
          (multSingleton u) =
          relTerm (Term.UOp UserOp.gt) (multSingleton t) (multSingleton u) :=
      mk_rel_eq_relTerm_gt htList huList
    rw [hRelEq] at hTy ⊢
    exact facts_arith_mult_abs_comparison_rec M hM B
      (relTerm (Term.UOp UserOp.gt) (multSingleton t) (multSingleton u))
      hBTrue (AbsCmpAcc.gt _ _ _ _ _ _ htList huList hGt) hTy
  · rename_i _ t u B
    have hHeadTrue :
        eo_interprets M (relTerm (Term.UOp UserOp.eq) (absTerm t) (absTerm u))
          true :=
      RuleProofs.eo_interprets_and_left M _ B hFTrue
    have hBTrue : eo_interprets M B true :=
      RuleProofs.eo_interprets_and_right M _ B hFTrue
    rcases abs_eq_factor_factors M hM t u hHeadTrue with
      ⟨nt, nu, _htTy, _htEval, htList, huList, hEq⟩
    have hRelEq :
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.eq) (multSingleton t))
          (multSingleton u) =
          relTerm (Term.UOp UserOp.eq) (multSingleton t) (multSingleton u) :=
      mk_rel_eq_relTerm_eq htList huList
    rw [hRelEq] at hTy ⊢
    exact facts_arith_mult_abs_comparison_rec M hM B
      (relTerm (Term.UOp UserOp.eq) (multSingleton t) (multSingleton u))
      hBTrue (AbsCmpAcc.eq _ _ _ _ _ _ htList huList hEq) hTy
  · exact False.elim (false_of_typeof_stuck_bool hTy)

theorem facts_arith_mult_abs_comparison
    (M : SmtModel) (hM : model_wf M)
    (premises : List Term) :
    AllInterpretedTrue M premises ->
    __eo_typeof (__eo_prog_arith_mult_abs_comparison
      (Proof.pf (premiseAndFormulaList premises))) = Term.Bool ->
    eo_interprets M
      (__eo_prog_arith_mult_abs_comparison
        (Proof.pf (premiseAndFormulaList premises))) true := by
  intro hPremisesTrue hTy
  have hFTrue := premiseAndFormulaList_true_of_all_true M premises hPremisesTrue
  change __eo_typeof
    (__mk_arith_mult_abs_comparison (premiseAndFormulaList premises)) =
      Term.Bool at hTy
  change eo_interprets M
    (__mk_arith_mult_abs_comparison (premiseAndFormulaList premises)) true
  exact facts_arith_mult_abs_comparison_mk M hM
    (premiseAndFormulaList premises) hFTrue hTy

end ArithMultSupport
