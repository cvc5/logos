module

public import Cpc.SmtModel
import all Cpc.SmtReal
import all Cpc.SmtEval
import all Cpc.SmtModel
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# From the checker's rationals to the model's reals

The checker computes with `native_Rat` while a value of sort `Real` holds a
`native_Real`. A literal denotes its image under `native_rat_to_real`. The lemmas
here say that image commutes with every operation the checker computes, which is
what lets a rule's proof move a side condition computed on literals to the values
those literals denote.
-/

@[expose] public section

namespace SmtEval

noncomputable section

/-- Equality of real values, as the model's `native_veq` decides it. -/
noncomputable def native_req (x y : native_Real) : native_Bool := decide (x = y)

theorem native_rat_to_real_mk_rational (x y : native_Int) :
    native_rat_to_real (native_mk_rational x y) = native_mk_real x y := by
  simp [native_rat_to_real, native_mk_rational, native_mk_real]

theorem native_rat_to_real_to_real (x : native_Int) :
    native_rat_to_real (native_to_real x) = native_int_to_real x := by
  simp [native_rat_to_real, native_to_real, native_mk_rational, native_int_to_real]

theorem native_rat_to_real_qplus (a b : native_Rat) :
    native_rat_to_real (native_qplus a b) =
      native_rplus (native_rat_to_real a) (native_rat_to_real b) := by
  simp [native_rat_to_real, native_qplus, native_rplus]

theorem native_rat_to_real_qmult (a b : native_Rat) :
    native_rat_to_real (native_qmult a b) =
      native_rmult (native_rat_to_real a) (native_rat_to_real b) := by
  simp [native_rat_to_real, native_qmult, native_rmult]

theorem native_rat_to_real_qneg (a : native_Rat) :
    native_rat_to_real (native_qneg a) = native_rneg (native_rat_to_real a) := by
  simp [native_rat_to_real, native_qneg, native_rneg]

theorem native_rat_to_real_qdiv_total (a b : native_Rat) :
    native_rat_to_real (native_qdiv_total a b) =
      native_rdiv_total (native_rat_to_real a) (native_rat_to_real b) := by
  simp [native_rat_to_real, native_qdiv_total, native_rdiv_total]

theorem native_rlt_rat_to_real (a b : native_Rat) :
    native_rlt (native_rat_to_real a) (native_rat_to_real b) = native_qlt a b := by
  simp [native_rlt, native_qlt, native_rat_to_real]

theorem native_real_to_int_rat_to_real (q : native_Rat) :
    native_real_to_int (native_rat_to_real q) = native_to_int q := by
  simp only [native_real_to_int, native_rat_to_real, native_to_int]
  rw [Rat.floor_cast]
  rfl

theorem native_rat_to_real_inj {a b : native_Rat} :
    native_rat_to_real a = native_rat_to_real b ↔ a = b := by
  simp [native_rat_to_real]

theorem native_int_to_real_eq_rat (x : native_Int) :
    native_int_to_real x = native_rat_to_real (native_to_real x) :=
  (native_rat_to_real_to_real x).symm

theorem native_real_to_int_int_to_real (x : native_Int) :
    native_real_to_int (native_int_to_real x) = x := by
  simp [native_real_to_int, native_int_to_real]

end

end SmtEval

namespace Smtm

noncomputable section

open SmtEval

theorem native_rat_to_real_qabs (a : native_Rat) :
    native_rat_to_real (native_qabs a) = native_rabs (native_rat_to_real a) := by
  simp only [native_rat_to_real, native_qabs, native_rabs]
  by_cases h : a < 0
  · have hr : (a : _root_.Real) < 0 := by exact_mod_cast h
    rw [ite_eq_left_iff.mpr (fun hn => absurd h hn), abs_of_neg hr]
    simp
  · have hr : (0 : _root_.Real) ≤ a := by exact_mod_cast (not_lt.mp h)
    rw [ite_eq_right_iff.mpr (fun hp => absurd hp h), abs_of_nonneg hr]

theorem native_rleq_rat_to_real (a b : native_Rat) :
    native_rleq (native_rat_to_real a) (native_rat_to_real b) = native_qleq a b := by
  simp [native_rleq, native_qleq, native_rat_to_real]

end

end Smtm

namespace SmtEval

/-!
realSimpNormal: `simp` normal forms for proofs over values. A value operation
becomes the corresponding operation of `ℝ`, and a literal the cast of a rational
whose arithmetic moves outside the cast.
-/

attribute [simp] native_rat_to_real native_int_to_real native_mk_real native_rplus
  native_rmult native_rneg native_rabs native_rdiv_total

@[simp] theorem cast_native_zplus (a b : native_Int) :
    ((native_zplus a b : native_Int) : native_Real) = (a : native_Real) + (b : native_Real) := by
  simp [native_zplus]

@[simp] theorem cast_native_zmult (a b : native_Int) :
    ((native_zmult a b : native_Int) : native_Real) = (a : native_Real) * (b : native_Real) := by
  simp [native_zmult]

@[simp] theorem cast_native_zneg (a : native_Int) :
    ((native_zneg a : native_Int) : native_Real) = -(a : native_Real) := by
  simp [native_zneg]

@[simp] theorem cast_native_qplus (a b : native_Rat) :
    ((native_qplus a b : native_Rat) : native_Real) = (a : native_Real) + (b : native_Real) := by
  simp [native_qplus]

@[simp] theorem cast_native_qmult (a b : native_Rat) :
    ((native_qmult a b : native_Rat) : native_Real) = (a : native_Real) * (b : native_Real) := by
  simp [native_qmult]

@[simp] theorem cast_native_qneg (a : native_Rat) :
    ((native_qneg a : native_Rat) : native_Real) = -(a : native_Real) := by
  simp [native_qneg]

@[simp] theorem cast_native_qdiv_total (a b : native_Rat) :
    ((native_qdiv_total a b : native_Rat) : native_Real) = (a : native_Real) / (b : native_Real) := by
  have := native_rat_to_real_qdiv_total a b
  simpa using this

@[simp] theorem cast_native_mk_rational (x y : native_Int) :
    ((native_mk_rational x y : native_Rat) : native_Real) = (x : native_Real) / (y : native_Real) := by
  have := native_rat_to_real_mk_rational x y
  simpa using this

@[simp] theorem cast_native_to_real (x : native_Int) :
    ((native_to_real x : native_Rat) : native_Real) = (x : native_Real) := by
  have := native_rat_to_real_to_real x
  simpa using this

theorem native_mk_real_zero : native_mk_real 0 1 = 0 := by simp

theorem native_mk_real_one : native_mk_real 1 1 = 1 := by simp

end SmtEval
