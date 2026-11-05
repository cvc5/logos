module

public import Cpc.Proofs.RealBridge
import all Cpc.Proofs.RealBridge
import all Cpc.SmtReal
public import Cpc.Proofs.RuleSupport.ArithValueSupport
import all Cpc.Proofs.RuleSupport.ArithValueSupport

public section

noncomputable section

open ArithValueSupport

open SmtEval

namespace ArithFactorSupport

/-- Every value in a factor list has the same arithmetic kind. -/
def allFactorKind (k : ArithKind) : List ArithValue -> Prop
  | [] => True
  | v :: vs => v.kind = k ∧ allFactorKind k vs

/-- Product of the nonnegative magnitudes of a factor list. -/
def factorMagnitude : List ArithValue -> native_Real
  | [] => 1
  | v :: vs => v.magnitude * factorMagnitude vs

/-- Typed product of a factor list, using the kind's multiplicative identity. -/
def factorProduct : ArithKind -> List ArithValue -> ArithValue
  | k, [] => ArithValue.one k
  | k, v :: vs => v.mul (factorProduct k vs)

theorem allFactorKind_append {k : ArithKind} {xs ys : List ArithValue} :
    allFactorKind k (xs ++ ys) ↔
      allFactorKind k xs ∧ allFactorKind k ys := by
  induction xs with
  | nil => simp [allFactorKind]
  | cons x xs ih =>
      change (x.kind = k ∧ allFactorKind k (xs ++ ys)) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hx, hxs, hys⟩
        exact ⟨⟨hx, hxs⟩, hys⟩
      · rintro ⟨⟨hx, hxs⟩, hys⟩
        exact ⟨hx, hxs, hys⟩

theorem factorMagnitude_nonneg (xs : List ArithValue) :
    0 <= factorMagnitude xs := by
  induction xs with
  | nil => simp [factorMagnitude]
  | cons x xs ih =>
      exact mul_nonneg (ArithValue.magnitude_nonneg x) ih

theorem factorMagnitude_append (xs ys : List ArithValue) :
    factorMagnitude (xs ++ ys) = factorMagnitude xs * factorMagnitude ys := by
  induction xs with
  | nil => simp [factorMagnitude]
  | cons x xs ih =>
      simp [factorMagnitude, ih, mul_assoc]

theorem factorMagnitude_append_lt_append_of_lt_lt
    {a b c d : List ArithValue}
    (hAB : factorMagnitude b < factorMagnitude a)
    (hCD : factorMagnitude d < factorMagnitude c) :
    factorMagnitude (b ++ d) < factorMagnitude (a ++ c) := by
  rw [factorMagnitude_append, factorMagnitude_append]
  exact mul_lt_mul'' hAB hCD (factorMagnitude_nonneg b) (factorMagnitude_nonneg d)

theorem factorMagnitude_append_eq_append_of_eq_eq
    {a b c d : List ArithValue}
    (hAB : factorMagnitude a = factorMagnitude b)
    (hCD : factorMagnitude c = factorMagnitude d) :
    factorMagnitude (a ++ c) = factorMagnitude (b ++ d) := by
  simp [factorMagnitude_append, hAB, hCD]

theorem factorMagnitude_append_lt_append_of_lt_eq_pos
    {a b c d : List ArithValue}
    (hAB : factorMagnitude b < factorMagnitude a)
    (hCD : factorMagnitude c = factorMagnitude d)
    (hPos : 0 < factorMagnitude c) :
    factorMagnitude (b ++ d) < factorMagnitude (a ++ c) := by
  rw [factorMagnitude_append, factorMagnitude_append, ← hCD]
  exact mul_lt_mul_of_pos_right hAB hPos

theorem factorProduct_kind {k : ArithKind} {vs : List ArithValue}
    (h : allFactorKind k vs) : (factorProduct k vs).kind = k := by
  induction vs with
  | nil => cases k <;> simp [factorProduct, ArithValue.one, ArithValue.kind]
  | cons v vs ih =>
      rcases h with ⟨hv, hvs⟩
      exact (ArithValue.kind_mul_of_same_kind (hv.trans (ih hvs).symm)).trans hv

theorem factorProduct_magnitude {k : ArithKind} {vs : List ArithValue}
    (h : allFactorKind k vs) :
    (factorProduct k vs).magnitude = factorMagnitude vs := by
  induction vs with
  | nil =>
      simp [factorProduct, factorMagnitude]
  | cons v vs ih =>
      rcases h with ⟨hv, hvs⟩
      rw [factorProduct, factorMagnitude,
        ArithValue.magnitude_mul_of_same_kind
          (hv.trans (factorProduct_kind hvs).symm),
        ih hvs]

end ArithFactorSupport
