module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false

namespace ArithValueSupport

/-- The two scalar arithmetic sorts handled by overloaded arithmetic rules. -/
inductive ArithKind where
  | int
  | real
deriving DecidableEq

/-- A scalar arithmetic model value, retaining whether it is integral or real. -/
inductive ArithValue where
  | int (n : native_Int)
  | real (q : native_Rat)

namespace ArithValue

def kind : ArithValue -> ArithKind
  | .int _ => .int
  | .real _ => .real

def smtType : ArithValue -> SmtType
  | .int _ => SmtType.Int
  | .real _ => SmtType.Real

def eoType : ArithValue -> Term
  | .int _ => Term.Int
  | .real _ => Term.Real

def one : ArithKind -> ArithValue
  | .int => .int 1
  | .real => .real 1

def zero : ArithKind -> ArithValue
  | .int => .int 0
  | .real => .real 0

def mul : ArithValue -> ArithValue -> ArithValue
  | .int a, .int b => .int (a * b)
  | .real a, .real b => .real (a * b)
  | a, _ => a

def abs : ArithValue -> ArithValue
  | .int a => .int (native_zabs a)
  | .real a => .real (native_qabs a)

def smtValue : ArithValue -> SmtValue
  | .int a => SmtValue.Numeral a
  | .real a => SmtValue.Rational a

private def intAbs (n : native_Int) : native_Int :=
  ((Int.natAbs n : Nat) : Int)

/-- A common nonnegative rational magnitude for integer and real values. -/
def magnitude : ArithValue -> Rat
  | .int a => (intAbs a : Rat)
  | .real a => native_qabs a

def ltBool : ArithValue -> ArithValue -> native_Bool
  | .int a, .int b => native_zlt a b
  | .real a, .real b => native_qlt a b
  | _, _ => false

def eqBool : ArithValue -> ArithValue -> native_Bool
  | .int a, .int b => native_zeq a b
  | .real a, .real b => native_qeq a b
  | _, _ => false

private theorem intAbs_nonneg (n : native_Int) : 0 <= intAbs n := by
  exact Int.natCast_nonneg _

private theorem intAbs_mul (a b : native_Int) :
    intAbs (a * b) = intAbs a * intAbs b := by
  simp [intAbs, Int.natAbs_mul, Int.natCast_mul]

private theorem native_zabs_eq_intAbs (n : native_Int) :
    native_zabs n = intAbs n := by
  by_cases hneg : n < 0
  · have hnonpos : n <= 0 := Int.le_of_lt hneg
    simp [native_zabs, hneg, intAbs, Int.ofNat_natAbs_of_nonpos hnonpos]
  · have hnonneg : 0 <= n := Int.le_of_not_gt hneg
    simp [native_zabs, hneg, intAbs, Int.natAbs_of_nonneg hnonneg]

theorem magnitude_nonneg (a : ArithValue) : 0 <= magnitude a := by
  cases a with
  | int a =>
      exact Rat.intCast_nonneg.mpr (intAbs_nonneg a)
  | real a =>
      simp only [magnitude]
      unfold native_qabs
      by_cases hneg : a < 0
      · simp [hneg, Rat.le_of_lt (by simpa using Rat.neg_lt_neg hneg)]
      · simpa [hneg] using Rat.not_lt.mp hneg

@[simp] theorem magnitude_one (k : ArithKind) : magnitude (one k) = 1 := by
  cases k <;> native_decide

private theorem native_qabs_mul (a b : native_Rat) :
    native_qabs (a * b) = native_qabs a * native_qabs b := by
  by_cases ha : a < 0
  · by_cases hb : b < 0
    · have hna : 0 < -a := by simpa using Rat.neg_lt_neg ha
      have hnb : 0 < -b := by simpa using Rat.neg_lt_neg hb
      have habPos : 0 < a * b := by
        have := Rat.mul_pos hna hnb
        simpa [Rat.neg_mul, Rat.mul_neg] using this
      have hab : ¬ a * b < 0 := Rat.not_lt.mpr (Rat.le_of_lt habPos)
      simp [native_qabs, ha, hb, hab, Rat.neg_mul, Rat.mul_neg]
    · have hb0 : 0 <= b := Rat.not_lt.mp hb
      by_cases hbZero : b = 0
      · subst b
        simp [native_qabs]
      · have hbPos : 0 < b := Rat.lt_of_le_of_ne hb0 (Ne.symm hbZero)
        have hab : a * b < 0 := (Rat.mul_neg_iff_of_pos_right hbPos).mpr ha
        simp [native_qabs, ha, hb, hab, Rat.neg_mul]
  · have ha0 : 0 <= a := Rat.not_lt.mp ha
    by_cases hb : b < 0
    · by_cases haZero : a = 0
      · subst a
        simp [native_qabs]
      · have haPos : 0 < a := Rat.lt_of_le_of_ne ha0 (Ne.symm haZero)
        have hab : a * b < 0 := (Rat.mul_neg_iff_of_pos_left haPos).mpr hb
        simp [native_qabs, ha, hb, hab, Rat.mul_neg]
    · have hb0 : 0 <= b := Rat.not_lt.mp hb
      have hab : ¬ a * b < 0 := Rat.not_lt.mpr (Rat.mul_nonneg ha0 hb0)
      simp [native_qabs, ha, hb, hab]

theorem kind_mul_of_same_kind {a b : ArithValue}
    (h : kind a = kind b) : kind (mul a b) = kind a := by
  cases a <;> cases b <;> simp [kind, mul] at h ⊢

theorem smtType_eq_of_kind {a b : ArithValue} (h : kind a = kind b) :
    smtType a = smtType b := by
  cases a <;> cases b <;> simp [kind, smtType] at h ⊢

theorem modelEval_mul_of_same_kind {a b : ArithValue}
    (h : kind a = kind b) :
    __smtx_model_eval_mult a.smtValue b.smtValue = (mul a b).smtValue := by
  cases a <;> cases b <;>
    simp [kind, smtValue, mul, __smtx_model_eval_mult, native_zmult,
      native_qmult] at h ⊢

theorem magnitude_mul_of_same_kind {a b : ArithValue}
    (h : kind a = kind b) :
    magnitude (mul a b) = magnitude a * magnitude b := by
  cases a with
  | int a =>
      cases b with
      | int b => simp [magnitude, mul, intAbs_mul]
      | real b => simp [kind] at h
  | real a =>
      cases b with
      | int b => simp [kind] at h
      | real b =>
          simp only [magnitude, mul]
          exact native_qabs_mul a b

theorem ltBool_abs_true_iff_same_kind {a b : ArithValue}
    (h : kind a = kind b) :
    ltBool (abs a) (abs b) = true ↔ magnitude a < magnitude b := by
  cases a with
  | int a =>
      cases b with
      | real b => simp [kind] at h
      | int b =>
          simp [ltBool, abs, magnitude, native_zlt, native_zabs_eq_intAbs,
            Rat.intCast_lt_intCast]
  | real a =>
      cases b with
      | int b => simp [kind] at h
      | real b =>
          change decide (native_qabs a < native_qabs b) = true ↔
            native_qabs a < native_qabs b
          simp

theorem eqBool_abs_true_iff_same_kind {a b : ArithValue}
    (h : kind a = kind b) :
    eqBool (abs a) (abs b) = true ↔ magnitude a = magnitude b := by
  cases a with
  | int a =>
      cases b with
      | real b => simp [kind] at h
      | int b =>
          simp [eqBool, abs, magnitude, native_zeq, native_zabs_eq_intAbs]
  | real a =>
      cases b with
      | int b => simp [kind] at h
      | real b =>
          change decide (native_qabs a = native_qabs b) = true ↔
            native_qabs a = native_qabs b
          simp

theorem magnitude_pos_of_eqBool_zero_false {a : ArithValue} :
    eqBool a (zero (kind a)) = false → 0 < magnitude a := by
  intro h
  cases a with
  | int a =>
      simp only [eqBool, zero, kind, magnitude] at h ⊢
      unfold native_zeq at h
      have ha : a ≠ 0 := by simpa using h
      have hpos : 0 < intAbs a := by
        exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr ha)
      exact (Rat.intCast_lt_intCast).mpr hpos
  | real a =>
      simp only [eqBool, zero, kind, magnitude] at h ⊢
      unfold native_qeq at h
      have ha : a ≠ 0 := by simpa using h
      by_cases hneg : a < 0
      · have hpos : 0 < -a := by simpa using Rat.neg_lt_neg hneg
        simpa [native_qabs, hneg] using hpos
      · have ha0 : 0 <= a := Rat.not_lt.mp hneg
        have hpos : 0 < a := Rat.lt_of_le_of_ne ha0 (Ne.symm ha)
        simpa [native_qabs, hneg] using hpos

theorem magnitude_mul_lt_mul_of_lt_lt {a b c d : ArithValue}
    (hAB : magnitude b < magnitude a)
    (hCD : magnitude d < magnitude c)
    (hAC : kind a = kind c)
    (hABK : kind a = kind b)
    (hCDK : kind c = kind d) :
    magnitude (mul b d) < magnitude (mul a c) := by
  rw [magnitude_mul_of_same_kind (hABK.symm.trans hAC |>.trans hCDK),
    magnitude_mul_of_same_kind hAC]
  have hb := magnitude_nonneg b
  have hd := magnitude_nonneg d
  have hcNe : magnitude c ≠ 0 := by
    intro hc
    rw [hc] at hCD
    exact (Rat.not_lt.mpr hd) hCD
  have hcPos : 0 < magnitude c :=
    Rat.lt_of_le_of_ne (magnitude_nonneg c) (Ne.symm hcNe)
  have h1 : magnitude b * magnitude d <= magnitude b * magnitude c :=
    Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hCD) hb
  have h2 : magnitude b * magnitude c < magnitude a * magnitude c :=
    Rat.mul_lt_mul_of_pos_right hAB hcPos
  apply Rat.lt_of_le_of_ne (Rat.le_trans h1 (Rat.le_of_lt h2))
  intro heq
  have hle : magnitude a * magnitude c <= magnitude b * magnitude c := by
    rw [← heq]
    exact h1
  exact (Rat.not_lt.mpr hle) h2

theorem magnitude_mul_eq_of_eq_eq {a b c d : ArithValue}
    (hAB : magnitude a = magnitude b)
    (hCD : magnitude c = magnitude d)
    (hAC : kind a = kind c)
    (hABK : kind a = kind b)
    (hCDK : kind c = kind d) :
    magnitude (mul a c) = magnitude (mul b d) := by
  rw [magnitude_mul_of_same_kind hAC,
    magnitude_mul_of_same_kind (hABK.symm.trans hAC |>.trans hCDK), hAB, hCD]

theorem magnitude_mul_lt_mul_of_lt_eq_pos {a b c d : ArithValue}
    (hAB : magnitude b < magnitude a)
    (hCD : magnitude c = magnitude d)
    (hPos : 0 < magnitude c)
    (hAC : kind a = kind c)
    (hABK : kind a = kind b)
    (hCDK : kind c = kind d) :
    magnitude (mul b d) < magnitude (mul a c) := by
  rw [magnitude_mul_of_same_kind (hABK.symm.trans hAC |>.trans hCDK),
    magnitude_mul_of_same_kind hAC, ← hCD]
  exact Rat.mul_lt_mul_of_pos_right hAB hPos

end ArithValue

/- Superseded option representation of arithmetic products.
/-- A product can become ill-typed when integer and real factor lists are joined. -/
abbrev ArithProduct := Option ArithValue

namespace ArithProduct

def mul : ArithProduct -> ArithProduct -> ArithProduct
  | some a, some b =>
      if ArithValue.kind a = ArithValue.kind b then
        some (ArithValue.mul a b)
      else
        none
  | _, _ => none

def smtType : ArithProduct -> SmtType
  | some a => a.smtType
  | none => SmtType.None

def eoType : ArithProduct -> Term
  | some a => a.eoType
  | none => Term.Stuck

def smtValue : ArithProduct -> SmtValue
  | some a => a.smtValue
  | none => SmtValue.NotValue

def Greater : ArithProduct -> ArithProduct -> Prop
  | some a, some b =>
      ArithValue.kind a = ArithValue.kind b ∧
        ArithValue.magnitude b < ArithValue.magnitude a
  | _, _ => True

def EqualMagnitude : ArithProduct -> ArithProduct -> Prop
  | some a, some b =>
      ArithValue.kind a = ArithValue.kind b ∧
        ArithValue.magnitude a = ArithValue.magnitude b
  | _, _ => True

def Positive : ArithProduct -> Prop
  | some a => 0 < ArithValue.magnitude a
  | none => True

theorem mul_assoc (a b c : ArithProduct) :
    mul (mul a b) c = mul a (mul b c) := by
  cases a with
  | none => simp [mul]
  | some a =>
      cases b with
      | none => simp [mul]
      | some b =>
          cases c with
          | none => simp [mul]
          | some c =>
              cases a <;> cases b <;> cases c <;>
                simp [mul, ArithValue.kind, ArithValue.mul, Int.mul_assoc,
                  Rat.mul_assoc]

theorem smtType_mul (a b : ArithProduct) :
    __smtx_typeof_arith_overload_op_2 a.smtType b.smtType =
      (mul a b).smtType := by
  cases a with
  | none => simp [smtType, mul, __smtx_typeof_arith_overload_op_2]
  | some a =>
      cases b with
      | none => simp [smtType, mul, __smtx_typeof_arith_overload_op_2]
      | some b =>
          cases a <;> cases b <;>
            simp [smtType, mul, ArithValue.smtType, ArithValue.kind,
              ArithValue.mul, __smtx_typeof_arith_overload_op_2]

theorem modelEval_mul (a b : ArithProduct) :
    __smtx_model_eval_mult a.smtValue b.smtValue = (mul a b).smtValue := by
  cases a with
  | none => simp [smtValue, mul, __smtx_model_eval_mult]
  | some a =>
      cases b with
      | none => simp [smtValue, mul, __smtx_model_eval_mult]
      | some b =>
          cases a <;> cases b <;>
            simp [smtValue, mul, ArithValue.smtValue, ArithValue.kind,
              ArithValue.mul, __smtx_model_eval_mult, native_zmult, native_qmult]

theorem greater_mul (a b c d : ArithProduct)
    (hAB : Greater a b) (hCD : Greater c d) :
    Greater (mul a c) (mul b d) := by
  cases a with
  | none => simp [mul, Greater]
  | some a =>
      cases b with
      | none => simp [mul, Greater]
      | some b =>
          cases c with
          | none => simp [mul, Greater]
          | some c =>
              cases d with
              | none => simp [mul, Greater]
              | some d =>
                  rcases hAB with ⟨hABK, hAB⟩
                  rcases hCD with ⟨hCDK, hCD⟩
                  by_cases hAC : a.kind = c.kind
                  · have hBD : b.kind = d.kind := hABK.symm.trans hAC |>.trans hCDK
                    simp only [mul, hAC, hBD, ite_eq_left, Greater]
                    exact ⟨(ArithValue.kind_mul_of_same_kind hAC).trans
                        (hABK.trans (ArithValue.kind_mul_of_same_kind hBD).symm),
                      ArithValue.magnitude_mul_lt_mul_of_lt_lt
                        hAB hCD hAC hABK hCDK⟩
                  · have hBD : b.kind ≠ d.kind := by
                      intro h
                      exact hAC (hABK.trans h |>.trans hCDK.symm)
                    simp [mul, hAC, hBD, Greater]

theorem equalMagnitude_mul (a b c d : ArithProduct)
    (hAB : EqualMagnitude a b) (hCD : EqualMagnitude c d) :
    EqualMagnitude (mul a c) (mul b d) := by
  cases a with
  | none => simp [mul, EqualMagnitude]
  | some a =>
      cases b with
      | none => simp [mul, EqualMagnitude]
      | some b =>
          cases c with
          | none => simp [mul, EqualMagnitude]
          | some c =>
              cases d with
              | none => simp [mul, EqualMagnitude]
              | some d =>
                  rcases hAB with ⟨hABK, hAB⟩
                  rcases hCD with ⟨hCDK, hCD⟩
                  by_cases hAC : a.kind = c.kind
                  · have hBD : b.kind = d.kind := hABK.symm.trans hAC |>.trans hCDK
                    simp only [mul, hAC, hBD, ite_eq_left, EqualMagnitude]
                    exact ⟨(ArithValue.kind_mul_of_same_kind hAC).trans
                        (hABK.trans (ArithValue.kind_mul_of_same_kind hBD).symm),
                      ArithValue.magnitude_mul_eq_of_eq_eq
                        hAB hCD hAC hABK hCDK⟩
                  · have hBD : b.kind ≠ d.kind := by
                      intro h
                      exact hAC (hABK.trans h |>.trans hCDK.symm)
                    simp [mul, hAC, hBD, EqualMagnitude]

theorem greater_mul_equalMagnitude (a b c d : ArithProduct)
    (hAB : Greater a b) (hCD : EqualMagnitude c d) (hPos : Positive c) :
    Greater (mul a c) (mul b d) := by
  cases a with
  | none => simp [mul, Greater]
  | some a =>
      cases b with
      | none => simp [mul, Greater]
      | some b =>
          cases c with
          | none => simp [mul, Greater]
          | some c =>
              cases d with
              | none => simp [mul, Greater]
              | some d =>
                  rcases hAB with ⟨hABK, hAB⟩
                  rcases hCD with ⟨hCDK, hCD⟩
                  by_cases hAC : a.kind = c.kind
                  · have hBD : b.kind = d.kind := hABK.symm.trans hAC |>.trans hCDK
                    simp only [mul, hAC, hBD, ite_eq_left, Greater]
                    exact ⟨(ArithValue.kind_mul_of_same_kind hAC).trans
                        (hABK.trans (ArithValue.kind_mul_of_same_kind hBD).symm),
                      ArithValue.magnitude_mul_lt_mul_of_lt_eq_pos
                        hAB hCD hPos hAC hABK hCDK⟩
                  · have hBD : b.kind ≠ d.kind := by
                      intro h
                      exact hAC (hABK.trans h |>.trans hCDK.symm)
                    simp [mul, hAC, hBD, Greater]

end ArithProduct
-/

/- Superseded aggregate-product experiment.
/-- A multiplication list is empty at a typed identity, has a typed value, or is
    permanently invalid after unlike arithmetic sorts are concatenated. -/
inductive ArithProduct where
  | empty (kind : ArithKind)
  | value (value : ArithValue)
  | invalid

namespace ArithProduct

def append : ArithProduct -> ArithProduct -> ArithProduct
  | .empty _, b => b
  | .invalid, _ => .invalid
  | .value _, .invalid => .invalid
  | .value a, .empty k =>
      if a.kind = k then .value a else .invalid
  | .value a, .value b =>
      if a.kind = b.kind then .value (a.mul b) else .invalid

def smtType : ArithProduct -> SmtType
  | .empty .int => SmtType.Int
  | .empty .real => SmtType.Real
  | .value a => a.smtType
  | .invalid => SmtType.None

def eoType : ArithProduct -> Term
  | .empty .int => Term.Int
  | .empty .real => Term.Real
  | .value a => a.eoType
  | .invalid => Term.Stuck

def smtValue : ArithProduct -> SmtValue
  | .empty .int => SmtValue.Numeral 1
  | .empty .real => SmtValue.Rational 1
  | .value a => a.smtValue
  | .invalid => SmtValue.NotValue

def Greater : ArithProduct -> ArithProduct -> Prop
  | .invalid, _ | _, .invalid => True
  | .value a, .value b => a.kind = b.kind ∧ b.magnitude < a.magnitude
  | _, _ => False

def EqualMagnitude : ArithProduct -> ArithProduct -> Prop
  | .invalid, _ | _, .invalid => True
  | .value a, .value b => a.kind = b.kind ∧ a.magnitude = b.magnitude
  | _, _ => False

def Positive : ArithProduct -> Prop
  | .invalid => True
  | .value a => 0 < a.magnitude
  | .empty _ => False

@[simp] theorem append_invalid_right (a : ArithProduct) :
    append a .invalid = .invalid := by
  cases a <;> simp [append]

@[simp] theorem greater_invalid_left (a : ArithProduct) :
    Greater .invalid a := by
  cases a <;> simp [Greater]

@[simp] theorem greater_invalid_right (a : ArithProduct) :
    Greater a .invalid := by
  cases a <;> simp [Greater]

@[simp] theorem equalMagnitude_invalid_left (a : ArithProduct) :
    EqualMagnitude .invalid a := by
  cases a <;> simp [EqualMagnitude]

@[simp] theorem equalMagnitude_invalid_right (a : ArithProduct) :
    EqualMagnitude a .invalid := by
  cases a <;> simp [EqualMagnitude]

theorem append_assoc (a b c : ArithProduct) :
    append (append a b) c = append a (append b c) := by
  grind [append, ArithValue.kind, ArithValue.mul, Int.mul_assoc, Rat.mul_assoc]

theorem smtType_cons (a : ArithValue) (b : ArithProduct) :
    __smtx_typeof_arith_overload_op_2 a.smtType b.smtType =
      (append (.value a) b).smtType := by
  cases b with
  | invalid =>
      cases a <;> simp [append, smtType, ArithValue.smtType,
        __smtx_typeof_arith_overload_op_2]
  | empty k =>
      cases a <;> cases k <;> simp [append, smtType, ArithValue.kind,
        ArithValue.smtType, __smtx_typeof_arith_overload_op_2]
  | value b =>
      cases a <;> cases b <;> simp [append, smtType, ArithValue.kind,
        ArithValue.smtType, ArithValue.mul,
        __smtx_typeof_arith_overload_op_2]

theorem modelEval_cons (a : ArithValue) (b : ArithProduct) :
    __smtx_model_eval_mult a.smtValue b.smtValue =
      (append (.value a) b).smtValue := by
  cases b with
  | invalid =>
      cases a <;> simp [append, smtValue, ArithValue.smtValue,
        __smtx_model_eval_mult]
  | empty k =>
      cases a <;> cases k <;> simp [append, smtValue, ArithValue.kind,
        ArithValue.smtValue, ArithValue.mul, __smtx_model_eval_mult,
        native_zmult, native_qmult]
  | value b =>
      cases a <;> cases b <;> simp [append, smtValue, ArithValue.kind,
        ArithValue.smtValue, ArithValue.mul, __smtx_model_eval_mult,
        native_zmult, native_qmult]

theorem greater_append (a b c d : ArithProduct)
    (hAB : Greater a b) (hCD : Greater c d) :
    Greater (append a c) (append b d) := by
  cases a with
  | empty k => cases b <;> simp [append, Greater] at hAB ⊢
  | invalid => simp [append, Greater]
  | value a =>
      cases b with
      | empty k => simp [Greater] at hAB
      | invalid => simp
      | value b =>
          cases c with
          | empty k => cases d <;> simp [append, Greater] at hCD ⊢
          | invalid => simp [append, Greater]
          | value c =>
              cases d with
              | empty k => simp [Greater] at hCD
              | invalid => simp
              | value d =>
                  rcases hAB with ⟨hABK, hAB⟩
                  rcases hCD with ⟨hCDK, hCD⟩
                  by_cases hAC : a.kind = c.kind
                  · have hBD : b.kind = d.kind := hABK.symm.trans hAC |>.trans hCDK
                    simp only [append, hAC, hBD, ite_eq_left, Greater]
                    exact ⟨(ArithValue.kind_mul_of_same_kind hAC).trans
                        (hABK.trans (ArithValue.kind_mul_of_same_kind hBD).symm),
                      ArithValue.magnitude_mul_lt_mul_of_lt_lt
                        hAB hCD hAC hABK hCDK⟩
                  · have hBD : b.kind ≠ d.kind := by
                      intro h
                      exact hAC (hABK.trans h |>.trans hCDK.symm)
                    simp [append, hAC, hBD, Greater]

theorem equalMagnitude_append (a b c d : ArithProduct)
    (hAB : EqualMagnitude a b) (hCD : EqualMagnitude c d) :
    EqualMagnitude (append a c) (append b d) := by
  cases a with
  | empty k => cases b <;> simp [append, EqualMagnitude] at hAB ⊢
  | invalid => simp [append, EqualMagnitude]
  | value a =>
      cases b with
      | empty k => simp [EqualMagnitude] at hAB
      | invalid => simp
      | value b =>
          cases c with
          | empty k => cases d <;> simp [append, EqualMagnitude] at hCD ⊢
          | invalid => simp [append, EqualMagnitude]
          | value c =>
              cases d with
              | empty k => simp [EqualMagnitude] at hCD
              | invalid => simp
              | value d =>
                  rcases hAB with ⟨hABK, hAB⟩
                  rcases hCD with ⟨hCDK, hCD⟩
                  by_cases hAC : a.kind = c.kind
                  · have hBD : b.kind = d.kind := hABK.symm.trans hAC |>.trans hCDK
                    simp only [append, hAC, hBD, ite_eq_left, EqualMagnitude]
                    exact ⟨(ArithValue.kind_mul_of_same_kind hAC).trans
                        (hABK.trans (ArithValue.kind_mul_of_same_kind hBD).symm),
                      ArithValue.magnitude_mul_eq_of_eq_eq
                        hAB hCD hAC hABK hCDK⟩
                  · have hBD : b.kind ≠ d.kind := by
                      intro h
                      exact hAC (hABK.trans h |>.trans hCDK.symm)
                    simp [append, hAC, hBD, EqualMagnitude]

theorem greater_append_equalMagnitude (a b c d : ArithProduct)
    (hAB : Greater a b) (hCD : EqualMagnitude c d) (hPos : Positive c) :
    Greater (append a c) (append b d) := by
  cases a with
  | empty k => cases b <;> simp [append, Greater] at hAB ⊢
  | invalid => simp [append, Greater]
  | value a =>
      cases b with
      | empty k => simp [Greater] at hAB
      | invalid => simp
      | value b =>
          cases c with
          | empty k => simp [Positive] at hPos
          | invalid => simp [append, Greater]
          | value c =>
              cases d with
              | empty k => simp [EqualMagnitude] at hCD
              | invalid => simp
              | value d =>
                  rcases hAB with ⟨hABK, hAB⟩
                  rcases hCD with ⟨hCDK, hCD⟩
                  by_cases hAC : a.kind = c.kind
                  · have hBD : b.kind = d.kind := hABK.symm.trans hAC |>.trans hCDK
                    simp only [append, hAC, hBD, ite_eq_left, Greater]
                    exact ⟨(ArithValue.kind_mul_of_same_kind hAC).trans
                        (hABK.trans (ArithValue.kind_mul_of_same_kind hBD).symm),
                      ArithValue.magnitude_mul_lt_mul_of_lt_eq_pos
                        hAB hCD hPos hAC hABK hCDK⟩
                  · have hBD : b.kind ≠ d.kind := by
                      intro h
                      exact hAC (hABK.trans h |>.trans hCDK.symm)
                    simp [append, hAC, hBD, Greater]

end ArithProduct
-/
end ArithValueSupport
