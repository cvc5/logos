module

public import Cpc.Logos
import all Cpc.Logos

public section

/-!
Checker-side invariants for `quant_var_elim_ineq`: normalization has no zero
coefficients, accepted polynomials are affine, and accepted literal directions
remain compatible throughout elimination. The rational bounds here are used
to choose a single integer assignment that falsifies all removed literals.
-/

open Eo SmtEval

set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

namespace QuantVarElimIneq

abbrev mon (a : Term) (c : Rat) : Term :=
  ((Term.UOp UserOp._at__at_mon).Apply a).Apply (Term.Rational c)
abbrev poly (a : Term) (c : Rat) (p : Term) : Term :=
  ((Term.UOp UserOp._at__at_poly).Apply (mon a c)).Apply p
abbrev zero : Term := Term.UOp UserOp._at__at_poly_zero

/-- Normalization either fails or produces a polynomial with no zero coefficients.
This invariant rules out treating a zero coefficient as a positive direction. -/
inductive NonzeroCoeffs : Term → Prop where
  | stuck : NonzeroCoeffs Term.Stuck
  | zero : NonzeroCoeffs zero
  | cons (a : Term) (c : Rat) (p : Term) :
      c ≠ 0 → NonzeroCoeffs p → NonzeroCoeffs (poly a c p)

theorem nonzeroCoeffs_neg {p : Term} (h : NonzeroCoeffs p) :
    NonzeroCoeffs (__poly_neg p) := by
  induction h with
  | stuck => exact .stuck
  | zero => exact .zero
  | cons a c p hc hp ih =>
      by_cases ht : __poly_neg p = Term.Stuck
      · simpa [poly, mon, __poly_neg, __eo_mk_apply, __eo_neg, ht] using
          NonzeroCoeffs.stuck
      · have hneg : -c ≠ 0 := by
          intro hzero
          apply hc
          have := congrArg Neg.neg hzero
          simpa only [Rat.neg_neg, Rat.neg_zero] using this
        simpa [poly, mon, __poly_neg, __eo_mk_apply, __eo_neg, ht,
          native_qneg] using
          NonzeroCoeffs.cons a (-c) (__poly_neg p) hneg ih

theorem nonzeroCoeffs_prepend (a : Term) (c : Rat) (p : Term)
    (hc : c ≠ 0) (hp : NonzeroCoeffs p) :
    NonzeroCoeffs (__eo_mk_apply ((Term.UOp UserOp._at__at_poly).Apply (mon a c)) p) := by
  by_cases h : p = Term.Stuck
  · simp [h, __eo_mk_apply, NonzeroCoeffs.stuck]
  · simpa [__eo_mk_apply, h] using NonzeroCoeffs.cons a c p hc hp

theorem ratZero : native_mk_rational 0 1 = (0 : Rat) := by native_decide

theorem nonzeroCoeffs_add {p q : Term} (hp : NonzeroCoeffs p) (hq : NonzeroCoeffs q) :
    NonzeroCoeffs (__poly_add p q) := by
  cases hp with
  | stuck => simpa [__poly_add, zero, poly, mon] using NonzeroCoeffs.stuck
  | zero =>
      cases hq with
      | stuck => simpa [__poly_add, zero, poly, mon] using NonzeroCoeffs.stuck
      | zero => simpa [__poly_add, zero] using NonzeroCoeffs.zero
      | cons b d q hd hq => simpa [__poly_add, zero, poly, mon] using NonzeroCoeffs.cons b d q hd hq
  | cons a c p hc hp =>
      cases hq with
      | stuck => simpa [__poly_add, zero, poly, mon] using NonzeroCoeffs.stuck
      | zero => simpa [__poly_add, zero, poly, mon] using NonzeroCoeffs.cons a c p hc hp
      | cons b d q hd hq =>
          rw [__poly_add.eq_def]
          dsimp only [poly, mon]
          by_cases ha : a = Term.Stuck
          · subst a
            simpa [__eo_eq, __eo_ite, native_ite, native_teq] using NonzeroCoeffs.stuck
          · by_cases hb : b = Term.Stuck
            · subst b
              simpa [__eo_eq, __eo_ite, native_ite, native_teq] using NonzeroCoeffs.stuck
            · by_cases hab : a = b
              · subst b
                have hr := nonzeroCoeffs_add hp hq
                by_cases hcd : c + d = 0
                · simpa [__eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                    ha, native_qplus, ratZero, hcd] using hr
                · have hh := nonzeroCoeffs_prepend a (c + d) (__poly_add p q) hcd hr
                  simpa [__eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                    ha, native_qplus, ratZero, hcd, __eo_mk_apply, eq_comm] using hh
              · by_cases hcmp : native_tcmp b a = true
                · have hr := nonzeroCoeffs_add hp (NonzeroCoeffs.cons b d q hd hq)
                  have hh := nonzeroCoeffs_prepend a c (__poly_add p (poly b d q)) hc hr
                  simpa [__eo_eq, __eo_ite, __eo_cmp, native_ite, native_teq,
                    ha, hb, hab, hcmp, eq_comm, poly, mon] using hh
                · have hr := nonzeroCoeffs_add (NonzeroCoeffs.cons a c p hc hp) hq
                  have hh := nonzeroCoeffs_prepend b d (__poly_add (poly a c p) q) hd hr
                  simpa [__eo_eq, __eo_ite, __eo_cmp, native_ite, native_teq,
                    ha, hb, hab, hcmp, eq_comm, poly, mon] using hh
termination_by sizeOf p + sizeOf q

theorem nonzeroCoeffs_mul_mon (a : Term) (c : Rat) (hc : c ≠ 0)
    {p : Term} (hp : NonzeroCoeffs p) :
    NonzeroCoeffs (__poly_mul_mon (mon a c) p) := by
  induction hp with
  | stuck => simpa [__poly_mul_mon, mon] using NonzeroCoeffs.stuck
  | zero => simpa [__poly_mul_mon, mon, zero] using NonzeroCoeffs.zero
  | cons b d p hd hp ih =>
      rw [__poly_mul_mon.eq_def]
      dsimp only [poly, mon]
      apply nonzeroCoeffs_add _ ih
      have hcd : c * d ≠ 0 := by
        intro h
        rcases Rat.mul_eq_zero.mp h with h | h
        · exact hc h
        · exact hd h
      by_cases hm : __mvar_mul_mvar a b = Term.Stuck
      · simpa [__mon_mul_mon, __eo_mk_apply, __eo_mul, hm] using NonzeroCoeffs.stuck
      · simpa [__mon_mul_mon, __eo_mk_apply, __eo_mul, hm, native_qmult] using
          NonzeroCoeffs.cons (__mvar_mul_mvar a b) (c * d) zero hcd NonzeroCoeffs.zero

theorem nonzeroCoeffs_mul {p q : Term} (hp : NonzeroCoeffs p) (hq : NonzeroCoeffs q) :
    NonzeroCoeffs (__poly_mul p q) := by
  induction hp with
  | stuck => simpa [__poly_mul] using NonzeroCoeffs.stuck
  | zero =>
      cases hq with
      | stuck => simpa [__poly_mul, zero] using NonzeroCoeffs.stuck
      | zero => simpa [__poly_mul, zero] using NonzeroCoeffs.zero
      | cons a c p hc hp => simpa [__poly_mul, poly, mon, zero] using NonzeroCoeffs.zero
  | cons a c p hc hp ih =>
      by_cases hq0 : q = Term.Stuck
      · simp [hq0, poly, mon, __poly_mul, NonzeroCoeffs.stuck]
      · simpa [__poly_mul, poly, mon, hq0] using
          nonzeroCoeffs_add (nonzeroCoeffs_mul_mon a c hc hq) ih

theorem ratOne : native_mk_rational 1 1 = (1 : Rat) := by native_decide

abbrev single (a : Term) : Term := (Term.__eo_List_cons.Apply a).Apply Term.__eo_List_nil
abbrev atomic (a : Term) : Term := poly (single a) 1 zero

theorem nonzeroCoeffs_atomic (a : Term) : NonzeroCoeffs (atomic a) :=
  .cons _ _ _ (by decide) .zero

theorem to_q_cases (a : Term) :
    __eo_to_q a = Term.Stuck ∨ ∃ c : Rat, __eo_to_q a = Term.Rational c := by
  cases a <;> simp [__eo_to_q]

abbrev divideNorm (p t b : Term) : Term :=
  let q := __eo_to_q b
  __eo_ite (__eo_ite (__eo_is_q q)
      (__eo_not (__eo_eq q (Term.Rational (native_mk_rational 0 1)))) (Term.Boolean false))
    (__poly_mul_mon
      (__eo_mk_apply ((Term.UOp UserOp._at__at_mon).Apply Term.__eo_List_nil)
        (__eo_qdiv (Term.Rational (native_mk_rational 1 1)) q)) p)
    (poly (single t) (native_mk_rational 1 1) zero)

theorem nonzeroCoeffs_divideNorm {p : Term} (hp : NonzeroCoeffs p) (t b : Term) :
    NonzeroCoeffs (divideNorm p t b) := by
  rcases to_q_cases b with hb | ⟨c, hb⟩
  · simpa [divideNorm, hb, __eo_is_q, __eo_is_q_internal, __eo_ite, __eo_not,
      __eo_eq, native_ite, native_teq, native_not, native_and, ratOne] using
      nonzeroCoeffs_atomic t
  · by_cases hc : c = 0
    · subst c
      simpa [divideNorm, hb, __eo_is_q, __eo_is_q_internal, __eo_ite, __eo_not,
        __eo_eq, native_ite, native_teq, native_not, native_and, ratOne, ratZero] using
        nonzeroCoeffs_atomic t
    · have hdiv : (1 : Rat) / c ≠ 0 := by
        intro h
        have heq := Rat.div_mul_cancel (a := (1 : Rat)) hc
        rw [h, Rat.zero_mul] at heq
        exact (by decide : (0 : Rat) ≠ 1) heq
      have hr := nonzeroCoeffs_mul_mon Term.__eo_List_nil ((1 : Rat) / c) hdiv hp
      simpa [divideNorm, hb, __eo_is_q, __eo_is_q_internal, __eo_ite, __eo_not,
        __eo_eq, __eo_qdiv, __eo_mk_apply, native_ite, native_teq, native_not,
        native_and, native_qeq, native_qdiv_total, ratOne, ratZero, hc, eq_comm, mon] using hr

abbrev constantOrAtomic (a : Term) : Term :=
  let q := __eo_to_q a
  __eo_ite (__eo_is_q q)
    (__eo_ite (__eo_is_eq q (Term.Rational (native_mk_rational 0 1))) zero
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
        (__eo_mk_apply ((Term.UOp UserOp._at__at_mon).Apply Term.__eo_List_nil) q)) zero))
    (poly (single a) (native_mk_rational 1 1) zero)

theorem nonzeroCoeffs_constantOrAtomic (a : Term) :
    NonzeroCoeffs (constantOrAtomic a) := by
  rcases to_q_cases a with ha | ⟨c, ha⟩
  · simpa [constantOrAtomic, ha, __eo_is_q, __eo_is_q_internal, __eo_ite,
      native_ite, native_teq, native_not, native_and, ratOne] using nonzeroCoeffs_atomic a
  · by_cases hc : c = 0
    · subst c
      simpa [constantOrAtomic, ha, __eo_is_q, __eo_is_q_internal, __eo_ite,
        __eo_is_eq, native_ite, native_teq, native_not, native_and, ratZero] using
        NonzeroCoeffs.zero
    · simpa [constantOrAtomic, ha, __eo_is_q, __eo_is_q_internal, __eo_ite,
        __eo_is_eq, __eo_mk_apply, native_ite, native_teq, native_not, native_and,
        ratZero, hc, eq_comm, zero, poly, mon] using
        NonzeroCoeffs.cons Term.__eo_List_nil c zero hc NonzeroCoeffs.zero

theorem nonzeroCoeffs_norm (t : Term) : NonzeroCoeffs (__get_arith_poly_norm t) := by
  induction t using __get_arith_poly_norm.induct with
  | case1 => simpa [__get_arith_poly_norm] using NonzeroCoeffs.stuck
  | case2 a ih => simpa [__get_arith_poly_norm] using nonzeroCoeffs_neg ih
  | case3 a b iha ihb => simpa [__get_arith_poly_norm] using nonzeroCoeffs_add iha ihb
  | case4 a b iha ihb => simpa [__get_arith_poly_norm] using nonzeroCoeffs_add iha (nonzeroCoeffs_neg ihb)
  | case5 a b iha ihb => simpa [__get_arith_poly_norm] using nonzeroCoeffs_mul iha ihb
  | case6 a b ih =>
      simpa only [__get_arith_poly_norm, divideNorm, poly, single, mon, zero] using
        nonzeroCoeffs_divideNorm ih (((Term.UOp UserOp.qdiv).Apply a).Apply b) b
  | case7 a b ih =>
      simpa only [__get_arith_poly_norm, divideNorm, poly, single, mon, zero] using
        nonzeroCoeffs_divideNorm ih (((Term.UOp UserOp.qdiv_total).Apply a).Apply b) b
  | case8 a ih => simpa [__get_arith_poly_norm] using ih
  | case9 a h1 h2 h3 h4 h5 h6 h7 h8 =>
      rw [__get_arith_poly_norm.eq_def]
      split <;> first | solve_by_elim | exact nonzeroCoeffs_constantOrAtomic _

/-- A polynomial has exactly one linear occurrence of the eliminated variable;
all factors before and after that occurrence are independent of it. -/
inductive LinearPart (x : Term) : Term → Rat → Prop where
  | head (c : Rat) (p : Term) :
      __poly_contains_atomic_term_free p x = Term.Boolean false →
      LinearPart x (poly (single x) c p) c
  | skip (a : Term) (b : Rat) (p : Term) (c : Rat) :
      __contains_atomic_term_list_free_rec a (single x) Term.__eo_List_nil = Term.Boolean false →
      LinearPart x p c → LinearPart x (poly a b p) c

theorem requires_facts {a b v r : Term} (h : __eo_requires a b v = r)
    (hr : r ≠ Term.Stuck) : a = b ∧ v = r := by
  by_cases hab : a = b
  · subst b
    by_cases hs : a = Term.Stuck
    · have hbad : Term.Stuck = r := by
        simpa [__eo_requires, hs, native_ite, native_teq, native_not] using h
      exact False.elim (hr hbad.symm)
    · refine ⟨rfl, ?_⟩
      simpa [__eo_requires, native_ite, native_teq, native_not, hs] using h
  · have hbad : Term.Stuck = r := by
      simpa [__eo_requires, native_ite, native_teq, native_not, hab] using h
    exact False.elim (hr hbad.symm)

theorem linear_dir_nonzero {x p : Term} (hx : x ≠ Term.Stuck)
    (hp : NonzeroCoeffs p) (d : Int) (hd : __arith_linear_dir x p = Term.Numeral d) :
    ∃ c : Rat, c ≠ 0 ∧ LinearPart x p c ∧ d = if c < 0 then -1 else 1 := by
  induction hp with
  | stuck => simp [__arith_linear_dir] at hd
  | zero => simp [__arith_linear_dir, __eo_l_1___arith_linear_dir, zero] at hd
  | cons a c p hc hp ih =>
      have hFallback :
          __eo_l_1___arith_linear_dir x (poly a c p) =
            __eo_requires
              (__contains_atomic_term_list_free_rec a (single x) Term.__eo_List_nil)
              (Term.Boolean false) (__arith_linear_dir x p) := by
        simp [__eo_l_1___arith_linear_dir, poly, mon, single, hx]
      have finishFallback
          (h : __eo_l_1___arith_linear_dir x (poly a c p) = Term.Numeral d) :
          ∃ c' : Rat, c' ≠ 0 ∧ LinearPart x (poly a c p) c' ∧
            d = if c' < 0 then -1 else 1 := by
        rw [hFallback] at h
        obtain ⟨hfree, htail⟩ := requires_facts h (by simp)
        obtain ⟨c', hc', hl, hd'⟩ := ih htail
        exact ⟨c', hc', .skip a c p c' hfree hl, hd'⟩
      rw [__arith_linear_dir.eq_def] at hd
      split at hd
      · contradiction
      · contradiction
      · rename_i x x1 x2 y c' p' hx' hshape
        have hshape' : a = single y ∧ Term.Rational c = c' ∧ p = p' := by
          simpa [poly, mon, single, and_assoc] using hshape
        rcases hshape' with ⟨rfl, rfl, rfl⟩
        by_cases heq : x = y
        · subst y
          have heqtrue : __eo_eq x x = Term.Boolean true := by
            simp [__eo_eq, hx, native_teq]
          simp only [heqtrue, __eo_ite, native_ite, native_teq, ↓reduceIte, decide_true,
            decide_false] at hd
          obtain ⟨hfree, hdir⟩ := requires_facts hd (by simp)
          refine ⟨c, hc, ?_, ?_⟩
          · exact .head c p hfree
          · simp [__eo_ite, __eo_is_neg, native_qlt, ratZero, native_ite, native_teq] at hdir
            split at hdir <;> simp_all
        · have heqfalse : __eo_eq x y = Term.Boolean false ∨ y = Term.Stuck := by
            by_cases hy : y = Term.Stuck
            · exact Or.inr hy
            · exact Or.inl (by simp [__eo_eq, hx, hy, native_teq, heq, eq_comm])
          rcases heqfalse with heqfalse | rfl
          · simp only [heqfalse, __eo_ite, native_ite, native_teq, ↓reduceIte,
              decide_true, decide_false] at hd
            exact finishFallback hd
          · simp [__eo_eq, __eo_ite, native_ite, native_teq] at hd
      · exact finishFallback hd

/-- A positive affine slope eventually dominates any constant offset, even
when the variable is restricted to integer values. -/
theorem affine_eventually_pos (a b : Rat) (ha : 0 < a) :
    ∃ B : Int, ∀ n : Int, B ≤ n → 0 < a * (n : Rat) + b := by
  refine ⟨(-b / a).floor + 1, ?_⟩
  intro n hn
  have hbound : -b / a < (n : Rat) :=
    Rat.not_le.mp (fun h => (Rat.not_le.mpr (Rat.lt_floor_add_one _))
      (Rat.le_trans (Rat.intCast_le_intCast.mpr hn) h))
  have hmul : -b < a * (n : Rat) := (Rat.div_lt_iff' ha).mp hbound
  have hsum := (Rat.add_lt_add_right (c := b)).mpr hmul
  simpa only [Rat.neg_add_cancel] using hsum

theorem affine_eventually_ne (a b : Rat) (ha : a ≠ 0) :
    ∃ B : Int, ∀ n : Int, B ≤ n → a * (n : Rat) + b ≠ 0 := by
  by_cases hpos : 0 < a
  · obtain ⟨B, hB⟩ := affine_eventually_pos a b hpos
    exact ⟨B, fun n hn => Rat.ne_of_gt (hB n hn)⟩
  · have hneg : a < 0 := Rat.lt_of_le_of_ne (Rat.not_lt.mp hpos) ha
    obtain ⟨B, hB⟩ := affine_eventually_pos (-a) (-b) (by simpa only [Rat.neg_zero] using Rat.neg_lt_neg hneg)
    refine ⟨B, fun n hn heq => ?_⟩
    have hp := hB n hn
    have hzero : -a * (n : Rat) + -b = 0 := by
      rw [Rat.neg_mul, ← Rat.neg_add, heq, Rat.neg_zero]
    rw [hzero] at hp
    exact Rat.lt_irrefl hp

private theorem native_ite_prop {P : Term → Prop} (c : Bool) {a b : Term}
    (ha : P a) (hb : P b) : P (native_ite c a b) := by
  cases c <;> assumption

private theorem eo_ite_prop {P : Term → Prop} (c : Term) {a b : Term}
    (hs : P Term.Stuck) (ha : P a) (hb : P b) : P (__eo_ite c a b) := by
  unfold __eo_ite
  exact native_ite_prop _ ha (native_ite_prop _ hb hs)

private theorem requires_prop {P : Term → Prop} (a b : Term) {v : Term}
    (hs : P Term.Stuck) (hv : P v) : P (__eo_requires a b v) := by
  unfold __eo_requires
  exact native_ite_prop _ (native_ite_prop _ hv hs) hs

def IsSignResult (t : Term) : Prop :=
  t = Term.Stuck ∨ t = Term.Numeral (-1) ∨ t = Term.Numeral 1

theorem linear_dir_range (x p : Term) : IsSignResult (__arith_linear_dir x p) := by
  apply __arith_linear_dir.induct
    (motive1 := fun x p => IsSignResult (__eo_l_1___arith_linear_dir x p))
    (motive2 := fun x p => IsSignResult (__arith_linear_dir x p))
  · intro p
    simp [__eo_l_1___arith_linear_dir, IsSignResult]
  · intro x a c p hx ih
    simp only [__eo_l_1___arith_linear_dir, hx]
    exact requires_prop _ _ (Or.inl rfl) ih
  · intro x p hx hshape
    rw [__eo_l_1___arith_linear_dir.eq_def]
    split <;> first | solve_by_elim | exact Or.inl rfl
  · intro p
    simp [__arith_linear_dir, IsSignResult]
  · intro x hx
    simp [__arith_linear_dir, IsSignResult]
  · intro x y c p hx ih
    simp only [__arith_linear_dir, hx]
    apply eo_ite_prop _ (Or.inl rfl) _ ih
    apply requires_prop _ _ (Or.inl rfl)
    exact eo_ite_prop _ (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  · intro x p hx hp hshape ih
    rw [__arith_linear_dir.eq_def]
    split <;> first | solve_by_elim | exact ih

def IsDirection (d : Int) : Prop := d = -1 ∨ d = 0 ∨ d = 1

theorem literal_dir_range (x f : Term) :
    __get_quant_var_elim_ineq_dir x f = Term.Stuck ∨
      ∃ d : Int, __get_quant_var_elim_ineq_dir x f = Term.Numeral d ∧ IsDirection d := by
  have basic (p : Term) : __arith_linear_dir x p = Term.Stuck ∨
      ∃ d : Int, __arith_linear_dir x p = Term.Numeral d ∧ IsDirection d := by
    rcases linear_dir_range x p with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨-1, h, Or.inl rfl⟩
    · exact Or.inr ⟨1, h, Or.inr (Or.inr rfl)⟩
  have scaled (p : Term) : __eo_mul (Term.Numeral 0) (__arith_linear_dir x p) = Term.Stuck ∨
      ∃ d : Int, __eo_mul (Term.Numeral 0) (__arith_linear_dir x p) = Term.Numeral d ∧ IsDirection d := by
    rcases linear_dir_range x p with h | h | h
    · exact Or.inl (by simp [h, __eo_mul])
    · exact Or.inr ⟨0, by simp [h, __eo_mul, native_zmult], Or.inr (Or.inl rfl)⟩
    · exact Or.inr ⟨0, by simp [h, __eo_mul, native_zmult], Or.inr (Or.inl rfl)⟩
  rw [__get_quant_var_elim_ineq_dir.eq_def]
  split <;> first | exact Or.inl rfl | exact basic _ | exact scaled _

abbrev qor (a b : Term) : Term := ((Term.UOp UserOp.or).Apply a).Apply b

inductive Eliminates (x : Term) : Term → Term → Int → Int → Prop where
  | nil (d : Int) : Eliminates x (Term.Boolean false) (Term.Boolean false) d d
  | keep (f fs gs : Term) (d e : Int) :
      __contains_atomic_term_list_free_rec f (single x) Term.__eo_List_nil = Term.Boolean false →
      Eliminates x fs gs d e → Eliminates x (qor f fs) (qor f gs) d e
  | drop (f fs gs : Term) (d e k : Int) :
      __contains_atomic_term_list_free_rec f (single x) Term.__eo_List_nil = Term.Boolean true →
      __get_quant_var_elim_ineq_dir x f = Term.Numeral k → IsDirection k → d * k ≠ -1 →
      Eliminates x fs gs (if k = 0 then d else k) e → Eliminates x (qor f fs) gs d e

private theorem ite_facts {c a b r : Term} (h : __eo_ite c a b = r) (hr : r ≠ Term.Stuck) :
    (c = Term.Boolean true ∧ a = r) ∨ (c = Term.Boolean false ∧ b = r) := by
  by_cases ht : c = Term.Boolean true
  · exact Or.inl ⟨ht, by simpa [ht, __eo_ite, native_ite, native_teq] using h⟩
  · by_cases hf : c = Term.Boolean false
    · exact Or.inr ⟨hf, by simpa [hf, __eo_ite, native_ite, native_teq] using h⟩
    · have hbad : Term.Stuck = r := by
        simpa [__eo_ite, native_ite, native_teq, ht, hf] using h
      exact False.elim (hr hbad.symm)

private abbrev mkOr (x f fs : Term) (d : Int) : Term :=
  let k := __get_quant_var_elim_ineq_dir x f
  __eo_ite (__contains_atomic_term_list_free_rec f (single x) Term.__eo_List_nil)
    (__eo_requires (__eo_eq (__eo_mul (Term.Numeral d) k) (Term.Numeral (-1)))
      (Term.Boolean false)
      (__mk_quant_var_elim_ineq x fs (__eo_ite (__eo_eq k (Term.Numeral 0)) (Term.Numeral d) k)))
    (__eo_mk_apply ((Term.UOp UserOp.or).Apply f)
      (__mk_quant_var_elim_ineq x fs (Term.Numeral d)))

private theorem eliminates_or {x f fs G : Term} {d : Int}
    (hrec : ∀ (d' : Int) (G' : Term),
      __mk_quant_var_elim_ineq x fs (Term.Numeral d') = G' → G' ≠ Term.Stuck →
      ∃ e, Eliminates x fs G' d' e)
    (hmk : mkOr x f fs d = G) (hG : G ≠ Term.Stuck) :
    ∃ e, Eliminates x (qor f fs) G d e := by
  rcases ite_facts hmk hG with ⟨hf, hdrop⟩ | ⟨hf, hkeep⟩
  · obtain ⟨hcompat, htail⟩ := requires_facts hdrop hG
    rcases literal_dir_range x f with hbad | ⟨k, hk, hkRange⟩
    · simp [hbad, __eo_mul, __eo_eq] at hcompat
    · rw [hk] at hcompat htail
      have hdk : d * k ≠ -1 := by
        simpa [__eo_mul, __eo_eq, native_teq, native_zmult, eq_comm] using hcompat
      have hupdate : __eo_ite (__eo_eq (Term.Numeral k) (Term.Numeral 0))
          (Term.Numeral d) (Term.Numeral k) = Term.Numeral (if k = 0 then d else k) := by
        by_cases h : k = 0 <;> simp [__eo_ite, __eo_eq, native_ite, native_teq, h, eq_comm]
      rw [hupdate] at htail
      obtain ⟨e, he⟩ := hrec _ _ htail hG
      exact ⟨e, .drop f fs G d e k hf hk hkRange hdk he⟩
  · have ht : __mk_quant_var_elim_ineq x fs (Term.Numeral d) ≠ Term.Stuck := by
      intro ht
      have hbad : Term.Stuck = G := by simpa [ht, __eo_mk_apply] using hkeep
      exact hG hbad.symm
    obtain ⟨e, he⟩ := hrec d _ rfl ht
    have hresult : qor f (__mk_quant_var_elim_ineq x fs (Term.Numeral d)) = G := by
      simpa [__eo_mk_apply, ht] using hkeep
    rw [← hresult]
    exact ⟨e, .keep f fs _ d e hf he⟩

theorem mk_eliminates (x F : Term) (d : Int) (G : Term)
    (hx : x ≠ Term.Stuck)
    (hmk : __mk_quant_var_elim_ineq x F (Term.Numeral d) = G) (hG : G ≠ Term.Stuck) :
    ∃ e, Eliminates x F G d e := by
  rw [__mk_quant_var_elim_ineq.eq_def] at hmk
  split at hmk
  · contradiction
  · contradiction
  · apply eliminates_or _ hmk hG
    intro d' G' hmk' hG'
    apply mk_eliminates _ _ d' G' _ hmk' hG'
    assumption
  · subst G
    exact ⟨d, .nil d⟩
  · exact False.elim (hG hmk.symm)
termination_by sizeOf F

/-- The direction accumulated by the checker remains in its three-element range. -/
theorem Eliminates.final_direction {x F G : Term} {d e : Int}
    (h : Eliminates x F G d e) (hd : IsDirection d) : IsDirection e := by
  induction h with
  | nil => exact hd
  | keep _ _ _ _ _ _ _ ih => exact ih hd
  | drop _ _ _ d e k _ _ hk _ _ ih =>
      apply ih
      split <;> assumption

/-- A final choice of orientation is compatible with every earlier direction. -/
theorem compatible_previous {d k sign : Int}
    (hd : IsDirection d) (hk : IsDirection k) (hs : sign = -1 ∨ sign = 1)
    (hdk : d * k ≠ -1) (hnext : (if k = 0 then d else k) * sign ≠ -1) :
    d * sign ≠ -1 ∧ k * sign ≠ -1 := by
  rcases hd with rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl <;>
    rcases hs with rfl | rfl <;> simp_all

theorem compatible_slope {c : Rat} {d sign : Int} (hc : c ≠ 0)
    (hd : d = if c < 0 then -1 else 1) (hs : sign = -1 ∨ sign = 1)
    (hcompat : d * sign ≠ -1) : 0 < c * (sign : Rat) := by
  rcases hs with rfl | rfl
  · have hneg : c < 0 := by
      by_cases h : c < 0
      · exact h
      · simp [h] at hd
        subst d
        contradiction
    change 0 < c * (-1)
    rw [Rat.mul_neg, Rat.mul_one]
    simpa only [Rat.neg_zero] using Rat.neg_lt_neg hneg
  · have hnonneg : ¬c < 0 := by
      intro h
      simp [h] at hd
      subst d
      contradiction
    change 0 < c * 1
    rw [Rat.mul_one]
    exact Rat.lt_of_le_of_ne (Rat.not_lt.mp hnonneg) hc.symm

theorem Eliminates.initial_compatible {x F G : Term} {d e sign : Int}
    (h : Eliminates x F G d e) (hd : IsDirection d)
    (hs : sign = -1 ∨ sign = 1) (he : e * sign ≠ -1) : d * sign ≠ -1 := by
  induction h with
  | nil => exact he
  | keep _ _ _ _ _ _ _ ih => exact ih hd he
  | drop _ _ _ d e k _ _ hk hdk htail ih =>
      have hnext : IsDirection (if k = 0 then d else k) := by split <;> assumption
      exact (compatible_previous hd hk hs hdk (ih hnext he)).1

theorem LinearPart.two_atoms {x a b : Term} {c d k : Rat}
    (h : LinearPart x (poly (single a) c (poly (single b) d zero)) k) : x = a ∨ x = b := by
  cases h with
  | head => exact Or.inl rfl
  | skip _ _ _ _ _ h =>
      cases h with
      | head => exact Or.inr rfl
      | skip _ _ _ _ _ h => cases h

theorem LinearPart.atomic_difference {x a b : Term} {c : Rat}
    (h : LinearPart x (__poly_add (atomic a) (__poly_neg (atomic b))) c) : x = a ∨ x = b := by
  by_cases hab : a = b
  · subst b
    have hz : __poly_add (atomic a) (__poly_neg (atomic a)) = zero := by
      simp [atomic, poly, mon, single, zero, __poly_add, __poly_neg, __eo_mk_apply,
        __eo_eq, __eo_neg, __eo_add, __eo_ite, native_ite, native_teq,
        native_qplus, native_qneg, ratZero, Rat.add_neg_cancel]
    rw [hz] at h
    cases h
  · by_cases hcmp : native_tcmp (single b) (single a) = true
    · have he : __poly_add (atomic a) (__poly_neg (atomic b)) =
          poly (single a) 1 (poly (single b) (-1) zero) := by
        simp [atomic, poly, mon, single, zero, __poly_add, __poly_neg, __eo_mk_apply,
          __eo_eq, __eo_neg, __eo_add, __eo_ite, __eo_cmp, native_ite, native_teq,
          native_qplus, native_qneg, ratZero, Rat.add_neg_cancel, hab, hcmp, eq_comm]
      rw [he] at h
      exact h.two_atoms
    · have he : __poly_add (atomic a) (__poly_neg (atomic b)) =
          poly (single b) (-1) (poly (single a) 1 zero) := by
        simp [atomic, poly, mon, single, zero, __poly_add, __poly_neg, __eo_mk_apply,
          __eo_eq, __eo_neg, __eo_add, __eo_ite, __eo_cmp, native_ite, native_teq,
          native_qplus, native_qneg, ratZero, Rat.add_neg_cancel, hab, hcmp, eq_comm]
      rw [he] at h
      exact h.two_atoms.symm

end QuantVarElimIneq
