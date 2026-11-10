module

public import Cpc.Logos
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
import all Cpc.Logos
import all Cpc.SmtEval

/-!
# The univariate polynomials of the coverings calculus

The coverings rules compute with univariate polynomials written as `@@upoly`
terms: `(@@upoly a p)` is `a + x * p`, and `@@upoly_zero` is zero. This file
reads such a term as the list of its rational coefficients, lowest degree
first, and shows that the programs of `programs/UPoly.eo` compute what their
names say, as functions evaluated at a real point.
-/

@[expose] public section

open Eo
open SmtEval

set_option linter.unusedVariables false

namespace CoveringsProofs

/-- The value at `v` of the polynomial with coefficients `l`, lowest degree first. -/
noncomputable def lev : List Rat -> Real -> Real
  | [], _ => 0
  | a :: l, v => (a : Real) + v * lev l v

@[simp] theorem lev_nil (v : Real) : lev [] v = 0 := rfl

@[simp] theorem lev_cons (a : Rat) (l : List Rat) (v : Real) :
    lev (a :: l) v = (a : Real) + v * lev l v := rfl

/-- `P` is a `@@upoly` term with the rational coefficients `l`. -/
inductive UPolyWf : Term -> List Rat -> Prop where
  | zero : UPolyWf (Term.UOp UserOp._at__at_upoly_zero) []
  | cons (a : Rat) (p : Term) (l : List Rat) :
      UPolyWf p l ->
      UPolyWf (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_upoly) (Term.Rational a)) p)
        (a :: l)

/-- `P` is a `@@upoly` term whose value at every point is given by `f`. -/
def UPolyDen (P : Term) (f : Real -> Real) : Prop :=
  ∃ l, UPolyWf P l ∧ ∀ v, lev l v = f v

theorem UPolyWf.ne_stuck {P : Term} {l : List Rat} (h : UPolyWf P l) : P ≠ Term.Stuck := by
  cases h <;> simp

theorem upoly_zero_den : UPolyDen (Term.UOp UserOp._at__at_upoly_zero) (fun _ => 0) :=
  ⟨[], UPolyWf.zero, fun _ => rfl⟩

private theorem eo_is_list_upoly_of_wf {P : Term} {l : List Rat} (h : UPolyWf P l) :
    __eo_is_list (Term.UOp UserOp._at__at_upoly) P = Term.Boolean true := by
  induction h with
  | zero => rfl
  | cons a p l hp ih =>
      have hp' := hp.ne_stuck
      simp only [__eo_is_list, __eo_is_ok] at ih ⊢
      simp [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not] at ih ⊢
      exact ih

theorem eo_cons_upoly_of_wf {P : Term} {l : List Rat} (h : UPolyWf P l) (a : Rat) :
    __eo_cons (Term.UOp UserOp._at__at_upoly) (Term.Rational a) P =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_upoly) (Term.Rational a)) P := by
  simp [__eo_cons, eo_is_list_upoly_of_wf h, __eo_requires, native_ite, native_teq,
    native_not]

/-- `$upoly_cons a p`, as every program writes it inline. -/
def upolyCons (a : Rat) (P : Term) : Term :=
  __eo_ite (__eo_and (__eo_is_eq P (Term.UOp UserOp._at__at_upoly_zero))
      (__eo_is_eq (Term.Rational a) (Term.Rational (native_mk_rational 0 1))))
    (Term.UOp UserOp._at__at_upoly_zero)
    (__eo_cons (Term.UOp UserOp._at__at_upoly) (Term.Rational a) P)

theorem native_mk_rational_zero' : native_mk_rational 0 1 = (0 : Rat) := by native_decide

theorem upolyCons_eq {P : Term} {l : List Rat} (h : UPolyWf P l) (a : Rat) :
    upolyCons a P =
      if P = Term.UOp UserOp._at__at_upoly_zero ∧ a = 0 then Term.UOp UserOp._at__at_upoly_zero
      else Term.Apply (Term.Apply (Term.UOp UserOp._at__at_upoly) (Term.Rational a)) P := by
  have hP := h.ne_stuck
  rw [← eo_cons_upoly_of_wf h a]
  unfold upolyCons
  by_cases hc : P = Term.UOp UserOp._at__at_upoly_zero ∧ a = 0
  · rcases hc with ⟨rfl, rfl⟩
    simp [__eo_ite, __eo_and, __eo_is_eq, native_teq, native_and, native_not,
      native_mk_rational_zero', native_ite]
  · simp only [hc, ↓reduceIte]
    simp [__eo_ite, __eo_and, __eo_is_eq, native_teq, native_and, native_not,
      native_mk_rational_zero', native_ite, hP, eq_comm (a := Term.UOp UserOp._at__at_upoly_zero)]
    have hn0 : ¬(P = Term.UOp UserOp._at__at_upoly_zero ∧ (0 : Rat) = a) :=
      fun h' => hc ⟨h'.1, h'.2.symm⟩
    simp only [hn0, ↓reduceIte]
    have hn : ¬P = Term.UOp UserOp._at__at_upoly_zero ∨ ¬(0 : Rat) = a := by
      by_cases h1 : P = Term.UOp UserOp._at__at_upoly_zero
      · exact Or.inr fun h2 => hc ⟨h1, h2.symm⟩
      · exact Or.inl h1
    simp [hn]

theorem upolyCons_den {P : Term} {f : Real -> Real} (h : UPolyDen P f) (a : Rat) :
    UPolyDen (upolyCons a P) (fun v => (a : Real) + v * f v) := by
  rcases h with ⟨l, hl, hf⟩
  rw [upolyCons_eq hl]
  split
  · rename_i hz
    rcases hz with ⟨rfl, rfl⟩
    cases hl
    exact ⟨[], UPolyWf.zero, fun v => by simp [← hf v]⟩
  · exact ⟨a :: l, UPolyWf.cons a P l hl, fun v => by simp [hf v]⟩

local notation "UZ" => Term.UOp UserOp._at__at_upoly_zero
local notation "UC" a ", " p => Term.Apply (Term.Apply (Term.UOp UserOp._at__at_upoly) (Term.Rational a)) p

theorem upoly_add_zero_left (Q : Term) : __upoly_add UZ Q = (if Q = Term.Stuck then Term.Stuck else Q) := by
  cases Q <;> simp [__upoly_add]

theorem upoly_add_cons_zero (a : Rat) (p : Term) : __upoly_add (UC a, p) UZ = (UC a, p) := by
  simp [__upoly_add]

theorem upoly_add_cons_cons (a b : Rat) (p q : Term) :
    __upoly_add (UC a, p) (UC b, q) = upolyCons (a + b) (__upoly_add p q) := by
  simp [__upoly_add, upolyCons, __eo_add, native_qplus]

theorem upoly_add_den {P Q : Term} {f g : Real -> Real} (hP : UPolyDen P f) (hQ : UPolyDen Q g) :
    UPolyDen (__upoly_add P Q) (fun v => f v + g v) := by
  rcases hP with ⟨l, hl, hf⟩
  induction hl generalizing Q f g with
  | zero =>
      rcases hQ with ⟨m, hm, hg⟩
      simp only [upoly_add_zero_left, hm.ne_stuck, ↓reduceIte]
      exact ⟨m, hm, fun v => by simp [← hf v, hg v]⟩
  | cons a p l hp ih =>
      rcases hQ with ⟨m, hm, hg⟩
      cases hm with
      | zero =>
          rw [upoly_add_cons_zero]
          exact ⟨a :: l, UPolyWf.cons a p l hp, fun v => by simp [hf v, ← hg v]⟩
      | cons b q m hq =>
          rw [upoly_add_cons_cons]
          have hrec := ih (f := lev l) (g := lev m) ⟨m, hq, fun _ => rfl⟩ (fun _ => rfl)
          have := upolyCons_den hrec (a + b)
          refine (show UPolyDen _ _ = UPolyDen _ _ from ?_) ▸ this
          congr 1
          funext v
          rw [← hf v, ← hg v]
          simp
          ring

theorem upoly_scale_zero (c : Rat) : __upoly_scale (Term.Rational c) UZ = UZ := by
  simp [__upoly_scale]

theorem upoly_scale_cons (c a : Rat) (p : Term) :
    __upoly_scale (Term.Rational c) (UC a, p) = upolyCons (c * a) (__upoly_scale (Term.Rational c) p) := by
  simp [__upoly_scale, upolyCons, __eo_mul, native_qmult]

theorem upoly_scale_den (c : Rat) {P : Term} {f : Real -> Real} (hP : UPolyDen P f) :
    UPolyDen (__upoly_scale (Term.Rational c) P) (fun v => (c : Real) * f v) := by
  rcases hP with ⟨l, hl, hf⟩
  induction hl generalizing f with
  | zero =>
      rw [upoly_scale_zero]
      exact ⟨[], UPolyWf.zero, fun v => by simp [← hf v]⟩
  | cons a p l hp ih =>
      rw [upoly_scale_cons]
      have := upolyCons_den (ih (f := lev l) (fun _ => rfl)) (c * a)
      refine (show UPolyDen _ _ = UPolyDen _ _ from ?_) ▸ this
      congr 1
      funext v
      rw [← hf v]
      simp
      ring

theorem upoly_mul_zero (Q : Term) (hQ : Q ≠ Term.Stuck) : __upoly_mul UZ Q = UZ := by
  cases Q <;> simp_all [__upoly_mul]

theorem upoly_mul_cons (a : Rat) (p Q : Term) (hQ : Q ≠ Term.Stuck) :
    __upoly_mul (UC a, p) Q =
      __upoly_add (__upoly_scale (Term.Rational a) Q) (upolyCons 0 (__upoly_mul p Q)) := by
  cases Q <;> simp_all [__upoly_mul, upolyCons, __eo_and, __eo_is_eq, native_mk_rational_zero',
    native_and, native_teq, native_not]

theorem upoly_mul_den {P Q : Term} {f g : Real -> Real} (hP : UPolyDen P f) (hQ : UPolyDen Q g) :
    UPolyDen (__upoly_mul P Q) (fun v => f v * g v) := by
  rcases hP with ⟨l, hl, hf⟩
  have hQs : Q ≠ Term.Stuck := by rcases hQ with ⟨m, hm, _⟩; exact hm.ne_stuck
  induction hl generalizing f with
  | zero =>
      rw [upoly_mul_zero Q hQs]
      exact ⟨[], UPolyWf.zero, fun v => by simp [← hf v]⟩
  | cons a p l hp ih =>
      rw [upoly_mul_cons a p Q hQs]
      have h1 := upoly_scale_den a hQ
      have h2 := upolyCons_den (ih (f := lev l) (fun _ => rfl)) 0
      have := upoly_add_den h1 h2
      refine (show UPolyDen _ _ = UPolyDen _ _ from ?_) ▸ this
      congr 1
      funext v
      rw [← hf v]
      simp
      ring

/-- `q` is an `@List` of the rational literals `l`. -/
inductive RatList : Term -> List Rat -> Prop where
  | nil : RatList Term.__eo_List_nil []
  | cons (a : Rat) (q : Term) (l : List Rat) :
      RatList q l ->
      RatList (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Rational a)) q) (a :: l)

theorem RatList.ne_stuck {q : Term} {l : List Rat} (h : RatList q l) : q ≠ Term.Stuck := by
  cases h <;> simp

private theorem eo_is_list_list_of_ratList {q : Term} {l : List Rat} (h : RatList q l) :
    __eo_is_list Term.__eo_List_cons q = Term.Boolean true := by
  induction h with
  | nil => rfl
  | cons a p l hp ih =>
      have hp' := hp.ne_stuck
      simp only [__eo_is_list, __eo_is_ok] at ih ⊢
      simp [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not] at ih ⊢
      exact ih

theorem upoly_to_list_of_wf {P : Term} {l : List Rat} (h : UPolyWf P l) :
    RatList (__upoly_to_list P) l := by
  induction h with
  | zero => exact RatList.nil
  | cons a p l hp ih =>
      have hEq : __upoly_to_list (UC a, p) =
          Term.Apply (Term.Apply Term.__eo_List_cons (Term.Rational a)) (__upoly_to_list p) := by
        simp [__upoly_to_list, __eo_cons, eo_is_list_list_of_ratList ih, __eo_requires,
          native_ite, native_teq, native_not]
      rw [hEq]
      exact RatList.cons a _ l ih

theorem upoly_of_list_den {q : Term} (h : __upoly_of_list q ≠ Term.Stuck) :
    ∃ l, RatList q l ∧ UPolyDen (__upoly_of_list q) (lev l) := by
  induction q using __upoly_of_list.induct with
  | case1 => exact ⟨[], RatList.nil, upoly_zero_den⟩
  | case2 c rest ih =>
      have hc : __eo_is_q c = Term.Boolean true := by
        rw [__upoly_of_list] at h
        simp only [__eo_requires, native_ite, native_teq] at h
        split at h <;> simp_all
      have hcq : ∃ a, c = Term.Rational a := by
        cases c <;> simp_all [__eo_is_q, __eo_is_q_internal, native_and, native_not, native_teq]
      rcases hcq with ⟨a, rfl⟩
      have hEq : __upoly_of_list (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Rational a)) rest) =
          upolyCons a (__upoly_of_list rest) := by
        rw [__upoly_of_list]
        simp [__eo_requires, hc, native_ite, native_teq, native_not, upolyCons]
      rw [hEq] at h ⊢
      have hrest : __upoly_of_list rest ≠ Term.Stuck := by
        intro hs
        apply h
        simp [upolyCons, hs, __eo_ite, __eo_and, __eo_is_eq, native_teq, native_not, native_and,
          __eo_cons, __eo_requires, __eo_is_list, native_ite]
      rcases ih hrest with ⟨l, hl, hd⟩
      exact ⟨a :: l, RatList.cons a rest l hl, upolyCons_den hd a⟩
  | case3 q hq hq2 =>
      exfalso
      apply h
      unfold __upoly_of_list
      split
      · exact absurd rfl hq
      · rename_i c l; exact absurd rfl (hq2 c l)
      · rfl

theorem upoly_eval_rat {P : Term} {l : List Rat} (h : UPolyWf P l) (v : Rat) :
    ∃ r : Rat, __upoly_eval P (Term.Rational v) = Term.Rational r ∧ (r : Real) = lev l v := by
  induction h with
  | zero => exact ⟨0, by simp [__upoly_eval, native_mk_rational_zero'], by simp⟩
  | cons a p l hp ih =>
      rcases ih with ⟨r, hr, hrl⟩
      refine ⟨a + v * r, ?_, ?_⟩
      · simp [__upoly_eval, hr, __eo_mul, __eo_add, native_qplus, native_qmult]
      · simp [hrl]

/-- What `$upoly_of_term` needs of a valuation: it respects the arithmetic operators the
program reads, on terms satisfying `H`, and `H` passes to their arguments. -/
structure OfTermVal (H : Term -> Prop) (ρ : Term -> Real) : Prop where
  rational : ∀ q, ρ (Term.Rational q) = q
  numeral : ∀ n : Int, ρ (Term.Numeral n) = n
  uneg : ∀ a, H (Term.Apply (Term.UOp UserOp.__eoo_neg_2) a) ->
    H a ∧ ρ (Term.Apply (Term.UOp UserOp.__eoo_neg_2) a) = - ρ a
  plus : ∀ a b, H (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) ->
    H a ∧ H b ∧ ρ (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) = ρ a + ρ b
  neg : ∀ a b, H (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) ->
    H a ∧ H b ∧ ρ (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) = ρ a - ρ b
  mult : ∀ a b, H (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) ->
    H a ∧ H b ∧ ρ (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) = ρ a * ρ b
  to_real : ∀ a, H (Term.Apply (Term.UOp UserOp.to_real) a) ->
    H a ∧ ρ (Term.Apply (Term.UOp UserOp.to_real) a) = ρ a

private theorem upoly_den_stuck_false {f : Real -> Real} (h : UPolyDen Term.Stuck f) : False := by
  rcases h with ⟨l, hl, _⟩
  exact hl.ne_stuck rfl

private theorem upoly_add_stuck_left (Q : Term) : __upoly_add Term.Stuck Q = Term.Stuck := by
  simp [__upoly_add]

private theorem upoly_add_stuck_right (P : Term) : __upoly_add P Term.Stuck = Term.Stuck := by
  cases P <;> simp [__upoly_add]

private theorem upoly_scale_stuck (c : Term) : __upoly_scale c Term.Stuck = Term.Stuck := by
  cases c <;> simp [__upoly_scale]

private theorem upoly_mul_stuck_left (Q : Term) : __upoly_mul Term.Stuck Q = Term.Stuck := by
  cases Q <;> simp [__upoly_mul]

private theorem upoly_mul_stuck_right (P : Term) : __upoly_mul P Term.Stuck = Term.Stuck := by
  simp [__upoly_mul]

/-- The atom case of `$upoly_of_term`. -/
def upolyOfTermAtom (x a : Term) : Term :=
  __eo_ite (__eo_is_q (__eo_to_q a))
    (__eo_ite (__eo_and (Term.Boolean true)
        (__eo_is_eq (__eo_to_q a) (Term.Rational (native_mk_rational 0 1))))
      (Term.UOp UserOp._at__at_upoly_zero)
      (__eo_cons (Term.UOp UserOp._at__at_upoly) (__eo_to_q a) (Term.UOp UserOp._at__at_upoly_zero)))
    (__eo_requires a x
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_upoly) (Term.Rational (native_mk_rational 0 1)))
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_upoly) (Term.Rational (native_mk_rational 1 1)))
          (Term.UOp UserOp._at__at_upoly_zero))))

theorem upoly_of_term_cases (x t : Term) (hx : x ≠ Term.Stuck) (ht : t ≠ Term.Stuck) :
    (∃ a, t = Term.Apply (Term.UOp UserOp.__eoo_neg_2) a ∧
        __upoly_of_term x t = __upoly_scale (Term.Rational (-1)) (__upoly_of_term x a)) ∨
    (∃ a b, t = Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b ∧
        __upoly_of_term x t = __upoly_add (__upoly_of_term x a) (__upoly_of_term x b)) ∨
    (∃ a b, t = Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b ∧
        __upoly_of_term x t = __upoly_add (__upoly_of_term x a)
          (__upoly_scale (Term.Rational (-1)) (__upoly_of_term x b))) ∨
    (∃ a b, t = Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b ∧
        __upoly_of_term x t = __upoly_mul (__upoly_of_term x a) (__upoly_of_term x b)) ∨
    (∃ a, t = Term.Apply (Term.UOp UserOp.to_real) a ∧
        __upoly_of_term x t = __upoly_of_term x a) ∨
    __upoly_of_term x t = upolyOfTermAtom x t := by
  have hm1 : native_mk_rational 1 1 = (1 : Rat) := by native_decide
  rw [__upoly_of_term.eq_def]
  split
  · exact absurd rfl hx
  · exact absurd rfl ht
  · exact Or.inl ⟨_, rfl, by simp [hm1]⟩
  · exact Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, by simp [hm1]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

private theorem upoly_const_den (q : Rat) :
    UPolyDen (__eo_ite (__eo_and (Term.Boolean true)
        (__eo_is_eq (Term.Rational q) (Term.Rational (native_mk_rational 0 1))))
      (Term.UOp UserOp._at__at_upoly_zero)
      (__eo_cons (Term.UOp UserOp._at__at_upoly) (Term.Rational q) (Term.UOp UserOp._at__at_upoly_zero)))
      (fun _ => (q : Real)) := by
  have := upolyCons_den upoly_zero_den q
  simp only [mul_zero, add_zero] at this
  refine (show UPolyDen _ _ = UPolyDen _ _ from ?_) ▸ this
  congr 1

private theorem upoly_of_term_atom_den {H : Term -> Prop} {ρ : Term -> Real} (hρ : OfTermVal H ρ)
    (x t : Term) (hx : x ≠ Term.Stuck) (h : upolyOfTermAtom x t ≠ Term.Stuck) :
    ∃ f, UPolyDen (upolyOfTermAtom x t) f ∧ ρ t = f (ρ x) := by
  have hm1 : native_mk_rational 1 1 = (1 : Rat) := by native_decide
  by_cases hq : ∃ q : Rat, __eo_to_q t = Term.Rational q ∧ ρ t = q
  · rcases hq with ⟨q, hq, hρq⟩
    refine ⟨fun _ => (q : Real), ?_, hρq⟩
    unfold upolyOfTermAtom
    rw [hq]
    simpa [__eo_is_q, __eo_is_q_internal, __eo_ite, native_and, native_not, native_teq,
      native_ite] using upoly_const_den q
  · have hnq : __eo_to_q t = Term.Stuck := by
      cases t with
      | Numeral n =>
          exact absurd ⟨native_to_real n, rfl, by
            rw [hρ.numeral]; simp [native_to_real, native_mk_rational]⟩ hq
      | Rational q => exact absurd ⟨q, rfl, hρ.rational q⟩ hq
      | _ => rfl
    have hEq : upolyOfTermAtom x t =
        __eo_requires t x
          (UC native_mk_rational 0 1, (UC native_mk_rational 1 1, UZ)) := by
      simp [upolyOfTermAtom, hnq, __eo_is_q, __eo_is_q_internal, __eo_ite, native_and,
        native_not, native_teq, native_ite]
    rw [hEq] at h ⊢
    have htx : t = x := by
      by_contra hne
      apply h
      simp [__eo_requires, native_ite, native_teq, hne]
    subst htx
    refine ⟨fun v => v, ?_, rfl⟩
    have hEq2 : __eo_requires t t (UC native_mk_rational 0 1, (UC native_mk_rational 1 1, UZ)) =
        (UC 0, (UC 1, UZ)) := by
      simp [__eo_requires, native_ite, native_teq, native_not, hx, hm1, native_mk_rational_zero']
    rw [hEq2]
    exact ⟨[0, 1], UPolyWf.cons 0 _ _ (UPolyWf.cons 1 _ _ UPolyWf.zero), fun v => by simp⟩

/-- The polynomial `$upoly_of_term x t` computes is `t` read as a polynomial in `x`. -/
theorem upoly_of_term_den {H : Term -> Prop} {ρ : Term -> Real} (hρ : OfTermVal H ρ)
    (x t : Term) (hx : x ≠ Term.Stuck) (hH : H t) (h : __upoly_of_term x t ≠ Term.Stuck) :
    ∃ f, UPolyDen (__upoly_of_term x t) f ∧ ρ t = f (ρ x) := by
  induction hn : sizeOf t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
  have ht : t ≠ Term.Stuck := by
    intro hs; subst hs; cases x <;> simp_all [__upoly_of_term]
  rcases upoly_of_term_cases x t hx ht with
    ⟨a1, rfl, hEq⟩ | ⟨a1, a2, rfl, hEq⟩ | ⟨a1, a2, rfl, hEq⟩ | ⟨a1, a2, rfl, hEq⟩ |
    ⟨a1, rfl, hEq⟩ | hEq
  · rw [hEq] at h ⊢
    have h1 : __upoly_of_term x a1 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_scale_stuck] at h; exact h rfl
    obtain ⟨hHa, hρa⟩ := hρ.uneg a1 hH
    rcases ih _ (by subst hn; simp <;> omega) a1 hHa h1 rfl with ⟨f, hf, hfv⟩
    exact ⟨_, upoly_scale_den (-1) hf, by simp [hρa, hfv]⟩
  · rw [hEq] at h ⊢
    have h1 : __upoly_of_term x a1 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_add_stuck_left] at h; exact h rfl
    have h2 : __upoly_of_term x a2 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_add_stuck_right] at h; exact h rfl
    obtain ⟨hH1, hH2, hρa⟩ := hρ.plus a1 a2 hH
    rcases ih _ (by subst hn; simp <;> omega) a1 hH1 h1 rfl with ⟨f, hf, hfv⟩
    rcases ih _ (by subst hn; simp <;> omega) a2 hH2 h2 rfl with ⟨g, hg, hgv⟩
    exact ⟨_, upoly_add_den hf hg, by simp [hρa, hfv, hgv]⟩
  · rw [hEq] at h ⊢
    have h1 : __upoly_of_term x a1 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_add_stuck_left] at h; exact h rfl
    have h2 : __upoly_of_term x a2 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_scale_stuck, upoly_add_stuck_right] at h; exact h rfl
    obtain ⟨hH1, hH2, hρa⟩ := hρ.neg a1 a2 hH
    rcases ih _ (by subst hn; simp <;> omega) a1 hH1 h1 rfl with ⟨f, hf, hfv⟩
    rcases ih _ (by subst hn; simp <;> omega) a2 hH2 h2 rfl with ⟨g, hg, hgv⟩
    exact ⟨_, upoly_add_den hf (upoly_scale_den (-1) hg), by simp [hρa, hfv, hgv]; ring⟩
  · rw [hEq] at h ⊢
    have h1 : __upoly_of_term x a1 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_mul_stuck_left] at h; exact h rfl
    have h2 : __upoly_of_term x a2 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_mul_stuck_right] at h; exact h rfl
    obtain ⟨hH1, hH2, hρa⟩ := hρ.mult a1 a2 hH
    rcases ih _ (by subst hn; simp <;> omega) a1 hH1 h1 rfl with ⟨f, hf, hfv⟩
    rcases ih _ (by subst hn; simp <;> omega) a2 hH2 h2 rfl with ⟨g, hg, hgv⟩
    exact ⟨_, upoly_mul_den hf hg, by simp [hρa, hfv, hgv]⟩
  · rw [hEq] at h ⊢
    obtain ⟨hHa, hρa⟩ := hρ.to_real a1 hH
    rcases ih _ (by subst hn; simp <;> omega) a1 hHa h rfl with ⟨f, hf, hfv⟩
    exact ⟨f, hf, by simp [hρa, hfv]⟩
  · rw [hEq] at h ⊢
    exact upoly_of_term_atom_den hρ x t hx h

end CoveringsProofs
