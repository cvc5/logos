module

public import Cpc.Proofs.RuleSupport.CoveringsUPolySupport
import all Cpc.Proofs.RuleSupport.CoveringsUPolySupport
public import Cpc.Proofs.RuleSupport.SturmTarski.Theorem
import all Cpc.Logos
import all Cpc.SmtEval

/-!
# `@@upoly` terms as real polynomials

The coefficients of a `@@upoly` term are a real polynomial. The programs of
`programs/UPoly.eo` keep a term canonical, with no zero leading coefficient, so on
such terms `$upoly_deg` and `$upoly_lc` are the degree and leading coefficient of the
polynomial. This is what the remainder sequences of the coverings rules are checked
with, and what relates them to `sturmSeq`.
-/

@[expose] public section

open Eo
open SmtEval
open Polynomial
open SturmTarski

set_option linter.unusedVariables false

namespace CoveringsProofs

local notation "UZ" => Term.UOp UserOp._at__at_upoly_zero

/-- The real polynomial with the coefficients `l`, lowest degree first. -/
noncomputable def toPoly : List Rat -> ℝ[X]
  | [] => 0
  | a :: l => C (a : ℝ) + X * toPoly l

@[simp] theorem toPoly_nil : toPoly [] = 0 := rfl

theorem toPoly_cons (a : Rat) (l : List Rat) : toPoly (a :: l) = C (a : ℝ) + X * toPoly l := rfl

theorem eval_toPoly (l : List Rat) (v : ℝ) : (toPoly l).eval v = lev l v := by
  induction l with
  | nil => simp
  | cons a l ih => simp [toPoly_cons, ih]

/-- Two coefficient lists with the same values are the same polynomial. -/
theorem toPoly_eq_of_lev {l m : List Rat} (h : ∀ v, lev l v = lev m v) : toPoly l = toPoly m :=
  Polynomial.funext fun v => by rw [eval_toPoly, eval_toPoly, h]

theorem coeff_toPoly (l : List Rat) (i : ℕ) : (toPoly l).coeff i = ((l.getD i 0 : Rat) : ℝ) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
      cases i with
      | zero => simp [toPoly_cons]
      | succ i => simp [toPoly_cons, coeff_X_mul, ih]

/-- No zero leading coefficient. -/
def Canon (l : List Rat) : Prop := ∀ h : l ≠ [], l.getLast h ≠ 0

theorem canon_nil : Canon [] := fun h => absurd rfl h

theorem natDegree_toPoly {l : List Rat} (hc : Canon l) (hne : l ≠ []) :
    (toPoly l).natDegree = l.length - 1 ∧ (toPoly l).leadingCoeff = ((l.getLast hne : Rat) : ℝ) := by
  have hlast : (toPoly l).coeff (l.length - 1) = ((l.getLast hne : Rat) : ℝ) := by
    have hlt : l.length - 1 < l.length := by
      have : 0 < l.length := List.length_pos_iff.mpr hne
      omega
    rw [coeff_toPoly, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      List.getLast_eq_getElem]
    rfl
  have hle : (toPoly l).natDegree ≤ l.length - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have : l.length - 1 < i := by exact_mod_cast hi
    rw [coeff_toPoly, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp
  have hdeg : (toPoly l).natDegree = l.length - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hlast]; exact_mod_cast hc hne)
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg, hlast]

theorem toPoly_ne_zero {l : List Rat} (hc : Canon l) (hne : l ≠ []) : toPoly l ≠ 0 := by
  intro h
  have := (natDegree_toPoly hc hne).2
  rw [h, leadingCoeff_zero] at this
  exact hc hne (by exact_mod_cast this.symm)

local notation "UC" a ", " p => Term.Apply (Term.Apply (Term.UOp UserOp._at__at_upoly) (Term.Rational a)) p

theorem upolyWf_unique {P : Term} {l m : List Rat} (h1 : UPolyWf P l) (h2 : UPolyWf P m) : l = m := by
  induction h1 generalizing m with
  | zero => cases h2; rfl
  | cons a p l hp ih => cases h2 with
    | cons _ _ m hm => rw [ih hm]

/-- `P` is canonical with the polynomial `p`. -/
def CPoly (P : Term) (p : ℝ[X]) : Prop := ∃ l, UPolyWf P l ∧ Canon l ∧ toPoly l = p

theorem CPoly.ne_stuck {P : Term} {p : ℝ[X]} (h : CPoly P p) : P ≠ Term.Stuck := by
  rcases h with ⟨l, hl, _⟩; exact hl.ne_stuck

theorem CPoly.den {P : Term} {p : ℝ[X]} (h : CPoly P p) : UPolyDen P (fun v => p.eval v) := by
  rcases h with ⟨l, hl, _, rfl⟩; exact ⟨l, hl, fun v => (eval_toPoly l v).symm⟩

theorem cpoly_zero : CPoly UZ 0 := ⟨[], UPolyWf.zero, canon_nil, rfl⟩

/-- A `CPoly` is determined by any description of its values. -/
theorem CPoly.of_den {P : Term} {p q : ℝ[X]} (h : CPoly P p) {f : ℝ -> ℝ} (hd : UPolyDen P f)
    (hq : ∀ v, q.eval v = f v) : CPoly P q := by
  rcases h with ⟨l, hl, hc, rfl⟩
  rcases hd with ⟨m, hm, hf⟩
  cases upolyWf_unique hl hm
  exact ⟨l, hl, hc, Polynomial.funext fun v => by rw [eval_toPoly, hf, hq]⟩

theorem upolyCons_cpoly {P : Term} {p : ℝ[X]} (h : CPoly P p) (a : Rat) :
    CPoly (upolyCons a P) (C (a : ℝ) + X * p) := by
  rcases h with ⟨l, hl, hc, rfl⟩
  rw [upolyCons_eq hl]
  split
  · rename_i hz
    rcases hz with ⟨rfl, rfl⟩
    cases hl
    exact ⟨[], UPolyWf.zero, canon_nil, by simp⟩
  · rename_i hz
    refine ⟨a :: l, UPolyWf.cons a P l hl, ?_, rfl⟩
    intro hne
    by_cases hl0 : l = []
    · subst hl0
      cases hl
      simp only [List.getLast_singleton]
      intro ha; exact hz ⟨rfl, ha⟩
    · rw [List.getLast_cons hl0]; exact hc hl0

theorem upoly_add_cpoly {P Q : Term} {p q : ℝ[X]} (hP : CPoly P p) (hQ : CPoly Q q) :
    CPoly (__upoly_add P Q) (p + q) := by
  rcases hP with ⟨l, hl, hcl, rfl⟩
  induction hl generalizing Q q with
  | zero =>
      have hQs := hQ.ne_stuck
      simp only [upoly_add_zero_left, hQs, ↓reduceIte]
      simpa using hQ
  | cons a p' l hp ih =>
      rcases hQ with ⟨m, hm, hcm, rfl⟩
      cases hm with
      | zero =>
          rw [upoly_add_cons_zero]
          exact ⟨a :: l, UPolyWf.cons a p' l hp, hcl, by simp⟩
      | cons b q' m hq =>
          rw [upoly_add_cons_cons]
          have hcl' : Canon l := fun hne => by
            have := hcl (List.cons_ne_nil a l); rwa [List.getLast_cons hne] at this
          have hcm' : Canon m := fun hne => by
            have := hcm (List.cons_ne_nil b m); rwa [List.getLast_cons hne] at this
          have := upolyCons_cpoly (ih (Q := q') (q := toPoly m) ⟨m, hq, hcm', rfl⟩ hcl') (a + b)
          refine (show CPoly _ _ = CPoly _ _ from ?_) ▸ this
          congr 1
          simp [toPoly_cons]; ring

theorem canon_tail {a : Rat} {l : List Rat} (h : Canon (a :: l)) : Canon l := fun hne => by
  have := h (List.cons_ne_nil a l); rwa [List.getLast_cons hne] at this

theorem upoly_scale_cpoly (c : Rat) {P : Term} {p : ℝ[X]} (hP : CPoly P p) :
    CPoly (__upoly_scale (Term.Rational c) P) (C (c : ℝ) * p) := by
  rcases hP with ⟨l, hl, hcl, rfl⟩
  induction hl with
  | zero => rw [upoly_scale_zero]; exact ⟨[], UPolyWf.zero, canon_nil, by simp⟩
  | cons a p' l hp ih =>
      rw [upoly_scale_cons]
      have := upolyCons_cpoly (ih (canon_tail hcl)) (c * a)
      refine (show CPoly _ _ = CPoly _ _ from ?_) ▸ this
      congr 1
      simp [toPoly_cons]; ring

theorem upoly_mul_cpoly {P Q : Term} {p q : ℝ[X]} (hP : CPoly P p) (hQ : CPoly Q q) :
    CPoly (__upoly_mul P Q) (p * q) := by
  rcases hP with ⟨l, hl, hcl, rfl⟩
  have hQs := hQ.ne_stuck
  induction hl with
  | zero => rw [upoly_mul_zero Q hQs]; exact ⟨[], UPolyWf.zero, canon_nil, by simp⟩
  | cons a p' l hp ih =>
      rw [upoly_mul_cons a p' Q hQs]
      have := upoly_add_cpoly (upoly_scale_cpoly a hQ) (upolyCons_cpoly (ih (canon_tail hcl)) 0)
      refine (show CPoly _ _ = CPoly _ _ from ?_) ▸ this
      congr 1
      simp [toPoly_cons]; ring

theorem upoly_derivative_rec_cpoly {P : Term} {p : ℝ[X]} (hP : CPoly P p) (i : Rat) :
    CPoly (__upoly_derivative_rec P (Term.Rational i)) (C (i : ℝ) * p + X * derivative p) := by
  rcases hP with ⟨l, hl, hcl, rfl⟩
  induction hl generalizing i with
  | zero => simp [__upoly_derivative_rec]; exact cpoly_zero
  | cons a p' l hp ih =>
      have hEq : __upoly_derivative_rec (UC a, p') (Term.Rational i) =
          upolyCons (i * a) (__upoly_derivative_rec p' (Term.Rational (i + 1))) := by
        have h1 : native_mk_rational 1 1 = (1 : Rat) := by native_decide
        simp [__upoly_derivative_rec, upolyCons, __eo_add, __eo_mul, native_qplus, native_qmult, h1]
      rw [hEq]
      have := upolyCons_cpoly (ih (i + 1) (canon_tail hcl)) (i * a)
      refine (show CPoly _ _ = CPoly _ _ from ?_) ▸ this
      congr 1
      simp [toPoly_cons, derivative_mul]; ring

theorem upoly_derivative_cpoly {P : Term} {p : ℝ[X]} (hP : CPoly P p) :
    CPoly (__upoly_derivative P) (derivative p) := by
  rcases hP with ⟨l, hl, hcl, rfl⟩
  cases hl with
  | zero => simp [__upoly_derivative]; exact cpoly_zero
  | cons a p' l hp =>
      have hEq : __upoly_derivative (UC a, p') = __upoly_derivative_rec p' (Term.Rational 1) := by
        have h1 : native_mk_rational 1 1 = (1 : Rat) := by native_decide
        simp [__upoly_derivative, h1]
      rw [hEq]
      have := upoly_derivative_rec_cpoly ⟨l, hp, canon_tail hcl, rfl⟩ 1
      refine (show CPoly _ _ = CPoly _ _ from ?_) ▸ this
      congr 1
      simp [toPoly_cons, derivative_mul]

theorem upoly_of_list_cpoly {q : Term} (h : __upoly_of_list q ≠ Term.Stuck) :
    ∃ l, RatList q l ∧ CPoly (__upoly_of_list q) (toPoly l) := by
  obtain ⟨l, hq, hd⟩ := upoly_of_list_den h
  refine ⟨l, hq, ?_⟩
  -- canonicity, by the same recursion
  have hc : ∀ q, __upoly_of_list q ≠ Term.Stuck -> ∃ p, CPoly (__upoly_of_list q) p := by
    intro q
    induction hn : sizeOf q using Nat.strong_induction_on generalizing q with
    | _ n ih =>
    intro h
    rcases upoly_of_list_den h with ⟨l, hl, _⟩
    cases hl with
    | nil => exact ⟨0, by simpa [__upoly_of_list] using cpoly_zero⟩
    | cons a rest l' hl' =>
        have hEq : __upoly_of_list (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Rational a)) rest) =
            upolyCons a (__upoly_of_list rest) := by
          rw [__upoly_of_list]
          simp [__eo_requires, __eo_is_q, __eo_is_q_internal, native_ite, native_teq, native_not,
            native_and, upolyCons]
        rw [hEq] at h ⊢
        have hrest : __upoly_of_list rest ≠ Term.Stuck := by
          intro hs; apply h
          simp [upolyCons, hs, __eo_ite, __eo_and, __eo_is_eq, native_teq, native_not, native_and,
            __eo_cons, __eo_requires, __eo_is_list, native_ite]
        obtain ⟨p, hp⟩ := ih _ (by subst hn; simp <;> omega) rest rfl hrest
        exact ⟨_, upolyCons_cpoly hp a⟩
  obtain ⟨p, hp⟩ := hc q h
  exact hp.of_den hd (fun v => eval_toPoly l v)

private theorem upoly_deg_wf {P : Term} {l : List Rat} (h : UPolyWf P l) :
    __upoly_deg P = Term.Numeral ((l.length : Int) - 1) := by
  induction h with
  | zero => simp [__upoly_deg]
  | cons a p l hp ih =>
      simp [__upoly_deg, ih, __eo_add, native_zplus]

/-- `$upoly_deg` of a canonical term is its degree, and `-1` for zero. -/
theorem upoly_deg_cpoly {P : Term} {p : ℝ[X]} (h : CPoly P p) :
    __upoly_deg P = Term.Numeral (if p = 0 then -1 else (p.natDegree : Int)) := by
  rcases h with ⟨l, hl, hc, rfl⟩
  rw [upoly_deg_wf hl]
  by_cases hne : l = []
  · subst hne; simp
  · simp only [toPoly_ne_zero hc hne, ↓reduceIte, (natDegree_toPoly hc hne).1]
    have : 0 < l.length := List.length_pos_iff.mpr hne
    congr 1; push_cast [Nat.cast_sub (show 1 ≤ l.length by omega)]; ring

private theorem upoly_lc_wf {P : Term} {l : List Rat} (h : UPolyWf P l) :
    __upoly_lc P = Term.Rational (l.getLastD 0) := by
  induction h with
  | zero => simp [__upoly_lc, native_mk_rational_zero']
  | cons a p l hp ih =>
      cases hp with
      | zero => simp [__upoly_lc]
      | cons b p' l' hp' =>
          rw [show __upoly_lc (UC a, (UC b, p')) = __upoly_lc (UC b, p') by simp [__upoly_lc], ih]
          simp

/-- `$upoly_lc` of a canonical term is its leading coefficient. -/
theorem upoly_lc_cpoly {P : Term} {p : ℝ[X]} (h : CPoly P p) :
    ∃ r : Rat, __upoly_lc P = Term.Rational r ∧ (r : ℝ) = p.leadingCoeff := by
  rcases h with ⟨l, hl, hc, rfl⟩
  refine ⟨_, upoly_lc_wf hl, ?_⟩
  by_cases hne : l = []
  · subst hne; simp
  · rw [(natDegree_toPoly hc hne).2, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl

theorem upoly_eval_cpoly {P : Term} {p : ℝ[X]} (h : CPoly P p) (v : Rat) :
    ∃ r : Rat, __upoly_eval P (Term.Rational v) = Term.Rational r ∧ (r : ℝ) = p.eval (v : ℝ) := by
  rcases h with ⟨l, hl, hc, rfl⟩
  obtain ⟨r, hr, hr'⟩ := upoly_eval_rat hl v
  exact ⟨r, hr, by rw [hr', eval_toPoly]⟩

theorem cpoly_zero_iff {P : Term} {p : ℝ[X]} (h : CPoly P p) : P = UZ ↔ p = 0 := by
  rcases h with ⟨l, hl, hc, rfl⟩
  constructor
  · rintro rfl; cases hl; rfl
  · intro h0
    by_cases hne : l = []
    · subst hne; cases hl; rfl
    · exact absurd h0 (toPoly_ne_zero hc hne)

/-! ### Remainder sequences -/

private theorem degree_C_mul_lt {a : ℝ} {p B : ℝ[X]} (h : p.degree < B.degree) :
    (C a * p).degree < B.degree := by
  by_cases ha : a = 0
  · subst ha; simp only [map_zero, zero_mul, degree_zero]
    exact lt_of_le_of_lt bot_le h
  · rw [degree_C_mul ha]; exact h

/-- A step `m a = q b - k c` of the checked remainder sequence, with `deg c < deg b`, makes `c`
a multiple of the next entry `-A % B` of the Sturm sequence of `A` and `B`. -/
theorem chain_step_poly {A B q c : ℝ[X]} {α β m k : ℝ} (hB : B ≠ 0) (hβ : β ≠ 0) (hk : k ≠ 0)
    (hdeg : c.degree < B.degree)
    (hrel : C m * (C α * A) - q * (C β * B) + C k * c = 0) :
    c = C (m * α / k) * (-A % B) := by
  have hdiv := EuclideanDomain.div_add_mod (-A) B
  have hEq : C k * c - C (m * α) * (-A % B) = B * (q * C β + C (m * α) * (-A / B)) := by
    rw [map_mul]
    linear_combination hrel - C m * C α * hdiv
  have hdvd : B ∣ C k * c - C (m * α) * (-A % B) := ⟨_, hEq⟩
  have hlt : (C k * c - C (m * α) * (-A % B)).degree < B.degree :=
    lt_of_le_of_lt (degree_sub_le _ _)
      (max_lt (degree_C_mul_lt hdeg) (degree_C_mul_lt (EuclideanDomain.mod_lt _ hB)))
  have h0 := eq_zero_of_dvd_of_degree_lt hdvd hlt
  have h1 : C k * c = C (m * α) * (-A % B) := sub_eq_zero.mp h0
  have : c = C k⁻¹ * (C k * c) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]
  rw [this, h1, ← mul_assoc, ← map_mul]
  congr 2
  field_simp

/-- The last step of the checked remainder sequence: `b` divides `m a`, so the Sturm sequence of
`A` and `B` stops at `B`. -/
theorem chain_last_poly {A B q : ℝ[X]} {α β m : ℝ} (hm : m ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hrel : C m * (C α * A) - q * (C β * B) = 0) : -A % B = 0 := by
  rw [EuclideanDomain.mod_eq_zero]
  have : -A = B * (- (C (m * α)⁻¹ * q * C β)) := by
    have h2 : A = C (m * α)⁻¹ * (q * (C β * B)) := by
      rw [← sub_eq_zero.mp hrel, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul,
        show (m * α)⁻¹ * m * α = 1 by field_simp, map_one, one_mul]
    rw [h2]; ring
  exact ⟨_, this⟩

/-- `L` is `L'` with each entry scaled by a constant of the sign `σ`. -/
inductive Scaled (σ : SignType) : List ℝ[X] -> List ℝ[X] -> Prop where
  | nil : Scaled σ [] []
  | cons (c : ℝ) (p : ℝ[X]) (L L' : List ℝ[X]) :
      SignType.sign c = σ -> Scaled σ L L' -> Scaled σ (C c * p :: L) (p :: L')

private theorem scaled_signs {σ : SignType} (hσ : σ ≠ 0) {L L' : List ℝ[X]} (h : Scaled σ L L')
    (f : ℝ[X] -> ℝ) (hf : ∀ c p, f (C c * p) = c * f p) :
    (L.map f).map SignType.sign = ((L'.map f).map SignType.sign).map (σ * ·) := by
  induction h with
  | nil => rfl
  | cons c p L L' hc _ ih => simp [hf, ih, sign_mul, hc]

/-- Scaling by constants of one sign leaves the sign variations unchanged. -/
theorem signVariations_scaled {σ : SignType} (hσ : σ ≠ 0) {L L' : List ℝ[X]} (h : Scaled σ L L')
    (f : ℝ[X] -> ℝ) (hf : ∀ c p, f (C c * p) = c * f p) :
    List.signVariations (L.map f) = List.signVariations (L'.map f) := by
  have hs := scaled_signs hσ h f hf
  rcases σ with _ | _ | _
  · exact absurd rfl hσ
  · -- σ = -1
    rw [← List.signVariations_map_sign (L.map f), hs,
      ← List.signVariations_map_sign (L'.map f)]
    exact List.signVariations_map_of_sign_eq_neg (fun x => by cases x <;> rfl) _
  · rw [List.signVariations_congr (l₂ := L'.map f) (by rw [hs]; simp)]

/-! ### The checked remainder sequence, term by term -/

/-- The entry `(@list ql cl)` of a remainder sequence. -/
abbrev seqEntry (ql cl : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons ql)
    (Term.Apply (Term.Apply Term.__eo_List_cons cl) Term.__eo_List_nil)

abbrev seqCons (ql cl rest : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons (seqEntry ql cl)) rest

/-- The polynomials of the entries of a remainder sequence. -/
inductive SeqPolys : Term -> List ℝ[X] -> Prop where
  | nil : SeqPolys Term.__eo_List_nil []
  | cons (ql cl rest : Term) (p : ℝ[X]) (Ps : List ℝ[X]) :
      CPoly (__upoly_of_list cl) p -> SeqPolys rest Ps -> SeqPolys (seqCons ql cl rest) (p :: Ps)

theorem cpoly_unique {P : Term} {p q : ℝ[X]} (h1 : CPoly P p) (h2 : CPoly P q) : p = q := by
  rcases h1 with ⟨l, hl, _, rfl⟩; rcases h2 with ⟨m, hm, _, rfl⟩
  rw [upolyWf_unique hl hm]

theorem lc_ne_zero_of_cpoly {P : Term} {p : ℝ[X]} (h : CPoly P p) (hp : p ≠ 0) :
    ∃ r : Rat, __upoly_lc P = Term.Rational r ∧ r ≠ 0 ∧ (r : ℝ) = p.leadingCoeff := by
  obtain ⟨r, hr, hr'⟩ := upoly_lc_cpoly h
  refine ⟨r, hr, ?_, hr'⟩
  intro h0; rw [h0] at hr'; exact hp (leadingCoeff_eq_zero.mp (by exact_mod_cast hr'.symm))

private theorem is_eq_true' {a b : Term} (h : __eo_is_eq a b = Term.Boolean true) :
    a = b ∧ a ≠ Term.Stuck := by
  simp [__eo_is_eq, native_and, native_not, native_teq] at h
  exact ⟨h.2.2.symm, h.1⟩

private theorem eo_ite_true {c x y : Term} (h : __eo_ite c x y = Term.Boolean true) :
    (c = Term.Boolean true ∧ x = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ y = Term.Boolean true) := by
  unfold __eo_ite at h
  by_cases hc : c = Term.Boolean true
  · subst hc; simp [native_ite, native_teq] at h; exact Or.inl ⟨rfl, h⟩
  · by_cases hc' : c = Term.Boolean false
    · subst hc'; simp [native_ite, native_teq] at h; exact Or.inr ⟨rfl, h⟩
    · simp [native_ite, native_teq, hc, hc'] at h

private theorem eo_and_true' {x y : Term} (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  cases x <;> cases y <;> simp_all [__eo_and, native_and]
  all_goals first
    | (simp [__eo_requires, native_ite, native_teq, native_not] at h; split at h <;> simp_all)
    | skip

private theorem eo_requires_eq_body' {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    x = y ∧ __eo_requires x y z = z := by
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x = Term.Stuck
    · subst hx; simp [__eo_requires, native_ite, native_teq, native_not] at h
    · exact ⟨rfl, by simp [__eo_requires, native_ite, native_teq, native_not, hx]⟩
  · exact absurd (by simp [__eo_requires, native_ite, native_teq, hxy]) h

private theorem qdiv_rat {a b : Rat} (hb : b ≠ 0) :
    __eo_qdiv (Term.Rational a) (Term.Rational b) = Term.Rational (a / b) := by
  have h0 : native_mk_rational 0 1 = (0 : Rat) := by native_decide
  simp [__eo_qdiv, native_ite, native_qeq, h0, Ne.symm hb, native_qdiv_total]

private theorem upoly_mul_stuck_left' (Q : Term) : __upoly_mul Term.Stuck Q = Term.Stuck := by
  cases Q <;> simp [__upoly_mul]

private theorem upoly_scale_stuck_left (P : Term) : __upoly_scale Term.Stuck P = Term.Stuck := by
  simp [__upoly_scale]

private theorem upoly_scale_stuck_right (c : Term) : __upoly_scale c Term.Stuck = Term.Stuck := by
  cases c <;> simp [__upoly_scale]

private theorem upoly_add_stuck_left' (Q : Term) : __upoly_add Term.Stuck Q = Term.Stuck := by
  simp [__upoly_add]

private theorem upoly_add_stuck_right' (P : Term) : __upoly_add P Term.Stuck = Term.Stuck := by
  cases P <;> simp [__upoly_add]

private theorem chain_shape {a b s : Term} (h : __upoly_rem_seq_chain a b s = Term.Boolean true) :
    a ≠ Term.Stuck ∧ b ≠ Term.Stuck ∧ ∃ ql cl rest, s = seqCons ql cl rest := by
  unfold __upoly_rem_seq_chain at h
  split at h
  · simp at h
  · simp at h
  · simp at h
  · rename_i hA hB; exact ⟨hA, hB, _, _, _, rfl⟩
  · simp at h

/-- One step of `$upoly_rem_seq_chain`, with its `eo::define`s named. -/
private theorem chain_cons_eq (a b ql cl rest : Term) (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __upoly_rem_seq_chain a b (seqCons ql cl rest) =
      let c := __upoly_of_list cl
      let q := __upoly_of_list ql
      let m := __eo_ite (__eo_is_eq q (Term.UOp UserOp._at__at_upoly_zero)) (Term.Rational 1)
        (__eo_qdiv (__eo_mul (__upoly_lc q) (__upoly_lc b)) (__upoly_lc a))
      let r := __upoly_add (__upoly_scale m a)
        (__upoly_scale (Term.Rational (-1)) (__upoly_mul q b))
      let k := __eo_qdiv (__eo_neg (__upoly_lc r)) (__upoly_lc c)
      __eo_ite (__eo_is_eq c (Term.UOp UserOp._at__at_upoly_zero))
        (__eo_and (__eo_is_eq rest Term.__eo_List_nil)
          (__eo_is_eq r (Term.UOp UserOp._at__at_upoly_zero)))
        (__eo_ite (__eo_and (__eo_and
            (__eo_is_eq (__upoly_add r (__upoly_scale k c)) (Term.UOp UserOp._at__at_upoly_zero))
            (__eo_gt (__upoly_deg b) (__upoly_deg c)))
            (__eo_gt (__eo_mul m k) (Term.Rational 0)))
          (__upoly_rem_seq_chain b c rest) (Term.Boolean false)) := by
  have h1 : native_mk_rational 1 1 = (1 : Rat) := by native_decide
  have h0 : native_mk_rational 0 1 = (0 : Rat) := by native_decide
  rw [__upoly_rem_seq_chain.eq_def]
  simp only [seqCons, seqEntry]
  simp [h1, h0]

private theorem deg_lt_of_gt {b c : Term} {pb pc : ℝ[X]} (hb : CPoly b pb) (hc : CPoly c pc)
    (hb0 : pb ≠ 0) (hc0 : pc ≠ 0)
    (h : __eo_gt (__upoly_deg b) (__upoly_deg c) = Term.Boolean true) : pc.degree < pb.degree := by
  rw [upoly_deg_cpoly hb, upoly_deg_cpoly hc] at h
  simp [hb0, hc0, __eo_gt, native_zlt] at h
  rw [degree_eq_natDegree hb0, degree_eq_natDegree hc0]
  exact_mod_cast h

/-- The checked remainder sequence of `a` and `b`, which are multiples of `A` and `B` of one sign
`σ`, is entrywise a multiple of the same sign of the Sturm sequence of `A` and `B`, and then the
zero remainder that ends it. -/
theorem chain_bridge : ∀ (s a b : Term) (pa pb A B : ℝ[X]) (α β : ℝ) (σ : SignType),
    CPoly a pa -> CPoly b pb -> A ≠ 0 -> B ≠ 0 -> α ≠ 0 -> β ≠ 0 ->
    pa = C α * A -> pb = C β * B -> SignType.sign α = σ -> SignType.sign β = σ ->
    __upoly_rem_seq_chain a b s = Term.Boolean true ->
    ∃ Ps, SeqPolys s Ps ∧ Scaled σ (pa :: pb :: Ps) (sturmSeq A B ++ [0]) := by
  intro s
  induction hn : sizeOf s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  intro a b pa pb A B α β σ ha hb hA hB hα hβ hpa hpb hsα hsβ h
  obtain ⟨haS, hbS, ql, cl, rest, rfl⟩ := chain_shape h
  rw [chain_cons_eq a b ql cl rest haS hbS] at h
  simp only at h
  have hpa0 : pa ≠ 0 := by rw [hpa]; exact mul_ne_zero (by simpa using hα) hA
  have hpb0 : pb ≠ 0 := by rw [hpb]; exact mul_ne_zero (by simpa using hβ) hB
  obtain ⟨la, hla, hla0, hla'⟩ := lc_ne_zero_of_cpoly ha hpa0
  obtain ⟨lb, hlb, hlb0, hlb'⟩ := lc_ne_zero_of_cpoly hb hpb0
  -- the remainder `r` is not stuck, in either branch
  have hrS : __upoly_add (__upoly_scale (__eo_ite (__eo_is_eq (__upoly_of_list ql)
        (Term.UOp UserOp._at__at_upoly_zero)) (Term.Rational 1)
        (__eo_qdiv (__eo_mul (__upoly_lc (__upoly_of_list ql)) (__upoly_lc b)) (__upoly_lc a))) a)
      (__upoly_scale (Term.Rational (-1)) (__upoly_mul (__upoly_of_list ql) b)) ≠ Term.Stuck := by
    rcases eo_ite_true h with ⟨_, h'⟩ | ⟨_, h'⟩
    · obtain ⟨_, h2⟩ := eo_and_true' h'
      exact (is_eq_true' h2).2
    · rcases eo_ite_true h' with ⟨h'', _⟩ | ⟨_, h''⟩
      · obtain ⟨h3, _⟩ := eo_and_true' h''
        obtain ⟨h4, _⟩ := eo_and_true' h3
        intro hs; rw [hs, upoly_add_stuck_left'] at h4; exact (is_eq_true' h4).2 rfl
      · cases h''
  -- the quotient `q`
  have hqS : __upoly_of_list ql ≠ Term.Stuck := by
    intro hs; apply hrS
    rw [hs, upoly_mul_stuck_left', upoly_scale_stuck_right, upoly_add_stuck_right']
  obtain ⟨lq, _, hq⟩ := upoly_of_list_cpoly hqS
  set Q := toPoly lq
  -- the multiplier `m`
  obtain ⟨m, hm, hm1⟩ : ∃ m : Rat, __eo_ite (__eo_is_eq (__upoly_of_list ql)
        (Term.UOp UserOp._at__at_upoly_zero)) (Term.Rational 1)
        (__eo_qdiv (__eo_mul (__upoly_lc (__upoly_of_list ql)) (__upoly_lc b)) (__upoly_lc a)) =
        Term.Rational m ∧ (Q = 0 -> m = 1) := by
    by_cases hQ0 : Q = 0
    · have : __upoly_of_list ql = Term.UOp UserOp._at__at_upoly_zero := (cpoly_zero_iff hq).mpr hQ0
      rw [this]; exact ⟨1, by simp [__eo_ite, __eo_is_eq, native_ite, native_teq, native_and,
        native_not], fun _ => rfl⟩
    · have hne : __upoly_of_list ql ≠ Term.UOp UserOp._at__at_upoly_zero :=
        fun h' => hQ0 ((cpoly_zero_iff hq).mp h')
      obtain ⟨lqq, hlqq, _⟩ := upoly_lc_cpoly hq
      refine ⟨lqq * lb / la, ?_, fun h' => absurd h' hQ0⟩
      rw [hlqq, hlb, hla]
      simp [__eo_ite, __eo_is_eq, native_ite, native_teq, native_and, native_not, Ne.symm hne, hqS,
        __eo_mul, native_qmult, qdiv_rat hla0]
  rw [hm] at h hrS
  have hr := upoly_add_cpoly (upoly_scale_cpoly m ha) (upoly_scale_cpoly (-1) (upoly_mul_cpoly hq hb))
  set R := C ((m : Rat) : ℝ) * pa + C (((-1 : Rat)) : ℝ) * (Q * pb)
  rcases eo_ite_true h with ⟨hc0, hT⟩ | ⟨hc0, hT⟩
  · -- the last remainder is zero
    obtain ⟨hcz, hcS⟩ := is_eq_true' hc0
    obtain ⟨hrest, hrz⟩ := eo_and_true' hT
    obtain ⟨hrest, _⟩ := is_eq_true' hrest
    obtain ⟨hrz, _⟩ := is_eq_true' hrz
    subst hrest
    have hR0 : R = 0 := (cpoly_zero_iff hr).mp hrz
    have hm0 : (m : ℝ) ≠ 0 := by
      intro hm0
      have hm0' : m = 0 := by exact_mod_cast hm0
      have hQ : Q = 0 := by
        have : Q * pb = 0 := by
          have := hR0; simp only [R, hm0', Rat.cast_zero, map_zero, zero_mul, zero_add] at this
          simpa using this
        exact (mul_eq_zero.mp this).resolve_right hpb0
      rw [hm1 hQ] at hm0'; exact one_ne_zero hm0'
    have hmod : -A % B = 0 := by
      apply chain_last_poly hm0 hα hβ (q := Q)
      rw [← hpa, ← hpb]
      have := hR0; simp only [R] at this; rw [← this]; simp; ring
    have hseq : sturmSeq A B = [A, B] := by
      rw [sturmSeq_cons hA, sturmSeq_cons hB, hmod]; simp
    refine ⟨[0], SeqPolys.cons ql cl _ 0 [] (hcz ▸ cpoly_zero) SeqPolys.nil, ?_⟩
    rw [hseq]
    have hc : ∃ c : ℝ, SignType.sign c = σ := ⟨α, hsα⟩
    obtain ⟨c, hc⟩ := hc
    have := Scaled.cons c 0 [] [] hc Scaled.nil
    rw [mul_zero] at this
    rw [hpa, hpb]
    exact Scaled.cons α A _ _ hsα (Scaled.cons β B _ _ hsβ this)
  · -- a nonzero remainder
    rcases eo_ite_true hT with ⟨hcond, hrec⟩ | ⟨_, hF⟩
    swap; · cases hF
    obtain ⟨hc12, hmk⟩ := eo_and_true' hcond
    obtain ⟨hzero, hdeg⟩ := eo_and_true' hc12
    obtain ⟨hzero, hzS⟩ := is_eq_true' hzero
    have hcS : __upoly_of_list cl ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_scale_stuck_right, upoly_add_stuck_right'] at hzS; exact hzS rfl
    obtain ⟨lc', _, hc⟩ := upoly_of_list_cpoly hcS
    set Cp := toPoly lc'
    have hCp0 : Cp ≠ 0 := by
      intro h0
      have := (cpoly_zero_iff hc).mpr h0
      rw [this] at hc0; simp [__eo_is_eq, native_and, native_not, native_teq] at hc0
    obtain ⟨lcc, hlcc, hlcc0, _⟩ := lc_ne_zero_of_cpoly hc hCp0
    obtain ⟨lr, hlr, _⟩ := upoly_lc_cpoly hr
    rw [hlr, hlcc] at hzero hmk
    rw [show __eo_neg (Term.Rational lr) = Term.Rational (-lr) by rfl, qdiv_rat hlcc0] at hzero hmk
    set k : Rat := -lr / lcc
    have hRk : R + C ((k : Rat) : ℝ) * Cp = 0 := (cpoly_zero_iff (upoly_add_cpoly hr (upoly_scale_cpoly k hc))).mp hzero
    have hmk' : 0 < m * k := by
      simpa [__eo_mul, __eo_gt, native_qmult, native_qlt] using hmk
    have hm0 : (m : ℝ) ≠ 0 := by
      have : m ≠ 0 := by intro h0; rw [h0, zero_mul] at hmk'; exact lt_irrefl _ hmk'
      exact_mod_cast this
    have hk0 : (k : ℝ) ≠ 0 := by
      have : k ≠ 0 := by intro h0; rw [h0, mul_zero] at hmk'; exact lt_irrefl _ hmk'
      exact_mod_cast this
    have hdegc : Cp.degree < B.degree := by
      have := deg_lt_of_gt hb hc hpb0 hCp0 hdeg
      rwa [hpb, degree_C_mul hβ] at this
    have hstep := chain_step_poly (A := A) (q := Q) (m := (m : ℝ)) (k := (k : ℝ)) (α := α) hB hβ hk0 hdegc
      (by rw [← hpa, ← hpb]; have := hRk; simp only [R] at this; rw [← this]; simp; ring)
    set γ : ℝ := (m : ℝ) * α / k
    have hγ : SignType.sign γ = σ := by
      have hmk'' : (0 : ℝ) < (m : ℝ) * (k : ℝ) := by exact_mod_cast hmk'
      have : 0 < (m : ℝ) / k := by
        have := div_pos_iff.mpr (by
          rcases lt_or_gt_of_ne hk0 with hk | hk
          · exact Or.inr ⟨by nlinarith, hk⟩
          · exact Or.inl ⟨by nlinarith, hk⟩ : (0 < (m:ℝ) ∧ 0 < (k:ℝ)) ∨ ((m:ℝ) < 0 ∧ (k:ℝ) < 0))
        exact this
      rw [show γ = (m : ℝ) / k * α by simp only [γ]; ring, sign_mul, sign_pos this, one_mul, hsα]
    have hγ0 : γ ≠ 0 := by
      intro h0; rw [h0, sign_zero] at hγ; rw [← hγ] at hsα; exact hα (sign_eq_zero_iff.mp hsα)
    have hR0 : -A % B ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hstep; exact hCp0 hstep
    obtain ⟨Ps, hPs, hsc⟩ := ih _ (by subst hn; simp <;> omega) rest rfl b (__upoly_of_list cl) pb Cp B
      (-A % B) β γ σ hb hc hB hR0 hβ hγ0 hpb hstep hsβ hγ hrec
    refine ⟨Cp :: Ps, SeqPolys.cons ql cl rest Cp Ps hc hPs, ?_⟩
    rw [sturmSeq_cons hA, List.cons_append, hpa]
    exact Scaled.cons α A _ _ hsα hsc

private theorem check_shape {P Q s : Term} (h : __upoly_rem_seq_check P Q s = Term.Boolean true) :
    P ≠ Term.Stuck ∧ Q ≠ Term.Stuck ∧
      ∃ q0 l0 q1 l1 rest, s = seqCons q0 l0 (seqCons q1 l1 rest) := by
  unfold __upoly_rem_seq_check at h
  split at h
  · simp at h
  · simp at h
  · simp at h
  · rename_i hP hQ; exact ⟨hP, hQ, _, _, _, _, _, rfl⟩
  · simp at h

private theorem check_cons_eq (P Q q0 l0 q1 l1 rest : Term) (hP : P ≠ Term.Stuck)
    (hQ : Q ≠ Term.Stuck) :
    __upoly_rem_seq_check P Q (seqCons q0 l0 (seqCons q1 l1 rest)) =
      __eo_ite (__eo_or (__eo_is_eq P (Term.UOp UserOp._at__at_upoly_zero))
          (__eo_is_eq Q (Term.UOp UserOp._at__at_upoly_zero))) (Term.Boolean false)
        (__eo_ite (__eo_and (__eo_and
            (__eo_is_eq (__upoly_of_list l0)
              (__upoly_scale (__eo_qdiv (__upoly_lc (__upoly_of_list l0)) (__upoly_lc P)) P))
            (__eo_is_eq (__upoly_of_list l1)
              (__upoly_scale (__eo_qdiv (__upoly_lc (__upoly_of_list l1)) (__upoly_lc Q)) Q)))
            (__eo_gt (__eo_mul (__eo_qdiv (__upoly_lc (__upoly_of_list l0)) (__upoly_lc P))
              (__eo_qdiv (__upoly_lc (__upoly_of_list l1)) (__upoly_lc Q))) (Term.Rational 0)))
          (__upoly_rem_seq_chain (__upoly_of_list l0) (__upoly_of_list l1) rest)
          (Term.Boolean false)) := by
  have h0 : native_mk_rational 0 1 = (0 : Rat) := by native_decide
  rw [__upoly_rem_seq_check.eq_def]
  simp only [seqCons, seqEntry]
  simp [h0]

private theorem first_entry {P L : Term} {p : ℝ[X]} (hP : CPoly P p) (hp : p ≠ 0)
    (h : __eo_is_eq (__upoly_of_list L)
      (__upoly_scale (__eo_qdiv (__upoly_lc (__upoly_of_list L)) (__upoly_lc P)) P) = Term.Boolean true) :
    ∃ c : Rat, __eo_qdiv (__upoly_lc (__upoly_of_list L)) (__upoly_lc P) = Term.Rational c ∧
      CPoly (__upoly_of_list L) (C (c : ℝ) * p) := by
  obtain ⟨hEq, hS⟩ := is_eq_true' h
  obtain ⟨l, _, hL⟩ := upoly_of_list_cpoly hS
  obtain ⟨r1, hr1, _⟩ := upoly_lc_cpoly hL
  obtain ⟨r2, hr2, hr20, _⟩ := lc_ne_zero_of_cpoly hP hp
  rw [hr1, hr2, qdiv_rat hr20] at hEq ⊢
  exact ⟨r1 / r2, rfl, hEq ▸ upoly_scale_cpoly (r1 / r2) hP⟩

/-- A remainder sequence `$upoly_rem_seq_check` accepts for `P` and `Q` is, entry by entry, a
multiple of one sign of the Sturm sequence of `P` and `Q`, and then a zero. -/
theorem rem_seq_check_bridge {P Q s : Term} {p q : ℝ[X]} (hP : CPoly P p) (hQ : CPoly Q q)
    (h : __upoly_rem_seq_check P Q s = Term.Boolean true) :
    p ≠ 0 ∧ q ≠ 0 ∧ ∃ σ : SignType, σ ≠ 0 ∧ ∃ Ps, SeqPolys s Ps ∧
      Scaled σ Ps (sturmSeq p q ++ [0]) := by
  obtain ⟨hPS, hQS, q0, l0, q1, l1, rest, rfl⟩ := check_shape h
  rw [check_cons_eq P Q q0 l0 q1 l1 rest hPS hQS] at h
  rcases eo_ite_true h with ⟨_, hF⟩ | ⟨hz, h⟩
  · cases hF
  have hPz : P ≠ Term.UOp UserOp._at__at_upoly_zero := by
    rintro rfl; simp [__eo_or, __eo_is_eq, native_or, native_and, native_not, native_teq] at hz
  have hQz : Q ≠ Term.UOp UserOp._at__at_upoly_zero := by
    rintro rfl; simp [__eo_or, __eo_is_eq, native_or, native_and, native_not, native_teq] at hz
  have hp : p ≠ 0 := fun h0 => hPz ((cpoly_zero_iff hP).mpr h0)
  have hq : q ≠ 0 := fun h0 => hQz ((cpoly_zero_iff hQ).mpr h0)
  refine ⟨hp, hq, ?_⟩
  rcases eo_ite_true h with ⟨hc, hch⟩ | ⟨_, hF⟩
  swap; · cases hF
  obtain ⟨h12, hgt⟩ := eo_and_true' hc
  obtain ⟨h1, h2⟩ := eo_and_true' h12
  obtain ⟨c0, hc0, hs0⟩ := first_entry hP hp h1
  obtain ⟨c1, hc1, hs1⟩ := first_entry hQ hq h2
  rw [hc0, hc1] at hgt
  have hpos : 0 < c0 * c1 := by
    simpa [__eo_mul, __eo_gt, native_qmult, native_qlt] using hgt
  have hpos' : (0 : ℝ) < (c0 : ℝ) * (c1 : ℝ) := by exact_mod_cast hpos
  have hc00 : (c0 : ℝ) ≠ 0 := by intro h0; rw [h0, zero_mul] at hpos'; exact lt_irrefl _ hpos'
  have hc10 : (c1 : ℝ) ≠ 0 := by intro h0; rw [h0, mul_zero] at hpos'; exact lt_irrefl _ hpos'
  have hsig : SignType.sign (c1 : ℝ) = SignType.sign (c0 : ℝ) := by
    rcases lt_or_gt_of_ne hc00 with h0 | h0
    · have : (c1 : ℝ) < 0 := by nlinarith
      rw [sign_neg h0, sign_neg this]
    · have : (0 : ℝ) < c1 := by nlinarith
      rw [sign_pos h0, sign_pos this]
  refine ⟨SignType.sign (c0 : ℝ), by simpa using hc00, ?_⟩
  obtain ⟨Ps, hPs, hsc⟩ := chain_bridge rest _ _ _ _ p q (c0 : ℝ) (c1 : ℝ) _ hs0 hs1 hp hq hc00 hc10
    rfl rfl rfl hsig hch
  exact ⟨_, SeqPolys.cons q0 l0 _ _ _ hs0 (SeqPolys.cons q1 l1 rest _ _ hs1 hPs), hsc⟩

/-! ### Sign variations -/

private theorem sign_rat_cast (x : Rat) : SignType.sign (x : ℝ) = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
  · simp
  · rw [sign_pos h, sign_pos (by exact_mod_cast h)]

/-- `$sign_variations_rec x` counts the sign variations of a list of rationals, after `x` when it
is not zero. -/
theorem sign_variations_rec_eq : ∀ {t : Term} {vs : List Rat}, RatList t vs -> ∀ x : Rat,
    __sign_variations_rec (Term.Rational x) t =
      Term.Numeral (if x = 0 then (List.signVariations vs : Int)
        else (List.signVariations (x :: vs) : Int)) := by
  intro t vs h
  induction h with
  | nil => intro x; split <;> simp [__sign_variations_rec]
  | cons y q l hq ih =>
      intro x
      have h0 : native_mk_rational 0 1 = (0 : Rat) := by native_decide
      have hEq : __sign_variations_rec (Term.Rational x)
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Rational y)) q) =
          __eo_ite (__eo_is_eq (Term.Rational y) (Term.Rational 0)) (__sign_variations_rec (Term.Rational x) q)
            (__eo_ite (__eo_and (__eo_not (__eo_is_eq (Term.Rational x) (Term.Rational 0)))
                (__eo_not (__eo_is_eq (__eo_is_neg (Term.Rational x)) (__eo_is_neg (Term.Rational y)))))
              (__eo_add (Term.Numeral 1) (__sign_variations_rec (Term.Rational y) q))
              (__sign_variations_rec (Term.Rational y) q)) := by
        simp [__sign_variations_rec, h0]
      rw [hEq]
      by_cases hy : y = 0
      · subst hy
        simp [__eo_ite, __eo_is_eq, native_ite, native_teq, native_and, native_not, ih x]
      · by_cases hx : x = 0
        · subst hx
          simp [__eo_ite, __eo_is_eq, native_ite, native_teq, native_and, native_not, __eo_not,
            __eo_and, Ne.symm hy, ih, hy]
        · rw [List.signVariations_cons_cons_of_ne_zero _ hx hy]
          rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy' <;>
            simp [__eo_ite, __eo_is_eq, native_ite, native_teq, native_and, native_not, __eo_not,
              __eo_and, __eo_is_neg, native_qlt, h0, Ne.symm hy, Ne.symm hx, hx, hy, ih,
              __eo_add, native_zplus, sign_neg, sign_pos, hx', hy', not_lt.mpr (le_of_lt hx'),
              not_lt.mpr (le_of_lt hy')] <;> ring

/-- The value `$cov_seq_values` reads off the entry `cl` at `v`. -/
def seqElem (cl v : Term) : Term :=
  __eo_ite (__eo_is_eq v (Term.UOp UserOp._at__at_cov_minus_inf))
    (__eo_ite (__eo_or (Term.Boolean false)
        (__eo_is_eq (__eo_zmod (__upoly_deg (__upoly_of_list cl)) (Term.Numeral 2)) (Term.Numeral 0)))
      (__upoly_lc (__upoly_of_list cl)) (__eo_neg (__upoly_lc (__upoly_of_list cl))))
    (__eo_ite (__eo_is_eq v (Term.UOp UserOp._at__at_cov_plus_inf))
      (__eo_ite (__eo_or (Term.Boolean true)
          (__eo_is_eq (__eo_zmod (__upoly_deg (__upoly_of_list cl)) (Term.Numeral 2)) (Term.Numeral 0)))
        (__upoly_lc (__upoly_of_list cl)) (__eo_neg (__upoly_lc (__upoly_of_list cl))))
      (__upoly_eval (__upoly_of_list cl) v))

private theorem eo_is_list_of_ratList {q : Term} {l : List Rat} (h : RatList q l) :
    __eo_is_list Term.__eo_List_cons q = Term.Boolean true := by
  induction h with
  | nil => rfl
  | cons a p l hp ih =>
      have hp' := hp.ne_stuck
      simp only [__eo_is_list, __eo_is_ok] at ih ⊢
      simp [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not] at ih ⊢
      exact ih

theorem seq_values_gen (v : Term) (hv : v ≠ Term.Stuck) (g : ℝ[X] -> SignType)
    (helem : ∀ cl p, CPoly (__upoly_of_list cl) p ->
      ∃ x : Rat, seqElem cl v = Term.Rational x ∧ SignType.sign (x : ℝ) = g p) :
    ∀ {s Ps}, SeqPolys s Ps -> ∃ vs : List Rat, RatList (__cov_seq_values s v) vs ∧
      vs.map (fun x : Rat => SignType.sign (x : ℝ)) = Ps.map g := by
  intro s Ps h
  induction h with
  | nil => exact ⟨[], by cases v <;> simp_all [__cov_seq_values] <;> exact RatList.nil, rfl⟩
  | cons ql cl rest p Ps hp _ ih =>
      obtain ⟨vs, hvs, hmap⟩ := ih
      obtain ⟨x, hx, hxg⟩ := helem cl p hp
      have hEq : __cov_seq_values (seqCons ql cl rest) v =
          __eo_cons Term.__eo_List_cons (seqElem cl v) (__cov_seq_values rest v) := by
        rw [__cov_seq_values.eq_def]
        cases v <;> simp_all [seqElem]
      rw [hEq, hx]
      refine ⟨x :: vs, ?_, by simp [hxg, hmap]⟩
      simp only [__eo_cons, eo_is_list_of_ratList hvs, __eo_requires, native_ite, native_teq,
        native_not]
      simp
      exact RatList.cons x _ vs hvs

theorem seqElem_rat (r : Rat) : ∀ cl p, CPoly (__upoly_of_list cl) p ->
    ∃ x : Rat, seqElem cl (Term.Rational r) = Term.Rational x ∧
      SignType.sign (x : ℝ) = SignType.sign (p.eval (r : ℝ)) := by
  intro cl p hp
  obtain ⟨x, hx, hx'⟩ := upoly_eval_cpoly hp r
  refine ⟨x, ?_, by rw [hx']⟩
  simp [seqElem, __eo_ite, __eo_is_eq, native_ite, native_teq, native_and, native_not, hx]

private theorem zmod_deg (p : ℝ[X]) (hp : p ≠ 0) :
    __eo_is_eq (__eo_zmod (Term.Numeral (p.natDegree : Int)) (Term.Numeral 2)) (Term.Numeral 0) =
      Term.Boolean (decide (Even p.natDegree)) := by
  have : (0 = (p.natDegree : Int) % 2) ↔ Even p.natDegree := by rw [Nat.even_iff]; omega
  simp [__eo_zmod, __eo_is_eq, native_ite, native_zeq, native_mod_total, native_teq, native_and,
    native_not, this]

theorem seqElem_minf : ∀ cl p, CPoly (__upoly_of_list cl) p ->
    ∃ x : Rat, seqElem cl (Term.UOp UserOp._at__at_cov_minus_inf) = Term.Rational x ∧
      SignType.sign (x : ℝ) = signNegInf p := by
  intro cl p hp
  obtain ⟨lc, hlc, hlc'⟩ := upoly_lc_cpoly hp
  by_cases hp0 : p = 0
  · subst hp0
    rw [leadingCoeff_zero] at hlc'
    have : lc = 0 := by exact_mod_cast hlc'
    subst this
    refine ⟨0, ?_, by simp [signNegInf]⟩
    rw [seqElem, upoly_deg_cpoly hp, hlc]
    simp [__eo_ite, __eo_is_eq, __eo_or, __eo_zmod, __eo_neg, native_ite, native_teq, native_and,
      native_not, native_or, native_zeq, native_mod_total, native_qneg]
  · by_cases he : Even p.natDegree
    · refine ⟨lc, ?_, by simp [signNegInf, he, hlc']⟩
      rw [seqElem, upoly_deg_cpoly hp]
      simp only [hp0, ↓reduceIte]
      rw [zmod_deg p hp0, hlc]
      simp [__eo_ite, __eo_is_eq, __eo_or, native_ite, native_teq, native_and, native_not,
        native_or, he]
    · refine ⟨-lc, ?_, by simp [signNegInf, he, ← hlc', Left.sign_neg]⟩
      rw [seqElem, upoly_deg_cpoly hp]
      simp only [hp0, ↓reduceIte]
      rw [zmod_deg p hp0, hlc]
      simp [__eo_ite, __eo_is_eq, __eo_or, __eo_neg, native_ite, native_teq, native_and, native_not,
        native_or, he, native_qneg]

theorem seqElem_pinf : ∀ cl p, CPoly (__upoly_of_list cl) p ->
    ∃ x : Rat, seqElem cl (Term.UOp UserOp._at__at_cov_plus_inf) = Term.Rational x ∧
      SignType.sign (x : ℝ) = signPosInf p := by
  intro cl p hp
  obtain ⟨lc, hlc, hlc'⟩ := upoly_lc_cpoly hp
  refine ⟨lc, ?_, by rw [signPosInf, hlc']⟩
  rw [seqElem, upoly_deg_cpoly hp, hlc]
  split <;> simp [__eo_ite, __eo_is_eq, __eo_or, __eo_zmod, native_ite, native_teq, native_and,
    native_not, native_or, native_zeq, native_mod_total]

private theorem signType_sign (x : SignType) : SignType.sign x = x := by
  cases x <;> rfl

theorem signVariations_append_zero {α : Type*} [Zero α] [LinearOrder α] (l : List α) :
    List.signVariations (l ++ [0]) = List.signVariations l := by
  simp [List.signVariations, List.filter_append]

/-- Scaling by constants of one sign leaves the sign variations of a sign reading unchanged. -/
theorem signVariations_scaled_sign {σ : SignType} (hσ : σ ≠ 0) {L L' : List ℝ[X]}
    (h : Scaled σ L L') (g : ℝ[X] -> SignType)
    (hg : ∀ c p, g (C c * p) = SignType.sign c * g p) :
    List.signVariations (L.map g) = List.signVariations (L'.map g) := by
  have hs : L.map g = (L'.map g).map (σ * ·) := by
    induction h with
    | nil => rfl
    | cons c p L L' hc _ ih => simp [hg, ih, hc]
  rw [hs]
  rcases σ with _ | _ | _
  · exact absurd rfl hσ
  · exact List.signVariations_map_of_sign_eq_neg (fun x => by cases x <;> rfl) _
  · exact List.signVariations_map (fun x => by cases x <;> rfl) _

/-- The sign variations the checker computes on a remainder sequence, read by `g`. -/
theorem seq_sign_variations (v : Term) (hv : v ≠ Term.Stuck) (g : ℝ[X] -> SignType)
    (helem : ∀ cl p, CPoly (__upoly_of_list cl) p ->
      ∃ x : Rat, seqElem cl v = Term.Rational x ∧ SignType.sign (x : ℝ) = g p)
    (hg : ∀ c p, g (C c * p) = SignType.sign c * g p) (hg0 : g 0 = 0)
    {s : Term} {Ps : List ℝ[X]} {p q : ℝ[X]} {σ : SignType} (hσ : σ ≠ 0)
    (hS : SeqPolys s Ps) (hsc : Scaled σ Ps (sturmSeq p q ++ [0])) :
    __sign_variations_rec (Term.Rational 0) (__cov_seq_values s v) =
      Term.Numeral (List.signVariations ((sturmSeq p q).map g) : Int) := by
  obtain ⟨vs, hvs, hmap⟩ := seq_values_gen v hv g helem hS
  have h0 : native_mk_rational 0 1 = (0 : Rat) := by native_decide
  rw [sign_variations_rec_eq hvs 0]
  simp only [↓reduceIte]
  congr 2
  have h1 : List.signVariations vs = List.signVariations (Ps.map g) := by
    apply List.signVariations_congr
    rw [← hmap]
    simp [Function.comp_def, sign_rat_cast, signType_sign]
  rw [h1, signVariations_scaled_sign hσ hsc g hg, List.map_append, List.map_singleton, hg0,
    signVariations_append_zero]

theorem g_point (r : ℝ) : ∀ c (p : ℝ[X]),
    SignType.sign ((C c * p).eval r) = SignType.sign c * SignType.sign (p.eval r) := by
  intro c p; simp [sign_mul]

theorem g_posInf : ∀ c (p : ℝ[X]), signPosInf (C c * p) = SignType.sign c * signPosInf p := by
  intro c p; simp [signPosInf, leadingCoeff_mul, sign_mul]

theorem g_negInf : ∀ c (p : ℝ[X]), signNegInf (C c * p) = SignType.sign c * signNegInf p := by
  intro c p
  by_cases hc : c = 0
  · subst hc; simp [signNegInf]
  · simp only [signNegInf, natDegree_C_mul hc, leadingCoeff_mul, leadingCoeff_C, sign_mul]
    split <;> simp [mul_neg]

/-! ### Divisibility -/

theorem upoly_monomial_cpoly (c : Rat) :
    ∀ (f : Term) (k : Int), __upoly_monomial (Term.Rational c) (Term.Numeral k) f ≠ Term.Stuck ->
      ∃ M, CPoly (__upoly_monomial (Term.Rational c) (Term.Numeral k) f) M := by
  intro f
  induction hn : sizeOf f using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  intro k h
  by_cases hk : k = 0
  · subst hk
    have hEq : __upoly_monomial (Term.Rational c) (Term.Numeral 0) f =
        upolyCons c (Term.UOp UserOp._at__at_upoly_zero) := by
      have hfS : f ≠ Term.Stuck := by rintro rfl; simp [__upoly_monomial] at h
      cases f <;> simp_all [__upoly_monomial, upolyCons, __eo_and, __eo_is_eq, native_teq,
        native_and, native_not]
    rw [hEq]
    exact ⟨_, upolyCons_cpoly cpoly_zero c⟩
  · rw [__upoly_monomial.eq_def] at h ⊢
    split at h
    all_goals try exact absurd rfl h
    · rename_i heq _ _; cases heq; exact absurd rfl hk
    · rename_i _ _ _ x f' _ _ _
      simp only at h ⊢
      have hEq : __eo_add (Term.Numeral k) (Term.Numeral (-1)) = Term.Numeral (k - 1) := by
        simp [__eo_add, native_zplus]; ring
      rw [hEq] at h ⊢
      have hv : __upoly_monomial (Term.Rational c) (Term.Numeral (k - 1)) f' ≠ Term.Stuck := by
        intro hs; rw [hs] at h
        simp [__eo_ite, __eo_and, __eo_is_eq, __eo_cons, __eo_is_list, __eo_requires, native_ite,
          native_teq, native_and, native_not] at h
      obtain ⟨M, hM⟩ := ih _ (by subst hn; simp <;> omega) f' rfl (k - 1) hv
      have := upolyCons_cpoly hM 0
      refine ⟨_, (show upolyCons 0 _ = _ from ?_) ▸ this⟩
      simp [upolyCons, __eo_and, __eo_is_eq, native_teq, native_and, native_not,
        native_mk_rational_zero']

/-- `$upoly_divides_rec b a f` reduces `a` by multiples of `b`, so it only succeeds when `b`
divides `a`. -/
theorem upoly_divides_sound {b : Term} {pb : ℝ[X]} (hb : CPoly b pb) (hb0 : pb ≠ 0) :
    ∀ (f a : Term) (pa : ℝ[X]), CPoly a pa ->
      __upoly_divides_rec b a f = Term.Boolean true -> pb ∣ pa := by
  intro f
  induction hn : sizeOf f using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  intro a pa ha h
  rw [__upoly_divides_rec.eq_def] at h
  split at h
  all_goals try exact absurd rfl h
  all_goals try (simp at h; done)
  · -- `a` is zero
    have := (cpoly_zero_iff ha).mp rfl
    rw [this]; exact dvd_zero _
  · simp only at h
    rcases eo_ite_true h with ⟨_, hF⟩ | ⟨_, h⟩
    · cases hF
    obtain ⟨la, hla, _⟩ := upoly_lc_cpoly ha
    obtain ⟨lb, hlb, hlb0, _⟩ := lc_ne_zero_of_cpoly hb hb0
    rw [hla, hlb, qdiv_rat hlb0, upoly_deg_cpoly ha, upoly_deg_cpoly hb] at h
    simp only [show ∀ q : Rat, __eo_neg (Term.Rational q) = Term.Rational (-q) from fun _ => rfl,
      show ∀ x y : Int, __eo_add (Term.Numeral x) (__eo_neg (Term.Numeral y)) = Term.Numeral (x + -y)
        from fun _ _ => rfl] at h
    by_cases hM : __upoly_monomial (Term.Rational (-(la / lb)))
        (Term.Numeral ((if pa = 0 then -1 else (pa.natDegree : Int)) +
          -(if pb = 0 then -1 else (pb.natDegree : Int)))) a = Term.Stuck
    · rw [hM, upoly_mul_stuck_left', upoly_add_stuck_right'] at h
      simp [__upoly_divides_rec] at h
    · obtain ⟨Mp, hMp⟩ := upoly_monomial_cpoly _ a _ hM
      have hnew := upoly_add_cpoly ha (upoly_mul_cpoly hMp hb)
      have := ih _ (by subst hn; simp <;> omega) _ rfl _ _ hnew h
      exact (dvd_add_left (dvd_mul_left pb Mp)).mp this

private theorem upoly_of_term_atom_cpoly (x t : Term) (hx : x ≠ Term.Stuck)
    (h : upolyOfTermAtom x t ≠ Term.Stuck) : ∃ p, CPoly (upolyOfTermAtom x t) p := by
  have hm1 : native_mk_rational 1 1 = (1 : Rat) := by native_decide
  by_cases hq : ∃ q : Rat, __eo_to_q t = Term.Rational q
  · rcases hq with ⟨q, hq⟩
    refine ⟨_, (show upolyCons q UZ = _ from ?_) ▸ upolyCons_cpoly cpoly_zero q⟩
    simp [upolyOfTermAtom, hq, upolyCons, __eo_is_q, __eo_is_q_internal, __eo_ite, __eo_and,
      __eo_is_eq, native_ite, native_teq, native_and, native_not]
  · have hnq : __eo_to_q t = Term.Stuck := by
      cases t with
      | Numeral n => exact absurd ⟨_, rfl⟩ hq
      | Rational q => exact absurd ⟨q, rfl⟩ hq
      | _ => rfl
    have hEq : upolyOfTermAtom x t =
        __eo_requires t x (UC native_mk_rational 0 1, (UC native_mk_rational 1 1, UZ)) := by
      simp [upolyOfTermAtom, hnq, __eo_is_q, __eo_is_q_internal, __eo_ite, native_and,
        native_not, native_teq, native_ite]
    rw [hEq] at h ⊢
    obtain ⟨_, hb⟩ := eo_requires_eq_body' h
    rw [hb, hm1, native_mk_rational_zero']
    refine ⟨_, ⟨[0, 1], UPolyWf.cons 0 _ _ (UPolyWf.cons 1 _ _ UPolyWf.zero), ?_, rfl⟩⟩
    intro _; simp

/-- `$upoly_of_term` always produces a canonical polynomial. -/
theorem upoly_of_term_cpoly (x : Term) (hx : x ≠ Term.Stuck) :
    ∀ t, __upoly_of_term x t ≠ Term.Stuck -> ∃ p, CPoly (__upoly_of_term x t) p := by
  intro t
  induction hn : sizeOf t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
  intro h
  have ht : t ≠ Term.Stuck := by
    intro hs; subst hs; cases x <;> simp_all [__upoly_of_term]
  rcases upoly_of_term_cases x t hx ht with
    ⟨a1, rfl, hEq⟩ | ⟨a1, a2, rfl, hEq⟩ | ⟨a1, a2, rfl, hEq⟩ | ⟨a1, a2, rfl, hEq⟩ |
    ⟨a1, rfl, hEq⟩ | hEq <;> rw [hEq] at h ⊢
  · have h1 : __upoly_of_term x a1 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_scale_stuck_right] at h; exact h rfl
    obtain ⟨p, hp⟩ := ih _ (by subst hn; simp <;> omega) a1 rfl h1
    exact ⟨_, upoly_scale_cpoly (-1) hp⟩
  · have h1 : __upoly_of_term x a1 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_add_stuck_left'] at h; exact h rfl
    have h2 : __upoly_of_term x a2 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_add_stuck_right'] at h; exact h rfl
    obtain ⟨p, hp⟩ := ih _ (by subst hn; simp <;> omega) a1 rfl h1
    obtain ⟨q, hq⟩ := ih _ (by subst hn; simp <;> omega) a2 rfl h2
    exact ⟨_, upoly_add_cpoly hp hq⟩
  · have h1 : __upoly_of_term x a1 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_add_stuck_left'] at h; exact h rfl
    have h2 : __upoly_of_term x a2 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_scale_stuck_right, upoly_add_stuck_right'] at h; exact h rfl
    obtain ⟨p, hp⟩ := ih _ (by subst hn; simp <;> omega) a1 rfl h1
    obtain ⟨q, hq⟩ := ih _ (by subst hn; simp <;> omega) a2 rfl h2
    exact ⟨_, upoly_add_cpoly hp (upoly_scale_cpoly (-1) hq)⟩
  · have h1 : __upoly_of_term x a1 ≠ Term.Stuck := by
      intro hs; rw [hs, upoly_mul_stuck_left'] at h; exact h rfl
    have h2 : __upoly_of_term x a2 ≠ Term.Stuck := by
      intro hs; rw [hs] at h; simp [__upoly_mul] at h
    obtain ⟨p, hp⟩ := ih _ (by subst hn; simp <;> omega) a1 rfl h1
    obtain ⟨q, hq⟩ := ih _ (by subst hn; simp <;> omega) a2 rfl h2
    exact ⟨_, upoly_mul_cpoly hp hq⟩
  · exact ih _ (by subst hn; simp <;> omega) a1 rfl h
  · exact upoly_of_term_atom_cpoly x t hx h

end CoveringsProofs
