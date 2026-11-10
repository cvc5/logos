module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoveringsSupport
import all Cpc.Proofs.RuleSupport.CoveringsSupport

open Eo
open SmtEval
open Smtm
open CoveringsProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

local notation "MINF" => Term.UOp UserOp._at__at_cov_minus_inf
local notation "PINF" => Term.UOp UserOp._at__at_cov_plus_inf

/-- The check `$cov_endpoint_ok` makes of the lower endpoint `l`, with the witness `lo`. -/
private def endL (P l lo sl : Term) : Term :=
  __eo_ite (__eo_or (__eo_is_eq l MINF) (__eo_is_eq l PINF))
    (__eo_and (__eo_and (__eo_is_eq lo l) (__eo_is_eq sl Term.__eo_List_nil))
      (__eo_is_eq (Term.Boolean true) (__eo_is_eq l MINF)))
    (__eo_ite (__eo_is_q lo)
      (__eo_and (__eo_and (__cov_is_root P l sl)
          (__eo_not (__eo_is_eq (__upoly_eval P lo) (Term.Rational 0))))
        (__cov_lt lo l))
      (Term.Boolean false))

/-- The check `$cov_endpoint_ok` makes of the upper endpoint `r`, with the witness `hi`. -/
private def endR (P r hi sr : Term) : Term :=
  __eo_ite (__eo_or (__eo_is_eq r MINF) (__eo_is_eq r PINF))
    (__eo_and (__eo_and (__eo_is_eq hi r) (__eo_is_eq sr Term.__eo_List_nil))
      (__eo_is_eq (Term.Boolean false) (__eo_is_eq r MINF)))
    (__eo_ite (__eo_is_q hi)
      (__eo_and (__eo_and (__cov_is_root P r sr)
          (__eo_not (__eo_is_eq (__upoly_eval P hi) (Term.Rational 0))))
        (__cov_lt r hi))
      (Term.Boolean false))

private def finCount (e : Term) : Term :=
  __eo_ite (__eo_or (__eo_is_eq e MINF) (__eo_is_eq e PINF)) (Term.Numeral 0) (Term.Numeral 1)

private def varsAt (s v : Term) : Term :=
  __sign_variations_rec (Term.Rational 0) (__cov_seq_values s v)

private theorem prog_sgn_inv_intro_inv (p l r lo hi s sl sr : Term)
    (h : __eo_prog_sgn_inv_intro p l r lo hi s sl sr ≠ Term.Stuck) :
    __upoly_rem_seq_check (__upoly_of_term (__upoly_term_var p) p)
        (__upoly_derivative (__upoly_of_term (__upoly_term_var p) p)) s = Term.Boolean true ∧
    endL (__upoly_of_term (__upoly_term_var p) p) l lo sl = Term.Boolean true ∧
    endR (__upoly_of_term (__upoly_term_var p) p) r hi sr = Term.Boolean true ∧
    __eo_is_eq (__eo_add (varsAt s lo) (__eo_neg (varsAt s hi)))
        (__eo_add (finCount l) (finCount r)) = Term.Boolean true ∧
    l ≠ Term.Stuck ∧ r ≠ Term.Stuck ∧
    __eo_prog_sgn_inv_intro p l r lo hi s sl sr =
      Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv
        (__upoly_to_list (__upoly_of_term (__upoly_term_var p) p))) l) r := by
  have h0 : native_mk_rational 0 1 = (0 : Rat) := by native_decide
  unfold __eo_prog_sgn_inv_intro at h ⊢
  split at h
  all_goals try exact absurd rfl h
  rename_i _ _ _ _ _ _ _ _ hp hl hr hlo hhi hs hsl hsr
  simp only at h ⊢
  obtain ⟨hc, hb⟩ := eo_requires_eq_body h
  rw [hb]
  rcases eo_ite_true_cases hc with ⟨hrem, hc⟩ | ⟨_, hc⟩
  swap; · cases hc
  rcases eo_ite_true_cases hc with ⟨hends, hcount⟩ | ⟨_, hc⟩
  swap; · cases hc
  obtain ⟨hL, hR⟩ := eo_and_true_inv hends
  refine ⟨hrem, by simpa [endL, h0] using hL, by simpa [endR, h0] using hR,
    by simpa [varsAt, finCount, h0] using hcount, hl, hr, ?_⟩
  simp [__eo_mk_apply]

private theorem or_false_inv {a b : Term} (h : __eo_or a b = Term.Boolean false) :
    a = Term.Boolean false ∧ b = Term.Boolean false := by
  cases a <;> cases b <;> simp_all [__eo_or, native_or]
  all_goals first
    | (simp [__eo_requires, native_ite, native_teq, native_not] at h; split at h <;> simp_all)
    | skip

private theorem is_eq_true_inv {a b : Term} (h : __eo_is_eq a b = Term.Boolean true) : a = b := by
  simp [__eo_is_eq, native_and, native_not, native_teq] at h
  exact h.2.2.symm

private theorem is_eq_false_ne {a b : Term} (h : __eo_is_eq a b = Term.Boolean false)
    (hb : b ≠ Term.Stuck) : a ≠ b := by
  rintro rfl
  have ha : a ≠ Term.Stuck := hb
  simp [__eo_is_eq, native_and, native_not, native_teq, ha] at h

private theorem eo_not_true_inv {x : Term} (h : __eo_not x = Term.Boolean true) :
    x = Term.Boolean false := by
  cases x <;> simp_all [__eo_not, native_not]

private theorem endL_cases {P l lo sl : Term} (h : endL P l lo sl = Term.Boolean true) :
    (l = MINF ∧ lo = MINF) ∨
    (l ≠ MINF ∧ l ≠ PINF ∧ ∃ a : Rat, lo = Term.Rational a ∧
      __cov_is_root P l sl = Term.Boolean true ∧
      __eo_is_eq (__upoly_eval P lo) (Term.Rational 0) = Term.Boolean false ∧
      __cov_lt lo l = Term.Boolean true) := by
  unfold endL at h
  rcases eo_ite_true_cases h with ⟨_, h⟩ | ⟨hinf, h⟩
  · left
    obtain ⟨h12, h3⟩ := eo_and_true_inv h
    obtain ⟨h1, _⟩ := eo_and_true_inv h12
    have h3 := is_eq_true_inv h3
    have hl := is_eq_true_inv h3.symm
    exact ⟨hl, (is_eq_true_inv h1).trans hl⟩
  · right
    obtain ⟨hm, hp⟩ := or_false_inv hinf
    refine ⟨is_eq_false_ne hm (by simp), is_eq_false_ne hp (by simp), ?_⟩
    rcases eo_ite_true_cases h with ⟨hq, h⟩ | ⟨_, h⟩
    swap; · cases h
    have ha : ∃ a, lo = Term.Rational a := by
      cases lo <;> simp_all [__eo_is_q, __eo_is_q_internal, native_and, native_not, native_teq]
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨h12, h3⟩ := eo_and_true_inv h
    obtain ⟨h1, h2⟩ := eo_and_true_inv h12
    exact ⟨a, rfl, h1, eo_not_true_inv h2, h3⟩

private theorem endR_cases {P r hi sr : Term} (h : endR P r hi sr = Term.Boolean true) :
    (r = PINF ∧ hi = PINF) ∨
    (r ≠ MINF ∧ r ≠ PINF ∧ ∃ b : Rat, hi = Term.Rational b ∧
      __cov_is_root P r sr = Term.Boolean true ∧
      __eo_is_eq (__upoly_eval P hi) (Term.Rational 0) = Term.Boolean false ∧
      __cov_lt r hi = Term.Boolean true) := by
  unfold endR at h
  rcases eo_ite_true_cases h with ⟨hinf, h⟩ | ⟨hinf, h⟩
  · left
    obtain ⟨h12, h3⟩ := eo_and_true_inv h
    obtain ⟨h1, _⟩ := eo_and_true_inv h12
    have h3 := is_eq_true_inv h3
    have hm : r ≠ MINF := is_eq_false_ne h3.symm (by simp)
    have hp : r = PINF := by
      by_contra hp
      have hpf : __eo_is_eq r PINF = Term.Boolean false := by
        have hrS : r ≠ Term.Stuck := by
          rintro rfl; simp [__eo_or, __eo_is_eq, native_or, native_and, native_not, native_teq] at hinf
        simp [__eo_is_eq, native_and, native_not, native_teq, hrS, Ne.symm hp]
      rw [← h3, hpf] at hinf
      simp [__eo_or, native_or] at hinf
    exact ⟨hp, (is_eq_true_inv h1).trans hp⟩
  · right
    obtain ⟨hm, hp⟩ := or_false_inv hinf
    refine ⟨is_eq_false_ne hm (by simp), is_eq_false_ne hp (by simp), ?_⟩
    rcases eo_ite_true_cases h with ⟨hq, h⟩ | ⟨_, h⟩
    swap; · cases h
    have hb : ∃ b, hi = Term.Rational b := by
      cases hi <;> simp_all [__eo_is_q, __eo_is_q_internal, native_and, native_not, native_teq]
    obtain ⟨b, rfl⟩ := hb
    obtain ⟨h12, h3⟩ := eo_and_true_inv h
    obtain ⟨h1, h2⟩ := eo_and_true_inv h12
    exact ⟨b, rfl, h1, eo_not_true_inv h2, h3⟩

private theorem finCount_inf (e : Term) (h : e = MINF ∨ e = PINF) : finCount e = Term.Numeral 0 := by
  rcases h with rfl | rfl <;>
    simp [finCount, __eo_ite, __eo_or, __eo_is_eq, native_ite, native_teq, native_and, native_not,
      native_or]

private theorem finCount_fin (e : Term) (hS : e ≠ Term.Stuck) (h1 : e ≠ MINF) (h2 : e ≠ PINF) :
    finCount e = Term.Numeral 1 := by
  simp [finCount, __eo_ite, __eo_or, __eo_is_eq, native_ite, native_teq, native_and, native_not,
    native_or, hS, Ne.symm h1, Ne.symm h2]

/-! ### No root between the endpoints -/

private theorem const_sign_of_no_root (f : Polynomial ℝ) (S : Set ℝ) (hS : IsPreconnected S)
    (h : ∀ v ∈ S, f.eval v ≠ 0) : ∃ τ : SignType, ∀ v ∈ S, SignType.sign (f.eval v) = τ := by
  by_cases hne : S.Nonempty
  · obtain ⟨v0, hv0⟩ := hne
    exact ⟨_, fun v hv => SturmTarski.IsPreconnected.sign_eq_of_continuousOn hS
      (f.continuousOn) h hv hv0⟩
  · exact ⟨0, fun v hv => absurd ⟨v, hv⟩ hne⟩

private theorem interval_ordConnected (M : SmtModel) (l r : Term) :
    ({v | InL M l v ∧ InR M r v} : Set ℝ).OrdConnected := by
  constructor
  intro x hx y hy z hz
  refine ⟨?_, ?_⟩
  · rcases hx.1 with h | h; exact Or.inl h; exact Or.inr (lt_of_lt_of_le h hz.1)
  · rcases hy.2 with h | h; exact Or.inl h; exact Or.inr (lt_of_le_of_lt hz.2 h)

private theorem card_lt_of_mem {s : Finset ℝ} {xs : Finset ℝ} (hsub : xs ⊆ s) :
    xs.card ≤ s.card := Finset.card_le_card hsub

private theorem sgn_inv_intro_sound (M : SmtModel) (hM : model_wf M)
    (p l r lo hi s sl sr : Term)
    (hlT : CovEndpointOk l) (hrT : CovEndpointOk r)
    (hTy : __eo_typeof (__eo_prog_sgn_inv_intro p l r lo hi s sl sr) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_sgn_inv_intro p l r lo hi s sl sr) ∧
    eo_interprets M (__eo_prog_sgn_inv_intro p l r lo hi s sl sr) true := by
  have hProg := term_ne_stuck_of_typeof_bool hTy
  obtain ⟨hrem, hL, hR, hcount, hlS, hrS, hEq⟩ := prog_sgn_inv_intro_inv p l r lo hi s sl sr hProg
  rw [hEq] at hTy ⊢
  set P := __upoly_of_term (__upoly_term_var p) p
  -- the polynomial and its Sturm sequence
  have hPS : P ≠ Term.Stuck := (check_shape hrem).1
  have hxS : __upoly_term_var p ≠ Term.Stuck := by
    intro hs; apply hPS; simp only [P, hs]; simp [__upoly_of_term]
  obtain ⟨pp, hP⟩ := upoly_of_term_cpoly _ hxS p hPS
  obtain ⟨_, _, σ, hσ, Ps, hSq, hsc⟩ := rem_seq_check_bridge hP (upoly_derivative_cpoly hP) hrem
  have hpp0 : pp ≠ 0 := (rem_seq_check_bridge hP (upoly_derivative_cpoly hP) hrem).1
  obtain ⟨lst, hwf, hcanon, hpp⟩ := hP
  have hP : CPoly P pp := ⟨lst, hwf, hcanon, hpp⟩
  have hList := upoly_to_list_of_wf hwf
  -- the Eunoia types of the endpoints
  have hT : __eo_typeof__at_sgn_inv (__eo_typeof (__upoly_to_list P)) (__eo_typeof l)
      (__eo_typeof r) = Term.Bool := hTy
  have hlR : __eo_typeof l = Term.UOp UserOp.Real ∧ __eo_typeof r = Term.UOp UserOp.Real := by
    unfold __eo_typeof__at_sgn_inv at hT
    split at hT
    · rename_i h1 h2 h3; exact ⟨h2, h3⟩
    · cases hT
  have hfin : ∀ e, CovEndpointOk e -> __eo_typeof e = Term.UOp UserOp.Real -> e ≠ MINF -> e ≠ PINF ->
      ∀ P' st, __cov_is_root P' e st = Term.Boolean true -> FinEnd e := by
    intro e he heT hm hp P' st hroot
    have hT' : __smtx_typeof (__eo_to_smt e) = SmtType.Real := by
      have htr : RuleProofs.eo_has_smt_translation e := by
        unfold CovEndpointOk at he; split at he
        · exact absurd rfl hm
        · exact absurd rfl hp
        · exact he
      rw [TranslationProofs.eo_to_smt_typeof_matches_translation e htr, heT]; rfl
    rcases cov_is_root_shape hroot with h | ⟨c, a, b, d, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, a, b, d, rfl, hT'⟩
  -- the count of sign variations
  have h0 : native_mk_rational 0 1 = (0 : Rat) := by native_decide
  have hV : ∀ v, v = MINF ∨ v = PINF ∨ (∃ a : Rat, v = Term.Rational a) ->
      ∃ n : Int, varsAt s v = Term.Numeral n := by
    rintro v (rfl | rfl | ⟨a, rfl⟩)
    · exact ⟨_, sturm_vars_minf hσ hSq hsc⟩
    · exact ⟨_, sturm_vars_pinf hσ hSq hsc⟩
    · exact ⟨_, sturm_vars_at hσ hSq hsc a⟩
  subst hpp
  set f := toPoly lst
  have hcnt : ∀ X Y nl nr : Int, varsAt s lo = Term.Numeral X -> varsAt s hi = Term.Numeral Y ->
      finCount l = Term.Numeral nl -> finCount r = Term.Numeral nr -> X - Y = nl + nr := by
    intro X Y nl nr h1 h2 h3 h4
    rw [h1, h2, h3, h4] at hcount
    simp [__eo_add, __eo_neg, __eo_is_eq, native_zplus, native_zneg, native_teq, native_and,
      native_not] at hcount
    linarith
  have hevalne : ∀ a : Rat, __eo_is_eq (__upoly_eval P (Term.Rational a)) (Term.Rational 0) =
      Term.Boolean false -> f.eval (a : ℝ) ≠ 0 := by
    intro a h h0'
    obtain ⟨x, hx, hx'⟩ := upoly_eval_cpoly hP a
    rw [hx] at h
    have : x ≠ 0 := by
      intro hx0; subst hx0; simp [__eo_is_eq, native_teq, native_and, native_not] at h
    exact this (by exact_mod_cast hx'.trans h0')
  have hmemA : ∀ (a v : ℝ), f.eval v = 0 -> a < v -> v ∈ SturmTarski.Theorem.rootsAbove f a := by
    intro a v h1 h2; simp [SturmTarski.Theorem.rootsAbove, Multiset.mem_toFinset,
      Polynomial.mem_roots hpp0, h1, h2]
  have hmemB : ∀ (b v : ℝ), f.eval v = 0 -> v < b -> v ∈ SturmTarski.Theorem.rootsBelow f b := by
    intro b v h1 h2; simp [SturmTarski.Theorem.rootsBelow, Multiset.mem_toFinset,
      Polynomial.mem_roots hpp0, h1, h2]
  have hmemI : ∀ (a b v : ℝ), f.eval v = 0 -> a < v -> v < b ->
      v ∈ SturmTarski.rootsInInterval f a b := by
    intro a b v h1 h2 h3; simp [SturmTarski.rootsInInterval, Multiset.mem_toFinset,
      Polynomial.mem_roots hpp0, h1, h2, h3]
  -- the endpoints
  have hfl : l ≠ Term.Stuck := hlS
  have key : ∀ (hlSh : l = MINF ∨ FinEnd l) (hrSh : r = PINF ∨ FinEnd r),
      (∀ v, InL M l v -> InR M r v -> f.eval v ≠ 0) ->
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv (__upoly_to_list P)) l) r) ∧
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv (__upoly_to_list P)) l) r) true := by
    intro hlSh hrSh hno
    obtain ⟨hB, htrue⟩ := sgn_inv_of_sign M hM hList l r hlSh hrSh
    refine ⟨hB, htrue ?_⟩
    obtain ⟨τ, hτ⟩ := const_sign_of_no_root f _ (interval_ordConnected M l r).isPreconnected
      (fun v hv => hno v hv.1 hv.2)
    exact ⟨τ, fun v h1 h2 => by rw [← eval_toPoly]; exact hτ v ⟨h1, h2⟩⟩
  rcases endL_cases hL with ⟨rfl, rfl⟩ | ⟨hlm, hlp, a, rfl, hlroot, hla0, hllt⟩ <;>
  rcases endR_cases hR with ⟨rfl, rfl⟩ | ⟨hrm, hrp, b, rfl, hrroot, hrb0, hrlt⟩
  · -- `(-∞, +∞)`: no roots at all
    refine key (Or.inl rfl) (Or.inl rfl) fun v _ _ hv => ?_
    obtain ⟨X, hX⟩ := hV _ (Or.inl rfl)
    obtain ⟨Y, hY⟩ := hV _ (Or.inr (Or.inl rfl))
    have hc := hcnt X Y 0 0 hX hY (finCount_inf _ (Or.inl rfl)) (finCount_inf _ (Or.inr rfl))
    rw [varsAt, sturm_vars_minf hσ hSq hsc] at hX; rw [varsAt, sturm_vars_pinf hσ hSq hsc] at hY
    injection hX with hX; injection hY with hY
    have hR := SturmTarski.Theorem.sturm_R f
    simp only [SturmTarski.signVariationsLineSturm, SturmTarski.signVariationsLine] at hR
    have hmem : v ∈ f.roots.toFinset := by
      simp [Multiset.mem_toFinset, Polynomial.mem_roots hpp0, hv]
    have : 0 < f.roots.toFinset.card := Finset.card_pos.mpr ⟨v, hmem⟩
    have hc' : (f.roots.toFinset.card : Int) = 0 := by linarith
    omega
  · -- `(-∞, r)`
    have hFr := hfin r hrT hlR.2 hrm hrp P sr hrroot
    have hwr := cov_is_root_sound M hM hP r sr hFr hrroot
    have hrb : covDen M r < b := by
      have := cov_lt_sound M hM hFr (Or.inl ⟨b, rfl⟩) hrlt; rwa [covDen_rational] at this
    have hb0 := hevalne b hrb0
    refine key (Or.inl rfl) (Or.inr hFr) fun v _ hIR hv => ?_
    rcases hIR with h | hvr; exact hrp h
    obtain ⟨X, hX⟩ := hV _ (Or.inl rfl)
    obtain ⟨Y, hY⟩ := hV _ (Or.inr (Or.inr ⟨b, rfl⟩))
    have hc := hcnt X Y 0 1 hX hY (finCount_inf _ (Or.inl rfl)) (finCount_fin _ hrS hrm hrp)
    rw [varsAt, sturm_vars_minf hσ hSq hsc] at hX; rw [varsAt, sturm_vars_at hσ hSq hsc b] at hY
    injection hX with hX; injection hY with hY
    have hB := SturmTarski.Theorem.sturm_below (b : ℝ) f hb0
    simp only [SturmTarski.signVariationsBelowSturm, SturmTarski.signVariationsBelowB] at hB
    have hsub : ({v, covDen M r} : Finset ℝ) ⊆ SturmTarski.Theorem.rootsBelow f b := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hmemB _ _ hv (lt_trans hvr hrb)
      · rw [Finset.mem_singleton.mp hz]; exact hmemB _ _ hwr hrb
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (ne_of_lt hvr)] at this
    have hc' : ((SturmTarski.Theorem.rootsBelow f b).card : Int) = 1 := by linarith
    omega
  · -- `(l, +∞)`
    have hFl := hfin l hlT hlR.1 hlm hlp P sl hlroot
    have hwl := cov_is_root_sound M hM hP l sl hFl hlroot
    have hal : (a : ℝ) < covDen M l := by
      have := cov_lt_sound M hM (Or.inl ⟨a, rfl⟩) hFl hllt; rwa [covDen_rational] at this
    have ha0 := hevalne a hla0
    refine key (Or.inr hFl) (Or.inl rfl) fun v hIL _ hv => ?_
    rcases hIL with h | hlv; exact hlm h
    obtain ⟨X, hX⟩ := hV _ (Or.inr (Or.inr ⟨a, rfl⟩))
    obtain ⟨Y, hY⟩ := hV _ (Or.inr (Or.inl rfl))
    have hc := hcnt X Y 1 0 hX hY (finCount_fin _ hlS hlm hlp) (finCount_inf _ (Or.inr rfl))
    rw [varsAt, sturm_vars_at hσ hSq hsc a] at hX; rw [varsAt, sturm_vars_pinf hσ hSq hsc] at hY
    injection hX with hX; injection hY with hY
    have hA := SturmTarski.Theorem.sturm_above (a : ℝ) f ha0
    simp only [SturmTarski.signVariationsAboveSturm, SturmTarski.signVariationsAboveA] at hA
    have hsub : ({covDen M l, v} : Finset ℝ) ⊆ SturmTarski.Theorem.rootsAbove f a := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hmemA _ _ hwl hal
      · rw [Finset.mem_singleton.mp hz]; exact hmemA _ _ hv (lt_trans hal hlv)
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (ne_of_lt hlv)] at this
    have hc' : ((SturmTarski.Theorem.rootsAbove f a).card : Int) = 1 := by linarith
    omega
  · -- `(l, r)`
    have hFl := hfin l hlT hlR.1 hlm hlp P sl hlroot
    have hwl := cov_is_root_sound M hM hP l sl hFl hlroot
    have hal : (a : ℝ) < covDen M l := by
      have := cov_lt_sound M hM (Or.inl ⟨a, rfl⟩) hFl hllt; rwa [covDen_rational] at this
    have ha0 := hevalne a hla0
    have hFr := hfin r hrT hlR.2 hrm hrp P sr hrroot
    have hwr := cov_is_root_sound M hM hP r sr hFr hrroot
    have hrb : covDen M r < b := by
      have := cov_lt_sound M hM hFr (Or.inl ⟨b, rfl⟩) hrlt; rwa [covDen_rational] at this
    have hb0 := hevalne b hrb0
    refine key (Or.inr hFl) (Or.inr hFr) fun v hIL hIR hv => ?_
    rcases hIL with h | hlv; exact hlm h
    rcases hIR with h | hvr; exact hrp h
    obtain ⟨X, hX⟩ := hV _ (Or.inr (Or.inr ⟨a, rfl⟩))
    obtain ⟨Y, hY⟩ := hV _ (Or.inr (Or.inr ⟨b, rfl⟩))
    have hc := hcnt X Y 1 1 hX hY (finCount_fin _ hlS hlm hlp) (finCount_fin _ hrS hrm hrp)
    rw [varsAt, sturm_vars_at hσ hSq hsc a] at hX; rw [varsAt, sturm_vars_at hσ hSq hsc b] at hY
    injection hX with hX; injection hY with hY
    have hab : (a : ℝ) < b := by linarith
    have hI := SturmTarski.Theorem.sturm_interval (a : ℝ) b f hab ha0 hb0
    simp only [SturmTarski.signVariationsSturmAb, SturmTarski.signVariationsAb] at hI
    have hsub : ({covDen M l, v, covDen M r} : Finset ℝ) ⊆ SturmTarski.rootsInInterval f a b := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hmemI _ _ _ hwl hal (by linarith)
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hmemI _ _ _ hv (by linarith) (by linarith)
      · rw [Finset.mem_singleton.mp hz]; exact hmemI _ _ _ hwr (by linarith) hrb
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp; constructor <;> intro h <;> linarith),
      Finset.card_pair (ne_of_lt hvr)] at this
    have hc' : ((SturmTarski.rootsInInterval f a b).card : Int) = 2 := by linarith
    omega

public theorem cmd_step_sgn_inv_intro_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sgn_inv_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sgn_inv_intro args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sgn_inv_intro args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sgn_inv_intro args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases args with _ | ⟨p, _ | ⟨l, _ | ⟨r, _ | ⟨lo, _ | ⟨hi, _ | ⟨sq, _ | ⟨sl, _ | ⟨sr, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  rcases premises with _ | ⟨_, _⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  have hT := hCmdTrans
  simp only [cmdTranslationOk, cArgListTranslationOkMask, argTranslationOkMasked] at hT
  have hTy : __eo_typeof (__eo_prog_sgn_inv_intro p l r lo hi sq sl sr) = Term.Bool := hResultTy
  have hSound := sgn_inv_intro_sound M hM p l r lo hi sq sl sr hT.2.1 hT.2.2.1 hTy
  exact ⟨fun _ => hSound.2, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hSound.1⟩
