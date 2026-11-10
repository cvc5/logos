module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormSupport
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.Translation.Coverings
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Ring.Real
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport
public import Cpc.Proofs.RuleSupport.CoveringsUPolySupport
import all Cpc.Proofs.RuleSupport.CoveringsUPolySupport

/-!
# Model semantics of the coverings calculus

The value a model gives an arithmetic term, read as a real number, and what the
translations of `@is_root`, `@sgn_inv` and `@ran` say about it.
-/

@[expose] public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CoveringsProofs

/-- The real number a model gives an arithmetic term, an integer read as a real. -/
noncomputable def covDen (M : SmtModel) (t : Term) : Real :=
  match arith_poly_norm_atom_denote_real M t with
  | SmtValue.Real r => r
  | _ => 0

/-- `t` translates to an SMT term of arithmetic sort. -/
def CovArith (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨ __smtx_typeof (__eo_to_smt t) = SmtType.Real

theorem covDen_spec (M : SmtModel) (hM : model_wf M) (t : Term) (ht : CovArith t) :
    arith_poly_norm_atom_denote_real M t = SmtValue.Real (covDen M t) := by
  rcases arith_poly_norm_atom_denote_real_rational_of_smt_arith_type M hM t ht with ⟨q, hq⟩
  simp [covDen, hq]

/-- A term of SMT sort `Real` evaluates to the real `covDen` gives it. -/
theorem eval_of_real (M : SmtModel) (hM : model_wf M) (t : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Real (covDen M t) := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Real := by
    simpa [ht] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simp [term_has_non_none_type, ht])
  rcases real_value_canonical hEvalTy with ⟨q, hq⟩
  have := covDen_spec M hM t (Or.inr ht)
  simp [arith_poly_norm_atom_denote_real, hq, __smtx_to_real_coerce] at this
  rw [hq, this]

private theorem covArith_of_typed {t : Term} {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = T) (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    CovArith t := by
  subst h; exact hT

private theorem nn_of_covArith {t : Term} {s : SmtTerm} (h : __eo_to_smt t = s)
    (hH : CovArith t) : term_has_non_none_type s := by
  unfold term_has_non_none_type
  rw [← h]
  rcases hH with h | h <;> rw [h] <;> simp

theorem covDen_ofTermVal (M : SmtModel) (hM : model_wf M) : OfTermVal CovArith (covDen M) where
  rational q := by
    simp [covDen, arith_poly_norm_atom_denote_real_of_rational]
  numeral n := by
    simp [covDen, arith_poly_norm_atom_denote_real_of_numeral, native_int_to_real]
  uneg a hH := by
    have hNN : term_has_non_none_type (SmtTerm.uneg (__eo_to_smt a)) := nn_of_covArith rfl hH
    have ha := arith_unop_arg_of_non_none (typeof_uneg_eq (__eo_to_smt a)) hNN
    refine ⟨ha, ?_⟩
    have h1 := arith_poly_norm_atom_denote_real_of_uneg M a
    rw [covDen_spec M hM _ hH, covDen_spec M hM a ha] at h1
    simp [__smtx_model_eval_uneg, native_rneg] at h1
    exact h1
  plus a b hH := by
    have hNN : term_has_non_none_type (SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)) := nn_of_covArith rfl hH
    have hab := arith_binop_args_of_non_none (typeof_plus_eq _ _) hNN
    have ha : CovArith a := by rcases hab with h | h; exact Or.inl h.1; exact Or.inr h.1
    have hb : CovArith b := by rcases hab with h | h; exact Or.inl h.2; exact Or.inr h.2
    refine ⟨ha, hb, ?_⟩
    have h1 := arith_poly_norm_atom_denote_real_of_plus M hM a b hH
    rw [covDen_spec M hM _ hH, covDen_spec M hM a ha, covDen_spec M hM b hb] at h1
    simp [__smtx_model_eval_plus, native_rplus] at h1
    exact h1
  neg a b hH := by
    have hNN : term_has_non_none_type (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) := nn_of_covArith rfl hH
    have hab := arith_binop_args_of_non_none (typeof_neg_eq _ _) hNN
    have ha : CovArith a := by rcases hab with h | h; exact Or.inl h.1; exact Or.inr h.1
    have hb : CovArith b := by rcases hab with h | h; exact Or.inl h.2; exact Or.inr h.2
    refine ⟨ha, hb, ?_⟩
    have h1 := arith_poly_norm_atom_denote_real_of_neg M hM a b hH
    rw [covDen_spec M hM _ hH, covDen_spec M hM a ha, covDen_spec M hM b hb] at h1
    simp [__smtx_model_eval_plus, __smtx_model_eval_uneg, native_rplus, native_rneg] at h1
    rw [h1]; ring
  mult a b hH := by
    have hNN : term_has_non_none_type (SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)) := nn_of_covArith rfl hH
    have hab := arith_binop_args_of_non_none (typeof_mult_eq _ _) hNN
    have ha : CovArith a := by rcases hab with h | h; exact Or.inl h.1; exact Or.inr h.1
    have hb : CovArith b := by rcases hab with h | h; exact Or.inl h.2; exact Or.inr h.2
    refine ⟨ha, hb, ?_⟩
    have h1 := arith_poly_norm_atom_denote_real_of_mult M hM a b hH
    rw [covDen_spec M hM _ hH, covDen_spec M hM a ha, covDen_spec M hM b hb] at h1
    simp [__smtx_model_eval_mult, native_rmult] at h1
    exact h1
  to_real a hH := by
    have hInt : __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
      have h : __smtx_typeof (SmtTerm.to_real (__eo_to_smt a)) ≠ SmtType.None :=
        nn_of_covArith rfl hH
      rw [typeof_to_real_eq] at h
      by_contra hne
      simp [native_ite, native_Teq, hne] at h
    refine ⟨Or.inl hInt, ?_⟩
    have h1 := arith_poly_norm_atom_denote_real_of_to_real M hM a hInt
    simp [covDen, h1]

/-- An arithmetic term evaluates to the integer or real `covDen` reads it as. -/
theorem eval_cases (M : SmtModel) (hM : model_wf M) (t : Term) (ht : CovArith t) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      ∃ n : Int, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral n ∧ covDen M t = n) ∨
    (__smtx_typeof (__eo_to_smt t) = SmtType.Real ∧
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Real (covDen M t)) := by
  rcases ht with h | h
  · rcases smt_eval_int_of_type M hM t h with ⟨n, hn⟩
    refine Or.inl ⟨h, n, hn, ?_⟩
    simp [covDen, arith_poly_norm_atom_denote_real, hn, __smtx_to_real_coerce,
      native_int_to_real]
  · exact Or.inr ⟨h, eval_of_real M hM t h⟩

/-- The order relations the coverings literals compare a polynomial with. -/
inductive CovRel : Type where
  | lt | leq | eq | geq | gt

def CovRel.op : CovRel -> Term
  | CovRel.lt => Term.UOp UserOp.lt
  | CovRel.leq => Term.UOp UserOp.leq
  | CovRel.eq => Term.UOp UserOp.eq
  | CovRel.geq => Term.UOp UserOp.geq
  | CovRel.gt => Term.UOp UserOp.gt

/-- What the relation says of `x` against `y`. -/
def CovRel.holds : CovRel -> Real -> Real -> Prop
  | CovRel.lt, x, y => x < y
  | CovRel.leq, x, y => x ≤ y
  | CovRel.eq, x, y => x = y
  | CovRel.geq, x, y => x ≥ y
  | CovRel.gt, x, y => x > y

noncomputable instance (r : CovRel) (x y : Real) : Decidable (r.holds x y) := by
  cases r <;> simp only [CovRel.holds] <;> infer_instance

def CovRel.atom (r : CovRel) (a b : Term) : Term := Term.Apply (Term.Apply r.op a) b

/-- Both sides of a typed comparison against an arithmetic term are arithmetic, of one sort. -/
theorem covRel_args (r : CovRel) (a b : Term)
    (hz : CovArith b) (hb : RuleProofs.eo_has_bool_type (r.atom a b)) :
    (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real) := by
  cases r
  · exact rel_operands_arith_type_of_lt_has_bool_type a b hb
  · exact rel_operands_arith_type_of_leq_has_bool_type a b hb
  · have h := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hb
    rcases hz with hz | hz
    · exact Or.inl ⟨h.1.trans hz, hz⟩
    · exact Or.inr ⟨h.1.trans hz, hz⟩
  · exact rel_operands_arith_type_of_geq_has_bool_type a b hb
  · exact rel_operands_arith_type_of_gt_has_bool_type a b hb

/-- A typed comparison evaluates to the comparison of the values of its sides. -/
theorem covRel_eval (M : SmtModel) (hM : model_wf M) (r : CovRel) (a b : Term)
    (hz : CovArith b) (hb : RuleProofs.eo_has_bool_type (r.atom a b)) :
    CovArith a ∧
    __smtx_model_eval M (__eo_to_smt (r.atom a b)) =
      SmtValue.Boolean (decide (r.holds (covDen M a) (covDen M b))) := by
  have hab := covRel_args r a b hz hb
  have ha : CovArith a := by rcases hab with h | h; exact Or.inl h.1; exact Or.inr h.1
  refine ⟨ha, ?_⟩
  rcases eval_cases M hM a ha with ⟨hta, n, hn, hdn⟩ | ⟨hta, hra⟩ <;>
  rcases eval_cases M hM b hz with ⟨htb, m, hm, hdm⟩ | ⟨htb, hrb⟩
  · cases r <;>
      simp [CovRel.atom, CovRel.op, CovRel.holds, __eo_to_smt, __smtx_model_eval, hn, hm,
        hdn, hdm, __smtx_model_eval_lt, __smtx_model_eval_leq, __smtx_model_eval_gt,
        __smtx_model_eval_geq, __smtx_model_eval_eq, native_zlt, native_zleq, native_veq]
  · rcases hab with h | h <;> simp_all
  · rcases hab with h | h <;> simp_all
  · cases r <;>
      simp [CovRel.atom, CovRel.op, CovRel.holds, __eo_to_smt, __smtx_model_eval, hra, hrb,
        __smtx_model_eval_lt, __smtx_model_eval_leq, __smtx_model_eval_gt,
        __smtx_model_eval_geq, __smtx_model_eval_eq, native_rlt, native_rleq, native_veq]

/-- A coverings literal: the comparison `r` of `p` with zero, negated when `neg`. -/
def covLit (neg : Bool) (r : CovRel) (p z : Term) : Term :=
  if neg then Term.Apply (Term.UOp UserOp.not) (r.atom p z) else r.atom p z

/-- What a coverings literal says of the value `v` of its polynomial. -/
def litSem (neg : Bool) (r : CovRel) (v : Real) : Prop :=
  if neg then ¬ r.holds v 0 else r.holds v 0

theorem eo_requires_eq_body {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    x = y ∧ __eo_requires x y z = z := by
  have hxy := eo_requires_arg_eq_of_ne_stuck h
  refine ⟨hxy, ?_⟩
  subst hxy
  by_cases hx : x = Term.Stuck
  · subst hx; simp [__eo_requires, native_ite, native_teq, native_not] at h
  · simp [__eo_requires, native_ite, native_teq, native_not, hx]

theorem eo_requires_left_ne_stuck {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  rintro rfl
  simp [__eo_requires, native_ite, native_teq, native_not] at h

private theorem cov_atom_poly_shape (A : Term) (h : __cov_atom_poly A ≠ Term.Stuck) :
    ∃ r : CovRel, ∃ p z, A = r.atom p z ∧ __eo_to_q z = Term.Rational 0 ∧ __cov_atom_poly A = p := by
  have hz : native_mk_rational 0 1 = (0 : Rat) := by native_decide
  unfold __cov_atom_poly at h ⊢
  split at h
  · obtain ⟨h1, h2⟩ := eo_requires_eq_body h
    exact ⟨CovRel.lt, _, _, rfl, by rw [h1, hz], h2⟩
  · obtain ⟨h1, h2⟩ := eo_requires_eq_body h
    exact ⟨CovRel.leq, _, _, rfl, by rw [h1, hz], h2⟩
  · obtain ⟨h1, h2⟩ := eo_requires_eq_body h
    exact ⟨CovRel.eq, _, _, rfl, by rw [h1, hz], h2⟩
  · obtain ⟨h1, h2⟩ := eo_requires_eq_body h
    exact ⟨CovRel.geq, _, _, rfl, by rw [h1, hz], h2⟩
  · obtain ⟨h1, h2⟩ := eo_requires_eq_body h
    exact ⟨CovRel.gt, _, _, rfl, by rw [h1, hz], h2⟩
  · exact absurd rfl h

noncomputable instance (neg : Bool) (r : CovRel) (v : Real) : Decidable (litSem neg r v) := by
  unfold litSem; split <;> infer_instance

theorem cov_lit_poly_shape (F : Term) (h : __cov_lit_poly F ≠ Term.Stuck) :
    ∃ neg r p z, F = covLit neg r p z ∧ __eo_to_q z = Term.Rational 0 ∧ __cov_lit_poly F = p := by
  by_cases hn : ∃ A, F = Term.Apply (Term.UOp UserOp.not) A
  · rcases hn with ⟨A, rfl⟩
    have hEq : __cov_lit_poly (Term.Apply (Term.UOp UserOp.not) A) = __cov_atom_poly A := by
      simp [__cov_lit_poly]
    rw [hEq] at h ⊢
    rcases cov_atom_poly_shape A h with ⟨r, p, z, rfl, hq, hp⟩
    exact ⟨true, r, p, z, rfl, hq, hp⟩
  · have hF : F ≠ Term.Stuck := by rintro rfl; simp [__cov_lit_poly] at h
    have hEq : __cov_lit_poly F = __cov_atom_poly F := by
      unfold __cov_lit_poly
      split
      · exact absurd rfl hF
      · exact absurd ⟨_, rfl⟩ hn
      · rfl
    rw [hEq] at h ⊢
    rcases cov_atom_poly_shape F h with ⟨r, p, z, rfl, hq, hp⟩
    exact ⟨false, r, p, z, rfl, hq, hp⟩

/-- `$cov_lit_holds` computes `litSem` at a rational. -/
theorem cov_lit_holds_rat (neg : Bool) (r : CovRel) (p z : Term) (q : Rat) :
    __cov_lit_holds (covLit neg r p z) (Term.Rational q) =
      Term.Boolean (decide (litSem neg r (q : Real))) := by
  have hz : native_mk_rational 0 1 = (0 : Rat) := by native_decide
  cases neg <;> cases r <;>
    simp [covLit, litSem, CovRel.atom, CovRel.op, CovRel.holds, __cov_lit_holds,
      __cov_atom_holds, __eo_is_neg, __eo_gt, __eo_not, __eo_and, native_qlt, native_not,
      native_and, hz] <;>
    rcases lt_trichotomy q 0 with h | rfl | h <;> grind

/-- A term that `eo::to_q` reads as zero is a zero literal. -/
theorem zero_of_to_q {z : Term} (hz : __eo_to_q z = Term.Rational 0) (M : SmtModel) :
    CovArith z ∧ covDen M z = 0 := by
  cases z with
  | Numeral n =>
      have hn : n = 0 := by
        simp [__eo_to_q, native_to_real, native_mk_rational] at hz
        exact_mod_cast hz
      subst hn
      refine ⟨Or.inl (by rw [__eo_to_smt.eq_def]; simp [__smtx_typeof]), ?_⟩
      simp [covDen, arith_poly_norm_atom_denote_real_of_numeral, native_int_to_real]
  | Rational q =>
      have hq : q = 0 := by simpa [__eo_to_q] using hz
      subst hq
      refine ⟨Or.inr (by rw [__eo_to_smt.eq_def]; simp [__smtx_typeof]), ?_⟩
      simp [covDen, arith_poly_norm_atom_denote_real_of_rational]
  | _ => simp [__eo_to_q] at hz

/-- A true coverings literal says `litSem` of the value of its polynomial. -/
theorem covLit_true (M : SmtModel) (hM : model_wf M) (neg : Bool) (r : CovRel) (p z : Term)
    (hz : __eo_to_q z = Term.Rational 0) (hT : eo_interprets M (covLit neg r p z) true) :
    CovArith p ∧ litSem neg r (covDen M p) := by
  obtain ⟨hzA, hz0⟩ := zero_of_to_q hz M
  cases neg with
  | false =>
      have hb := RuleProofs.eo_has_bool_type_of_interprets_true M _ hT
      obtain ⟨hp, hE⟩ := covRel_eval M hM r p z hzA hb
      refine ⟨hp, ?_⟩
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hT
      cases hT with
      | intro_true _ hE' =>
          simp only [covLit, Bool.false_eq_true, ↓reduceIte] at hE'
          rw [hE, hz0] at hE'
          simpa [litSem] using hE'
  | true =>
      have hF := RuleProofs.eo_interprets_not_true_implies_false M _ hT
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hF
      cases hF with
      | intro_false hTy hE' =>
          obtain ⟨hp, hE⟩ := covRel_eval M hM r p z hzA hTy
          refine ⟨hp, ?_⟩
          rw [hE, hz0] at hE'
          simpa [litSem] using hE'

/-- The value of the polynomial with the coefficients `q` at the SMT term `v`. -/
theorem coeffs_at_eval (M : SmtModel) {q : Term} {l : List Rat} (hq : RatList q l)
    (v : SmtTerm) (hv : __smtx_typeof v = SmtType.Real) (x : Real)
    (hx : __smtx_model_eval M v = SmtValue.Real x) :
    __smtx_typeof (__eo_to_smt_coeffs_at q v) = SmtType.Real ∧
    __smtx_model_eval M (__eo_to_smt_coeffs_at q v) = SmtValue.Real (lev l x) := by
  induction hq with
  | nil =>
      refine ⟨by simp [__eo_to_smt_coeffs_at, __smtx_typeof], ?_⟩
      simp [__eo_to_smt_coeffs_at, __smtx_model_eval, native_rat_to_real, native_mk_rational]
  | cons a q l hq ih =>
      obtain ⟨ihT, ihE⟩ := ih
      have hEq : __eo_to_smt_coeffs_at
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Rational a)) q) v =
          SmtTerm.plus (SmtTerm.Rational a) (SmtTerm.mult v (__eo_to_smt_coeffs_at q v)) := by
        rw [__eo_to_smt_coeffs_at]
      rw [hEq]
      refine ⟨?_, ?_⟩
      · rw [typeof_plus_eq, typeof_mult_eq, hv, ihT]
        simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2]
      · simp [__smtx_model_eval, hx, ihE, __smtx_model_eval_plus, __smtx_model_eval_mult,
          native_rplus, native_rmult, native_rat_to_real]

/-- A true `@is_root q r` says that `r` is a real root of the polynomial `q` lists. -/
theorem is_root_true (M : SmtModel) (hM : model_wf M) {q : Term} {l : List Rat}
    (hq : RatList q l) (r : Term)
    (hT : eo_interprets M (Term.Apply (Term.UOp1 UserOp1._at_is_root q) r) true) :
    __smtx_typeof (__eo_to_smt r) = SmtType.Real ∧ lev l (covDen M r) = 0 := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hT
  have hEq : __eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_is_root q) r) =
      native_ite (native_Teq (__smtx_typeof (__eo_to_smt r)) SmtType.Real)
        (SmtTerm.eq (__eo_to_smt_coeffs_at q (__eo_to_smt r))
          (SmtTerm.Rational (native_mk_rational 0 1))) SmtTerm.None := by
    rw [__eo_to_smt.eq_def]
  rw [hEq] at hT
  by_cases hr : __smtx_typeof (__eo_to_smt r) = SmtType.Real
  · refine ⟨hr, ?_⟩
    simp only [native_ite, native_Teq, hr, decide_true, ↓reduceIte] at hT
    obtain ⟨_, hE⟩ := coeffs_at_eval M hq _ hr _ (eval_of_real M hM r hr)
    cases hT with
    | intro_true _ hE' =>
        simp [__smtx_model_eval, hE, __smtx_model_eval_eq, native_veq, native_rat_to_real,
          native_mk_rational] at hE'
        exact hE'
  · simp only [native_ite, native_Teq, hr, decide_false] at hT
    cases hT with
    | intro_true hTy _ => simp at hTy

/-- A typed `@is_root q r` has a real `r`. -/
theorem is_root_typed (q r : Term)
    (hB : RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp1 UserOp1._at_is_root q) r)) :
    __smtx_typeof (__eo_to_smt r) = SmtType.Real := by
  unfold RuleProofs.eo_has_bool_type at hB
  have hEq : __eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_is_root q) r) =
      native_ite (native_Teq (__smtx_typeof (__eo_to_smt r)) SmtType.Real)
        (SmtTerm.eq (__eo_to_smt_coeffs_at q (__eo_to_smt r))
          (SmtTerm.Rational (native_mk_rational 0 1))) SmtTerm.None := by
    rw [__eo_to_smt.eq_def]
  rw [hEq] at hB
  by_contra hr
  simp [native_ite, native_Teq, hr] at hB

/-! ### The bound variable `@x` -/

/-- The variable the coverings translations bind. -/
abbrev covX : SmtTerm := SmtTerm.Var (native_string_lit "@x") SmtType.Real

/-- The model `M` with `@x` bound to `v`. -/
noncomputable abbrev pushX (M : SmtModel) (v : Real) : SmtModel :=
  native_model_push M (native_string_lit "@x") SmtType.Real (SmtValue.Real v)

theorem push_push_same (M : SmtModel) (s : native_String) (T : SmtType) (v w : SmtValue) :
    native_model_push (native_model_push M s T v) s T w = native_model_push M s T w := by
  cases M
  simp only [native_model_push, SmtModel.mk.injEq, and_true]
  funext k
  split <;> rfl

@[simp] theorem push_usortDom (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
    (native_model_push M s T v).usortDom = M.usortDom := rfl

theorem eval_covX_push (M : SmtModel) (v : Real) :
    __smtx_model_eval (pushX M v) covX = SmtValue.Real v := by
  simp [__smtx_model_eval, native_model_var_lookup, native_model_push]

/-- A choice over `@x` reads no outer binding of `@x`. -/
theorem eval_choice_push (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue)
    (b : SmtTerm) :
    __smtx_model_eval (native_model_push M s T v) (SmtTerm.choice s T b) =
      __smtx_model_eval M (SmtTerm.choice s T b) := by
  have hfun : native_model_push (native_model_push M s T v) s T = native_model_push M s T :=
    funext fun w => push_push_same M s T v w
  simp only [__smtx_model_eval, push_usortDom]
  rw [hfun]
  rfl

/-- What `$eo_to_smt_cov_throughout I F` says when it holds. -/
theorem throughout_true (M : SmtModel) (I F : SmtTerm) (PI PF : Real -> Prop)
    (hI : ∀ v, ∃ b, __smtx_model_eval (pushX M v) I = SmtValue.Boolean b ∧ (b = true ↔ PI v))
    (hF : ∀ v, ∃ b, __smtx_model_eval (pushX M v) F = SmtValue.Boolean b ∧ (b = true ↔ PF v))
    (h : __smtx_model_eval M (__eo_to_smt_cov_throughout I F) = SmtValue.Boolean true) :
    ∀ v, PI v -> PF v := by
  intro v hv
  by_contra hnot
  have hP : ∃ w : SmtValue,
      __smtx_typeof_value w = SmtType.Real ∧
        __smtx_value_canonical M.usortDom w = true ∧
          __smtx_model_eval (native_model_push M (native_string_lit "@x") SmtType.Real w)
            (SmtTerm.and I (SmtTerm.not F)) = SmtValue.Boolean true := by
    refine ⟨SmtValue.Real v, rfl, rfl, ?_⟩
    obtain ⟨b1, hb1, hb1'⟩ := hI v
    obtain ⟨b2, hb2, hb2'⟩ := hF v
    rw [__smtx_model_eval, __smtx_model_eval]
    rw [show native_model_push M (native_string_lit "@x") SmtType.Real (SmtValue.Real v) =
      pushX M v from rfl, hb1, hb2]
    cases b1 <;> cases b2 <;> simp_all [__smtx_model_eval_not, __smtx_model_eval_and,
      native_and, native_not]
  have hEx : __smtx_model_eval M
      (SmtTerm.exists (native_string_lit "@x") SmtType.Real (SmtTerm.and I (SmtTerm.not F))) =
        SmtValue.Boolean true := by
    rw [__smtx_model_eval]
    simp [hP]
  unfold __eo_to_smt_cov_throughout at h
  rw [__smtx_model_eval, hEx] at h
  simp [__smtx_model_eval_not, native_not] at h

/-! ### Endpoints -/

/-- `v` is above the lower endpoint `l`. -/
def InL (M : SmtModel) (l : Term) (v : Real) : Prop :=
  l = Term.UOp UserOp._at__at_cov_minus_inf ∨ covDen M l < v

/-- `v` is below the upper endpoint `r`. -/
def InR (M : SmtModel) (r : Term) (v : Real) : Prop :=
  r = Term.UOp UserOp._at__at_cov_plus_inf ∨ v < covDen M r

/-- A finite endpoint whose translation is closed: a rational, or a `@ran` choice. -/
theorem endpoint_eval_push (M : SmtModel) (hM : model_wf M) (e : Term)
    (hNotInf : e ≠ Term.UOp UserOp._at__at_cov_minus_inf ∧ e ≠ Term.UOp UserOp._at__at_cov_plus_inf)
    (hTy : __smtx_typeof (__eo_to_smt e) = SmtType.Real)
    (hShape : (∃ q, e = Term.Rational q) ∨ (∃ c a b d, e = Term.UOp4 UserOp4._at_ran c a b d))
    (v : Real) :
    __smtx_model_eval (pushX M v) (__eo_to_smt e) = SmtValue.Real (covDen M e) := by
  rw [← eval_of_real M hM e hTy]
  rcases hShape with ⟨q, rfl⟩ | ⟨c, a, b, d, rfl⟩
  · rfl
  · rcases TranslationProofs.eo_to_smt_ran_head_cases c a b d with h | ⟨F, h⟩
    · rw [h] at hTy; simp at hTy
    · rw [h]; exact eval_choice_push M _ _ _ F

private theorem real_of_cmp_x {op : SmtTerm -> SmtTerm -> SmtTerm} {y : SmtTerm}
    (hop : ∀ a b, __smtx_typeof (op a b) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof a) (__smtx_typeof b) SmtType.Bool)
    (h : __smtx_typeof (op covX y) ≠ SmtType.None ∨ __smtx_typeof (op y covX) ≠ SmtType.None) :
    __smtx_typeof y = SmtType.Real := by
  have hx : __smtx_typeof covX = SmtType.Real := by
    rw [__smtx_typeof.eq_def] <;> simp [__smtx_typeof_guard_wf, __smtx_type_wf, native_ite,
      __smtx_type_wf_component, __smtx_type_wf_rec, native_and]
  rcases h with h | h
  · rcases arith_binop_ret_bool_args_of_non_none (hop covX y) h with h' | h'
    · rw [hx] at h'; cases h'.1
    · exact h'.2
  · rcases arith_binop_ret_bool_args_of_non_none (hop y covX) h with h' | h'
    · rw [hx] at h'; cases h'.2
    · exact h'.1

/-- The lower-endpoint guard of `@sgn_inv`, under `@x ↦ v`. -/
theorem cov_above_eval (M : SmtModel) (hM : model_wf M) (l : Term)
    (hTy : __smtx_typeof (__eo_to_smt_cov_above l (__eo_to_smt l)) ≠ SmtType.None) (v : Real) :
    ∃ b, __smtx_model_eval (pushX M v) (__eo_to_smt_cov_above l (__eo_to_smt l)) =
      SmtValue.Boolean b ∧ (b = true ↔ InL M l v) := by
  unfold __eo_to_smt_cov_above at hTy ⊢
  split at hTy
  · exact ⟨true, by simp [__smtx_model_eval], by simp [InL]⟩
  · rename_i q
    refine ⟨decide ((q : Real) < v), ?_, ?_⟩
    · simp [__smtx_model_eval, __smtx_model_eval_gt, __smtx_model_eval_lt,
        native_rlt]
      rfl
    · simp [InL, covDen, arith_poly_norm_atom_denote_real_of_rational]
  · rename_i c a b d
    have hR := real_of_cmp_x (op := SmtTerm.gt) typeof_gt_eq (Or.inl hTy)
    have hE := endpoint_eval_push M hM _ ⟨by simp, by simp⟩ hR (Or.inr ⟨c, a, b, d, rfl⟩) v
    refine ⟨decide (covDen M (Term.UOp4 UserOp4._at_ran c a b d) < v), ?_, ?_⟩
    · rw [show __smtx_model_eval (pushX M v) (SmtTerm.gt covX
          (__eo_to_smt (Term.UOp4 UserOp4._at_ran c a b d))) =
          __smtx_model_eval_gt (__smtx_model_eval (pushX M v) covX)
            (__smtx_model_eval (pushX M v) (__eo_to_smt (Term.UOp4 UserOp4._at_ran c a b d)))
          by rw [__smtx_model_eval]]
      rw [hE, eval_covX_push]
      simp [__smtx_model_eval_gt, __smtx_model_eval_lt, native_rlt]
    · simp [InL]
  · exact absurd (by simp) hTy

/-- The upper-endpoint guard of `@sgn_inv`, under `@x ↦ v`. -/
theorem cov_below_eval (M : SmtModel) (hM : model_wf M) (r : Term)
    (hTy : __smtx_typeof (__eo_to_smt_cov_below r (__eo_to_smt r)) ≠ SmtType.None) (v : Real) :
    ∃ b, __smtx_model_eval (pushX M v) (__eo_to_smt_cov_below r (__eo_to_smt r)) =
      SmtValue.Boolean b ∧ (b = true ↔ InR M r v) := by
  unfold __eo_to_smt_cov_below at hTy ⊢
  split at hTy
  · exact ⟨true, by simp [__smtx_model_eval], by simp [InR]⟩
  · rename_i q
    refine ⟨decide (v < (q : Real)), ?_, ?_⟩
    · simp [__smtx_model_eval, __smtx_model_eval_lt,
        native_rlt]
      rfl
    · simp [InR, covDen, arith_poly_norm_atom_denote_real_of_rational]
  · rename_i c a b d
    have hR := real_of_cmp_x (op := SmtTerm.lt) typeof_lt_eq (Or.inl hTy)
    have hE := endpoint_eval_push M hM _ ⟨by simp, by simp⟩ hR (Or.inr ⟨c, a, b, d, rfl⟩) v
    refine ⟨decide (v < covDen M (Term.UOp4 UserOp4._at_ran c a b d)), ?_, ?_⟩
    · rw [show __smtx_model_eval (pushX M v) (SmtTerm.lt covX
          (__eo_to_smt (Term.UOp4 UserOp4._at_ran c a b d))) =
          __smtx_model_eval_lt (__smtx_model_eval (pushX M v) covX)
            (__smtx_model_eval (pushX M v) (__eo_to_smt (Term.UOp4 UserOp4._at_ran c a b d)))
          by rw [__smtx_model_eval]]
      rw [hE, eval_covX_push]
      simp [__smtx_model_eval_lt, native_rlt]
    · simp [InR]
  · exact absurd (by simp) hTy

theorem typeof_covX : __smtx_typeof covX = SmtType.Real := by
  rw [__smtx_typeof.eq_def] <;> simp [__smtx_typeof_guard_wf, __smtx_type_wf, native_ite,
    __smtx_type_wf_component, __smtx_type_wf_rec, native_and]

private theorem eval_or_true {a b : SmtValue} (h : __smtx_model_eval_or a b = SmtValue.Boolean true) :
    a = SmtValue.Boolean true ∨ b = SmtValue.Boolean true := by
  cases a <;> cases b <;> simp_all [__smtx_model_eval_or, native_or]

/-- A true `@sgn_inv q l r`: the polynomial `q` has one sign throughout `(l, r)`. -/
theorem sgn_inv_true (M : SmtModel) (hM : model_wf M) {q : Term} {lst : List Rat}
    (hq : RatList q lst) (l r : Term)
    (hT : eo_interprets M (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv q) l) r) true) :
    (∀ v, InL M l v -> InR M r v -> 0 < lev lst v) ∨
    (∀ v, InL M l v -> InR M r v -> lev lst v < 0) ∨
    (∀ v, InL M l v -> InR M r v -> lev lst v = 0) := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hT
  have hEq : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv q) l) r) =
      SmtTerm.or
        (__eo_to_smt_cov_throughout
          (SmtTerm.and (__eo_to_smt_cov_above l (__eo_to_smt l))
            (__eo_to_smt_cov_below r (__eo_to_smt r)))
          (SmtTerm.gt (__eo_to_smt_coeffs_at q covX) (SmtTerm.Rational (native_mk_rational 0 1))))
        (SmtTerm.or
          (__eo_to_smt_cov_throughout
            (SmtTerm.and (__eo_to_smt_cov_above l (__eo_to_smt l))
              (__eo_to_smt_cov_below r (__eo_to_smt r)))
            (SmtTerm.lt (__eo_to_smt_coeffs_at q covX) (SmtTerm.Rational (native_mk_rational 0 1))))
          (__eo_to_smt_cov_throughout
            (SmtTerm.and (__eo_to_smt_cov_above l (__eo_to_smt l))
              (__eo_to_smt_cov_below r (__eo_to_smt r)))
            (SmtTerm.eq (__eo_to_smt_coeffs_at q covX) (SmtTerm.Rational (native_mk_rational 0 1))))) := by
    rw [__eo_to_smt.eq_def]
  rw [hEq] at hT
  cases hT with
  | intro_true hTy hE =>
  -- typing of the guards
  have hOr := TranslationProofs.typeof_or_parts (TranslationProofs.non_none_of_bool hTy)
  have hThr := TranslationProofs.typeof_not_part (TranslationProofs.non_none_of_bool hOr.1)
  have hBody := TranslationProofs.typeof_exists_part (TranslationProofs.non_none_of_bool hThr)
  have hAnd := TranslationProofs.typeof_and_parts (TranslationProofs.non_none_of_bool hBody)
  have hI := TranslationProofs.typeof_and_parts (TranslationProofs.non_none_of_bool hAnd.1)
  have hL := cov_above_eval M hM l (TranslationProofs.non_none_of_bool hI.1)
  have hR := cov_below_eval M hM r (TranslationProofs.non_none_of_bool hI.2)
  have hIev : ∀ v, ∃ b, __smtx_model_eval (pushX M v)
      (SmtTerm.and (__eo_to_smt_cov_above l (__eo_to_smt l))
        (__eo_to_smt_cov_below r (__eo_to_smt r))) = SmtValue.Boolean b ∧
      (b = true ↔ (InL M l v ∧ InR M r v)) := by
    intro v
    obtain ⟨b1, h1, h1'⟩ := hL v
    obtain ⟨b2, h2, h2'⟩ := hR v
    refine ⟨b1 && b2, ?_, ?_⟩
    · rw [__smtx_model_eval, h1, h2]; simp [__smtx_model_eval_and, native_and]
    · simp [← h1', ← h2']
  have hP : ∀ v, __smtx_model_eval (pushX M v) (__eo_to_smt_coeffs_at q covX) =
      SmtValue.Real (lev lst v) := fun v =>
    (coeffs_at_eval (pushX M v) hq covX typeof_covX v (eval_covX_push M v)).2
  have h0 : ∀ v, __smtx_model_eval (pushX M v) (SmtTerm.Rational (native_mk_rational 0 1)) =
      SmtValue.Real 0 := by
    intro v; simp [__smtx_model_eval, native_rat_to_real, native_mk_rational_zero']
  rw [__smtx_model_eval] at hE
  rcases eval_or_true hE with hE | hE
  · left
    intro v hv1 hv2
    refine throughout_true M _ _ (fun v => InL M l v ∧ InR M r v) (fun v => 0 < lev lst v)
      hIev (fun v => ⟨decide (0 < lev lst v), ?_, by simp⟩) hE v ⟨hv1, hv2⟩
    rw [__smtx_model_eval, hP, h0]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, native_rlt]
  rw [__smtx_model_eval] at hE
  rcases eval_or_true hE with hE | hE
  · right; left
    intro v hv1 hv2
    refine throughout_true M _ _ (fun v => InL M l v ∧ InR M r v) (fun v => lev lst v < 0)
      hIev (fun v => ⟨decide (lev lst v < 0), ?_, by simp⟩) hE v ⟨hv1, hv2⟩
    rw [__smtx_model_eval, hP, h0]
    simp [__smtx_model_eval_lt, native_rlt]
  · right; right
    intro v hv1 hv2
    refine throughout_true M _ _ (fun v => InL M l v ∧ InR M r v) (fun v => lev lst v = 0)
      hIev (fun v => ⟨decide (lev lst v = 0), ?_, by simp⟩) hE v ⟨hv1, hv2⟩
    rw [__smtx_model_eval, hP, h0]
    simp [__smtx_model_eval_eq, native_veq]

/-! ### Real algebraic numbers -/

/-- `$valid_ran q lo hi s`, as `$cov_lt` and `$cov_is_root` inline it. -/
def validRan (q lo hi s : Term) : Term :=
  __eo_ite (__eo_and (__eo_is_q lo) (__eo_is_q hi))
    (__eo_ite (__upoly_rem_seq_check (__upoly_of_list q) (__upoly_derivative (__upoly_of_list q)) s)
      (__eo_and
        (__eo_is_neg (__eo_mul (__upoly_eval (__upoly_of_list q) lo)
          (__upoly_eval (__upoly_of_list q) hi)))
        (__eo_is_eq
          (__eo_add (__sign_variations_rec (Term.Rational (native_mk_rational 0 1))
              (__cov_seq_values s lo))
            (__eo_neg (__sign_variations_rec (Term.Rational (native_mk_rational 0 1))
              (__cov_seq_values s hi))))
          (Term.Numeral 1)))
      (Term.Boolean false))
    (Term.Boolean false)

theorem lev_continuous (l : List Rat) : Continuous (lev l) := by
  induction l with
  | nil => exact continuous_const
  | cons a l ih => exact continuous_const.add (continuous_id.mul ih)

theorem eo_ite_true_cases {c x y : Term} (h : __eo_ite c x y = Term.Boolean true) :
    (c = Term.Boolean true ∧ x = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ y = Term.Boolean true) := by
  unfold __eo_ite at h
  by_cases hc : c = Term.Boolean true
  · subst hc; simp [native_ite, native_teq] at h; exact Or.inl ⟨rfl, h⟩
  · by_cases hc' : c = Term.Boolean false
    · subst hc'; simp [native_ite, native_teq] at h; exact Or.inr ⟨rfl, h⟩
    · simp [native_ite, native_teq, hc, hc'] at h

theorem eo_and_true_inv {x y : Term} (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  cases x <;> cases y <;> simp_all [__eo_and, native_and]
  all_goals first
    | (rename_i w1 n1 w2 n2; simp [__eo_requires, native_ite, native_teq, native_not] at h;
        split at h <;> simp_all)
    | skip

/-- What `$valid_ran` checks without Sturm's theorem: rational bounds at which the
polynomial has opposite signs. -/
theorem validRan_bounds {q lo hi s : Term} (h : validRan q lo hi s = Term.Boolean true) :
    ∃ a b : Rat, ∃ lst : List Rat, lo = Term.Rational a ∧ hi = Term.Rational b ∧
      RatList q lst ∧ lev lst a * lev lst b < 0 := by
  unfold validRan at h
  rcases eo_ite_true_cases h with ⟨hq, h⟩ | ⟨_, h⟩
  · obtain ⟨hlo, hhi⟩ := eo_and_true_inv hq
    have hlo' : ∃ a, lo = Term.Rational a := by
      cases lo <;> simp_all [__eo_is_q, __eo_is_q_internal, native_and, native_not, native_teq]
    have hhi' : ∃ b, hi = Term.Rational b := by
      cases hi <;> simp_all [__eo_is_q, __eo_is_q_internal, native_and, native_not, native_teq]
    rcases hlo' with ⟨a, rfl⟩
    rcases hhi' with ⟨b, rfl⟩
    rcases eo_ite_true_cases h with ⟨_, h⟩ | ⟨_, h⟩
    · obtain ⟨hneg, _⟩ := eo_and_true_inv h
      have hP : __upoly_of_list q ≠ Term.Stuck := by
        intro hs; rw [hs] at hneg; simp [__upoly_eval, __eo_mul, __eo_is_neg] at hneg
      obtain ⟨lst, hq, l', hl', hlev⟩ := upoly_of_list_den hP
      obtain ⟨ra, hra, hra'⟩ := upoly_eval_rat hl' a
      obtain ⟨rb, hrb, hrb'⟩ := upoly_eval_rat hl' b
      rw [hra, hrb] at hneg
      simp [__eo_mul, __eo_is_neg, native_qmult, native_qlt, native_mk_rational_zero'] at hneg
      refine ⟨a, b, lst, rfl, rfl, hq, ?_⟩
      rw [← hlev, ← hlev, ← hra', ← hrb']
      exact_mod_cast hneg
    · cases h
  · cases h

-- TODO(sturm): proved from Sturm's theorem; until then this is the one open obligation.
set_option warningAsError false in
/-- The one consequence of `$valid_ran` that rests on Sturm's theorem: the bounds are in
order. A Sturm count `V(lo) - V(hi)` of one root needs `lo < hi`. -/
theorem validRan_lt {q : Term} {a b : Rat} {s : Term}
    (h : validRan q (Term.Rational a) (Term.Rational b) s = Term.Boolean true) : a < b := by
  sorry

/-- The body of the choice `@ran` translates to, under `@x ↦ t`. -/
private theorem ran_body_eval (M : SmtModel) {q : Term} {lst : List Rat} (hq : RatList q lst)
    (a b : Rat) (t : Real) :
    ∃ bb, __smtx_model_eval (pushX M t)
      (SmtTerm.and
        (SmtTerm.eq (__eo_to_smt_coeffs_at q covX) (SmtTerm.Rational (native_mk_rational 0 1)))
        (SmtTerm.and (SmtTerm.lt (SmtTerm.Rational a) covX) (SmtTerm.lt covX (SmtTerm.Rational b)))) =
      SmtValue.Boolean bb ∧ (bb = true ↔ (lev lst t = 0 ∧ (a : Real) < t ∧ t < b)) := by
  have hP := (coeffs_at_eval (pushX M t) hq covX typeof_covX t (eval_covX_push M t)).2
  refine ⟨decide (lev lst t = 0) && (decide ((a : Real) < t) && decide (t < b)), ?_, by simp⟩
  have hl : __smtx_model_eval (pushX M t) (SmtTerm.lt (SmtTerm.Rational a) covX) =
      SmtValue.Boolean (decide ((a : Real) < t)) := by
    rw [__smtx_model_eval, eval_covX_push]
    simp [__smtx_model_eval, __smtx_model_eval_lt, native_rlt, native_rat_to_real]
  have hr : __smtx_model_eval (pushX M t) (SmtTerm.lt covX (SmtTerm.Rational b)) =
      SmtValue.Boolean (decide (t < (b : Real))) := by
    rw [__smtx_model_eval, eval_covX_push]
    simp [__smtx_model_eval, __smtx_model_eval_lt, native_rlt, native_rat_to_real]
  have he : __smtx_model_eval (pushX M t)
      (SmtTerm.eq (__eo_to_smt_coeffs_at q covX) (SmtTerm.Rational (native_mk_rational 0 1))) =
      SmtValue.Boolean (decide (lev lst t = 0)) := by
    rw [__smtx_model_eval, hP]
    simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq, native_rat_to_real,
      native_mk_rational_zero']
  have hi : __smtx_model_eval (pushX M t)
      (SmtTerm.and (SmtTerm.lt (SmtTerm.Rational a) covX) (SmtTerm.lt covX (SmtTerm.Rational b))) =
      SmtValue.Boolean (decide ((a : Real) < t) && decide (t < (b : Real))) := by
    rw [__smtx_model_eval, hl, hr]
    simp [__smtx_model_eval_and, native_and]
  rw [__smtx_model_eval, he, hi]
  simp [__smtx_model_eval_and, native_and]

/-- A valid `@ran` with a translation denotes a root of its polynomial between its bounds. -/
theorem ran_val (M : SmtModel) (hM : model_wf M) (q lo hi s : Term)
    (hV : validRan q lo hi s = Term.Boolean true)
    (hTy : __smtx_typeof (__eo_to_smt (Term.UOp4 UserOp4._at_ran q lo hi s)) = SmtType.Real) :
    ∃ a b : Rat, ∃ lst : List Rat, lo = Term.Rational a ∧ hi = Term.Rational b ∧ RatList q lst ∧
      (a : Real) < covDen M (Term.UOp4 UserOp4._at_ran q lo hi s) ∧
      covDen M (Term.UOp4 UserOp4._at_ran q lo hi s) < b ∧
      lev lst (covDen M (Term.UOp4 UserOp4._at_ran q lo hi s)) = 0 := by
  obtain ⟨a, b, lst, rfl, rfl, hq, hsgn⟩ := validRan_bounds hV
  have hab : (a : Real) < b := by exact_mod_cast validRan_lt hV
  refine ⟨a, b, lst, rfl, rfl, hq, ?_⟩
  -- a root between the bounds
  have hroot : ∃ t : Real, (a : Real) < t ∧ t < b ∧ lev lst t = 0 := by
    have hc := (lev_continuous lst).continuousOn (s := Set.Icc (a : Real) b)
    rcases lt_or_gt_of_ne (show lev lst a ≠ 0 by intro h0; rw [h0] at hsgn; simp at hsgn)
      with hneg | hpos
    · have hb : 0 < lev lst b := by
        by_contra hb; have hb := not_lt.mp hb; nlinarith
      obtain ⟨t, ⟨ht1, ht2⟩, ht⟩ := intermediate_value_Ioo hab.le hc ⟨hneg, hb⟩
      exact ⟨t, ht1, ht2, ht⟩
    · have hb : lev lst b < 0 := by
        by_contra hb; have hb := not_lt.mp hb; nlinarith
      obtain ⟨t, ⟨ht1, ht2⟩, ht⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, hpos⟩
      exact ⟨t, ht1, ht2, ht⟩
  obtain ⟨t, ht1, ht2, ht⟩ := hroot
  rcases TranslationProofs.eo_to_smt_ran_cases q (Term.Rational a) (Term.Rational b) s with
    h | ⟨rl, rh, hrl, hrh, hS, h⟩
  · rw [h] at hTy; simp at hTy
  · cases hrl; cases hrh
    have hEval := eval_of_real M hM _ hTy
    rw [h] at hEval
    generalize covDen M (Term.UOp4 UserOp4._at_ran q (Term.Rational a) (Term.Rational b) s) = w
      at hEval ⊢
    have hSat : ∃ v : SmtValue, __smtx_typeof_value v = SmtType.Real ∧
        __smtx_value_canonical M.usortDom v = true ∧
        __smtx_model_eval (native_model_push M (native_string_lit "@x") SmtType.Real v)
          (SmtTerm.and
            (SmtTerm.eq (__eo_to_smt_coeffs_at q covX) (SmtTerm.Rational (native_mk_rational 0 1)))
            (SmtTerm.and (SmtTerm.lt (SmtTerm.Rational a) covX)
              (SmtTerm.lt covX (SmtTerm.Rational b)))) = SmtValue.Boolean true := by
      refine ⟨SmtValue.Real t, rfl, rfl, ?_⟩
      obtain ⟨bb, hbb, hbb'⟩ := ran_body_eval M hq a b t
      rw [show native_model_push M (native_string_lit "@x") SmtType.Real (SmtValue.Real t) =
        pushX M t from rfl, hbb, hbb'.mpr ⟨ht, ht1, ht2⟩]
    rw [__smtx_model_eval] at hEval
    simp only [hSat, dite_true] at hEval
    have hspec := Classical.choose_spec hSat
    rw [hEval] at hspec
    obtain ⟨_, _, hbody⟩ := hspec
    obtain ⟨bb, hbb, hbb'⟩ := ran_body_eval M hq a b w
    rw [show native_model_push M (native_string_lit "@x") SmtType.Real (SmtValue.Real w) =
      pushX M w from rfl, hbb] at hbody
    cases hbody
    obtain ⟨h1, h2, h3⟩ := hbb'.mp rfl
    exact ⟨h2, h3, h1⟩

/-! ### Comparing endpoints -/

/-- A finite endpoint: a rational, or a `@ran` with a translation. -/
def FinEnd (e : Term) : Prop :=
  (∃ q, e = Term.Rational q) ∨
    (∃ c a b d, e = Term.UOp4 UserOp4._at_ran c a b d ∧
      __smtx_typeof (__eo_to_smt e) = SmtType.Real)

private theorem eo_not_true {x : Term} (h : __eo_not x = Term.Boolean true) :
    x = Term.Boolean false := by
  cases x <;> simp_all [__eo_not, native_not]

private theorem rat_le_of_not_gt {x y : Term} (h : __eo_gt x y = Term.Boolean false)
    (hx : ∃ a, x = Term.Rational a) : ∃ a b, x = Term.Rational a ∧ y = Term.Rational b ∧ a ≤ b := by
  rcases hx with ⟨a, rfl⟩
  cases y <;> simp_all [__eo_gt, native_qlt]

private theorem rat_le_of_not_gt' {x y : Term} (h : __eo_gt x y = Term.Boolean false)
    (hy : ∃ b, y = Term.Rational b) : ∃ a b, x = Term.Rational a ∧ y = Term.Rational b ∧ a ≤ b := by
  rcases hy with ⟨b, rfl⟩
  cases x <;> simp_all [__eo_gt, native_qlt]

theorem covDen_rational (M : SmtModel) (q : Rat) : covDen M (Term.Rational q) = q := by
  simp [covDen, arith_poly_norm_atom_denote_real_of_rational]

theorem finEnd_ran_typed {c a b d : Term} (h : FinEnd (Term.UOp4 UserOp4._at_ran c a b d)) :
    __smtx_typeof (__eo_to_smt (Term.UOp4 UserOp4._at_ran c a b d)) = SmtType.Real := by
  rcases h with ⟨_, h'⟩ | ⟨_, _, _, _, _, hT⟩
  · cases h'
  · exact hT

theorem finEnd_rat_of_not_ran {e : Term} (h : FinEnd e)
    (hn : ∀ c a b d, e = Term.UOp4 UserOp4._at_ran c a b d -> False) : ∃ q, e = Term.Rational q := by
  rcases h with h' | ⟨c, a, b, d, rfl, _⟩
  · exact h'
  · exact absurd rfl (hn c a b d)

/-- `$cov_lt` compares finite endpoints by value. -/
theorem cov_lt_sound (M : SmtModel) (hM : model_wf M) {a b : Term} (ha : FinEnd a) (hb : FinEnd b)
    (h : __cov_lt a b = Term.Boolean true) : covDen M a < covDen M b := by
  unfold __cov_lt at h
  split at h
  · simp at h
  · simp at h
  · -- two real algebraic numbers
    rename_i q1 l1 h1 s1 q2 l2 h2 s2
    obtain ⟨hv, hn⟩ := eo_and_true_inv h
    obtain ⟨hv1, hv2⟩ := eo_and_true_inv hv
    obtain ⟨a1, b1, _, rfl, rfl, _, _, hb1, _⟩ := ran_val M hM q1 l1 h1 s1 hv1 (finEnd_ran_typed ha)
    obtain ⟨a2, b2, _, rfl, rfl, _, ha2, _, _⟩ := ran_val M hM q2 l2 h2 s2 hv2 (finEnd_ran_typed hb)
    obtain ⟨x, y, hx, hy, hxy⟩ := rat_le_of_not_gt (eo_not_true hn) ⟨b1, rfl⟩
    cases hx; cases hy
    have : (b1 : Real) ≤ a2 := by exact_mod_cast hxy
    linarith
  · -- a real algebraic number below a rational
    rename_i q1 l1 h1 s1 hbS hbR
    obtain ⟨hv1, hn⟩ := eo_and_true_inv h
    obtain ⟨a1, b1, _, rfl, rfl, _, _, hb1, _⟩ := ran_val M hM q1 l1 h1 s1 hv1 (finEnd_ran_typed ha)
    obtain ⟨y, rfl⟩ := finEnd_rat_of_not_ran hb (fun c a b d h' => hbR c a b d h')
    obtain ⟨x, y', hx, hy, hxy⟩ := rat_le_of_not_gt (eo_not_true hn) ⟨b1, rfl⟩
    cases hx; cases hy
    rw [covDen_rational]
    have : (b1 : Real) ≤ y := by exact_mod_cast hxy
    linarith
  · -- a rational below a real algebraic number
    rename_i q2 l2 h2 s2 haS haR
    obtain ⟨hv2, hn⟩ := eo_and_true_inv h
    obtain ⟨a2, b2, _, rfl, rfl, _, ha2, _, _⟩ := ran_val M hM q2 l2 h2 s2 hv2 (finEnd_ran_typed hb)
    obtain ⟨x, rfl⟩ := finEnd_rat_of_not_ran ha (fun c a b d h' => haR c a b d h')
    obtain ⟨x', y, hx, hy, hxy⟩ := rat_le_of_not_gt' (eo_not_true hn) ⟨a2, rfl⟩
    cases hx; cases hy
    rw [covDen_rational]
    have : (x : Real) ≤ a2 := by exact_mod_cast hxy
    linarith
  · -- two rationals
    rename_i _ hs2 _ hr2 _
    obtain ⟨x, rfl⟩ := finEnd_rat_of_not_ran ha (fun c a b d h' => hs2 c a b d h')
    obtain ⟨y, rfl⟩ := finEnd_rat_of_not_ran hb (fun c a b d h' => hr2 c a b d h')
    simp [__eo_gt, native_qlt] at h
    rw [covDen_rational, covDen_rational]
    exact_mod_cast h

theorem cov_above_shape (l : Term)
    (hTy : __smtx_typeof (__eo_to_smt_cov_above l (__eo_to_smt l)) ≠ SmtType.None) :
    l = Term.UOp UserOp._at__at_cov_minus_inf ∨ FinEnd l := by
  unfold __eo_to_smt_cov_above at hTy
  split at hTy
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, _, _, _, rfl,
      real_of_cmp_x (op := SmtTerm.gt) typeof_gt_eq (Or.inl hTy)⟩)
  · exact absurd (by simp) hTy

theorem cov_below_shape (r : Term)
    (hTy : __smtx_typeof (__eo_to_smt_cov_below r (__eo_to_smt r)) ≠ SmtType.None) :
    r = Term.UOp UserOp._at__at_cov_plus_inf ∨ FinEnd r := by
  unfold __eo_to_smt_cov_below at hTy
  split at hTy
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, _, _, _, rfl,
      real_of_cmp_x (op := SmtTerm.lt) typeof_lt_eq (Or.inl hTy)⟩)
  · exact absurd (by simp) hTy

/-- `$cov_bound_lt l s` with a rational `s` puts `s` above `l`. -/
theorem bound_lt_left (M : SmtModel) (hM : model_wf M) {l : Term} {q : Rat}
    (hl : l = Term.UOp UserOp._at__at_cov_minus_inf ∨ FinEnd l)
    (h : __cov_bound_lt l (Term.Rational q) = Term.Boolean true) : InL M l q := by
  rcases hl with rfl | hl
  · exact Or.inl rfl
  · right
    have hne : l ≠ Term.UOp UserOp._at__at_cov_minus_inf := by
      rintro rfl; rcases hl with ⟨_, h'⟩ | ⟨_, _, _, _, h', _⟩ <;> cases h'
    have hne' : l ≠ Term.UOp UserOp._at__at_cov_plus_inf := by
      rintro rfl; rcases hl with ⟨_, h'⟩ | ⟨_, _, _, _, h', _⟩ <;> cases h'
    have hEq : __cov_bound_lt l (Term.Rational q) = __cov_lt l (Term.Rational q) := by
      unfold __cov_bound_lt
      split <;> simp_all [__cov_lt]
    rw [hEq] at h
    have := cov_lt_sound M hM hl (Or.inl ⟨q, rfl⟩) h
    rwa [covDen_rational] at this

/-- `$cov_bound_lt s r` with a rational `s` puts `s` below `r`. -/
theorem bound_lt_right (M : SmtModel) (hM : model_wf M) {r : Term} {q : Rat}
    (hr : r = Term.UOp UserOp._at__at_cov_plus_inf ∨ FinEnd r)
    (h : __cov_bound_lt (Term.Rational q) r = Term.Boolean true) : InR M r q := by
  rcases hr with rfl | hr
  · exact Or.inl rfl
  · right
    have hne : r ≠ Term.UOp UserOp._at__at_cov_minus_inf := by
      rintro rfl; rcases hr with ⟨_, h'⟩ | ⟨_, _, _, _, h', _⟩ <;> cases h'
    have hne' : r ≠ Term.UOp UserOp._at__at_cov_plus_inf := by
      rintro rfl; rcases hr with ⟨_, h'⟩ | ⟨_, _, _, _, h', _⟩ <;> cases h'
    have hEq : __cov_bound_lt (Term.Rational q) r = __cov_lt (Term.Rational q) r := by
      unfold __cov_bound_lt
      split <;> simp_all [__cov_lt]
    rw [hEq] at h
    have := cov_lt_sound M hM (Or.inl ⟨q, rfl⟩) hr h
    rwa [covDen_rational] at this

/-! ### Pieces of a covering -/

local notation "MINF" => Term.UOp UserOp._at__at_cov_minus_inf
local notation "PINF" => Term.UOp UserOp._at__at_cov_plus_inf

/-- The four shapes `$mk_cover_piece x l r` takes. -/
theorem mk_cover_piece_cases (x l r : Term) (h : __mk_cover_piece x l r ≠ Term.Stuck) :
    x ≠ Term.Stuck ∧ l ≠ Term.Stuck ∧ r ≠ Term.Stuck ∧ (
    (l = MINF ∧ r = PINF ∧ __mk_cover_piece x l r = Term.Boolean true) ∨
    (l = MINF ∧ r ≠ PINF ∧ __mk_cover_piece x l r = CovRel.lt.atom x r) ∨
    (l ≠ MINF ∧ r = PINF ∧ __mk_cover_piece x l r = CovRel.gt.atom x l) ∨
    (l ≠ MINF ∧ r ≠ PINF ∧ l ≠ PINF ∧ r ≠ MINF ∧
      ((l = r ∧ __mk_cover_piece x l r = CovRel.eq.atom x l) ∨
       (l ≠ r ∧ __mk_cover_piece x l r =
          Term.Apply (Term.Apply (Term.UOp UserOp.and) (CovRel.gt.atom x l))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) (CovRel.lt.atom x r))
              (Term.Boolean true)))))) := by
  have hx : x ≠ Term.Stuck := by rintro rfl; simp [__mk_cover_piece] at h
  have hl : l ≠ Term.Stuck := by rintro rfl; cases x <;> simp_all [__mk_cover_piece]
  have hr : r ≠ Term.Stuck := by rintro rfl; cases x <;> cases l <;> simp_all [__mk_cover_piece]
  refine ⟨hx, hl, hr, ?_⟩
  unfold __mk_cover_piece at h ⊢
  split at h
  · exact absurd rfl hx
  · exact absurd rfl hl
  · exact absurd rfl hr
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · rename_i hne; exact Or.inr (Or.inl ⟨rfl, hne, rfl⟩)
  · rename_i hne; exact Or.inr (Or.inr (Or.inl ⟨hne, rfl, rfl⟩))
  · rename_i _ _ _ _ _ hlm _ hrp _
    obtain ⟨hc, hb⟩ := eo_requires_eq_body h
    have hlp : l ≠ PINF := by
      rintro rfl; simp [__eo_or, __eo_is_eq, native_or, native_and, native_not, native_teq] at hc
    have hrm : r ≠ MINF := by
      rintro rfl; simp [__eo_or, __eo_is_eq, native_or, native_and, native_not, native_teq] at hc
    refine Or.inr (Or.inr (Or.inr ⟨hlm, hrp, hlp, hrm, ?_⟩))
    rw [hb]
    by_cases hlr : l = r
    · subst hlr
      left
      refine ⟨rfl, ?_⟩
      simp [__eo_ite, __eo_is_eq, native_and, native_not, native_teq, hl, native_ite,
        CovRel.atom, CovRel.op]
    · right
      refine ⟨hlr, ?_⟩
      simp [__eo_ite, __eo_is_eq, native_and, native_not, native_teq, hl, hr, native_ite,
        Ne.symm hlr, CovRel.atom, CovRel.op]

/-- A true comparison against an arithmetic term compares the values. -/
theorem covRel_true (M : SmtModel) (hM : model_wf M) (r : CovRel) (a b : Term) (hb : CovArith b)
    (h : eo_interprets M (r.atom a b) true) : r.holds (covDen M a) (covDen M b) := by
  obtain ⟨_, hE⟩ := covRel_eval M hM r a b hb (RuleProofs.eo_has_bool_type_of_interprets_true M _ h)
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_true _ hE' => rw [hE] at hE'; simpa using hE'

/-- A true piece of a covering puts `x` strictly between its endpoints, or on a point. -/
theorem piece_true (M : SmtModel) (hM : model_wf M) (x l r : Term)
    (hP : __mk_cover_piece x l r ≠ Term.Stuck)
    (hlA : l ≠ MINF -> CovArith l) (hrA : r ≠ PINF -> CovArith r)
    (hT : eo_interprets M (__mk_cover_piece x l r) true) :
    (InL M l (covDen M x) ∧ InR M r (covDen M x)) ∨
      (l = r ∧ l ≠ MINF ∧ l ≠ PINF ∧ covDen M x = covDen M l) := by
  obtain ⟨_, _, _, hc⟩ := mk_cover_piece_cases x l r hP
  rcases hc with ⟨rfl, rfl, _⟩ | ⟨rfl, hr, hE⟩ | ⟨hl, rfl, hE⟩ | ⟨hl, hr, hlp, _, ⟨rfl, hE⟩ | ⟨_, hE⟩⟩
  · exact Or.inl ⟨Or.inl rfl, Or.inl rfl⟩
  · rw [hE] at hT
    exact Or.inl ⟨Or.inl rfl, Or.inr (covRel_true M hM CovRel.lt x r (hrA hr) hT)⟩
  · rw [hE] at hT
    exact Or.inl ⟨Or.inr (covRel_true M hM CovRel.gt x l (hlA hl) hT), Or.inl rfl⟩
  · rw [hE] at hT
    exact Or.inr ⟨rfl, hl, hlp, covRel_true M hM CovRel.eq x l (hlA hl) hT⟩
  · rw [hE] at hT
    have h1 := RuleProofs.eo_interprets_and_left M _ _ hT
    have h2 := RuleProofs.eo_interprets_and_left M _ _ (RuleProofs.eo_interprets_and_right M _ _ hT)
    exact Or.inl ⟨Or.inr (covRel_true M hM CovRel.gt x l (hlA hl) h1),
      Or.inr (covRel_true M hM CovRel.lt x r (hrA hr) h2)⟩

/-- Comparisons of two terms of one arithmetic sort are Boolean. -/
theorem covRel_bool (r : CovRel) (a b : Term) (T : SmtType)
    (ha : __smtx_typeof (__eo_to_smt a) = T) (hb : __smtx_typeof (__eo_to_smt b) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) : RuleProofs.eo_has_bool_type (r.atom a b) := by
  have hR : ∀ R : SmtType, (R = SmtType.Int ∨ R = SmtType.Real) ->
      __smtx_typeof_arith_overload_op_2_ret R R SmtType.Bool = SmtType.Bool := by
    intro R hR; rcases hR with rfl | rfl <;> rfl
  unfold RuleProofs.eo_has_bool_type
  cases r
  · rw [show __eo_to_smt (CovRel.lt.atom a b) = SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) from rfl,
      typeof_lt_eq, ha, hb, hR T hT]
  · rw [show __eo_to_smt (CovRel.leq.atom a b) = SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) from rfl,
      typeof_leq_eq, ha, hb, hR T hT]
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b (ha.trans hb.symm)
      (by rw [ha]; rcases hT with rfl | rfl <;> simp)
  · rw [show __eo_to_smt (CovRel.geq.atom a b) = SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) from rfl,
      typeof_geq_eq, ha, hb, hR T hT]
  · rw [show __eo_to_smt (CovRel.gt.atom a b) = SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) from rfl,
      typeof_gt_eq, ha, hb, hR T hT]

/-- An endpoint the Eunoia type checker compares with `x` has the SMT sort of `x`. -/
private theorem same_arith_of_typeof_lt (x e : Term)
    (hxT : RuleProofs.eo_has_smt_translation x) (heT : RuleProofs.eo_has_smt_translation e)
    (h : __eo_typeof_lt (__eo_typeof x) (__eo_typeof e) = Term.Bool) :
    ∃ T, __smtx_typeof (__eo_to_smt x) = T ∧ __smtx_typeof (__eo_to_smt e) = T ∧
      (T = SmtType.Int ∨ T = SmtType.Real) := by
  rw [TranslationProofs.eo_to_smt_typeof_matches_translation x hxT,
    TranslationProofs.eo_to_smt_typeof_matches_translation e heT]
  rcases RuleProofs.eo_typeof_lt_bool_cases _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, rfl, by rw [h1, h2], Or.inl (by rw [h1]; rfl)⟩
  · exact ⟨_, rfl, by rw [h1, h2], Or.inr (by rw [h1]; rfl)⟩

/-- A piece of a covering that the Eunoia type checker accepts is Boolean. -/
theorem piece_bool (x l r : Term) (hP : __mk_cover_piece x l r ≠ Term.Stuck)
    (hxT : RuleProofs.eo_has_smt_translation x)
    (hlT : l ≠ MINF -> RuleProofs.eo_has_smt_translation l)
    (hrT : r ≠ PINF -> RuleProofs.eo_has_smt_translation r)
    (hTy : __eo_typeof (__mk_cover_piece x l r) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__mk_cover_piece x l r) := by
  obtain ⟨_, _, _, hc⟩ := mk_cover_piece_cases x l r hP
  rcases hc with ⟨rfl, rfl, hE⟩ | ⟨rfl, hr, hE⟩ | ⟨hl, rfl, hE⟩ | ⟨hl, hr, _, _, ⟨rfl, hE⟩ | ⟨_, hE⟩⟩ <;>
    rw [hE] at hTy ⊢
  · exact RuleProofs.eo_has_bool_type_true
  · obtain ⟨T, h1, h2, hT⟩ := same_arith_of_typeof_lt x r hxT (hrT hr) hTy
    exact covRel_bool CovRel.lt x r T h1 h2 hT
  · obtain ⟨T, h1, h2, hT⟩ := same_arith_of_typeof_lt x l hxT (hlT hl) hTy
    exact covRel_bool CovRel.gt x l T h1 h2 hT
  · have hEq := (RuleProofs.eo_typeof_eq_bool_same _ _ hTy).1
    have h1 := TranslationProofs.eo_to_smt_typeof_matches_translation x hxT
    have h2 := TranslationProofs.eo_to_smt_typeof_matches_translation l (hlT hl)
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x l (by rw [h1, h2, hEq]) hxT
  · obtain ⟨hA, hB⟩ := RuleProofs.eo_typeof_or_bool_args _ _ hTy
    obtain ⟨hB1, _⟩ := RuleProofs.eo_typeof_or_bool_args _ _ hB
    obtain ⟨T, h1, h2, hT⟩ := same_arith_of_typeof_lt x l hxT (hlT hl) hA
    obtain ⟨T', h1', h2', hT'⟩ := same_arith_of_typeof_lt x r hxT (hrT hr) hB1
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ (covRel_bool CovRel.gt x l T h1 h2 hT)
      (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ (covRel_bool CovRel.lt x r T' h1' h2' hT')
        RuleProofs.eo_has_bool_type_true)

/-- A coverings literal only reads the sign of the value of its polynomial. -/
theorem litSem_of_same_sign (neg : Bool) (r : CovRel) {a b : Real}
    (h : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) ∨ (a = 0 ∧ b = 0)) :
    litSem neg r a ↔ litSem neg r b := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨rfl, rfl⟩
  all_goals cases neg <;> cases r <;> simp only [litSem, CovRel.holds] <;> grind

/-- A Boolean term is true or false in every model. -/
theorem interprets_true_or_false (M : SmtModel) (hM : model_wf M) (t : Term)
    (hB : RuleProofs.eo_has_bool_type t) :
    eo_interprets M t true ∨ eo_interprets M t false := by
  have hEvalTy : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Bool := by
    have := Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by unfold term_has_non_none_type; rw [hB]; simp)
    rw [this]; exact hB
  rcases bool_value_canonical hEvalTy with ⟨b, hb⟩
  cases b
  · exact Or.inr (RuleProofs.eo_interprets_of_bool_eval M t false hB hb)
  · exact Or.inl (RuleProofs.eo_interprets_of_bool_eval M t true hB hb)

/-- The endpoints of a typed `@sgn_inv`. -/
theorem sgn_inv_typed (q l r : Term)
    (hB : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv q) l) r)) :
    (l = MINF ∨ FinEnd l) ∧ (r = PINF ∨ FinEnd r) := by
  unfold RuleProofs.eo_has_bool_type at hB
  rw [__eo_to_smt.eq_def] at hB
  simp only at hB
  have hOr := TranslationProofs.typeof_or_parts (TranslationProofs.non_none_of_bool hB)
  have hThr := TranslationProofs.typeof_not_part (TranslationProofs.non_none_of_bool hOr.1)
  have hBody := TranslationProofs.typeof_exists_part (TranslationProofs.non_none_of_bool hThr)
  have hAnd := TranslationProofs.typeof_and_parts (TranslationProofs.non_none_of_bool hBody)
  have hI := TranslationProofs.typeof_and_parts (TranslationProofs.non_none_of_bool hAnd.1)
  exact ⟨cov_above_shape l (TranslationProofs.non_none_of_bool hI.1),
    cov_below_shape r (TranslationProofs.non_none_of_bool hI.2)⟩

theorem finEnd_covArith {e : Term} (h : FinEnd e) : CovArith e := by
  rcases h with ⟨q, rfl⟩ | ⟨_, _, _, _, _, hT⟩
  · right; rw [__eo_to_smt.eq_def]; simp [__smtx_typeof]
  · exact Or.inr hT

end CoveringsProofs
