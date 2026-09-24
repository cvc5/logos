module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

/-! ## Conclusion abbreviations -/

private abbrev ubvToIntTerm (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.ubv_to_int) x

private abbrev intToBvTerm (w n : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n

private abbrev geqTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b

private abbrev ltTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b

private abbrev int_pow2Term (w : Term) : Term :=
  Term.Apply (Term.UOp UserOp.int_pow2) w

private abbrev bvugeTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) a) b

private abbrev iteTerm (c t e : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e

/-- The right-hand side of the conclusion. -/
private abbrev ufGeqElimRhs (x n w : Term) : Term :=
  iteTerm (geqTerm n (int_pow2Term w)) (Term.Boolean false)
    (iteTerm (ltTerm n (Term.Numeral 0)) (Term.Boolean true)
      (bvugeTerm x (intToBvTerm w n)))

/-- The left-hand side of the conclusion. -/
private abbrev ufGeqElimLhs (x n : Term) : Term :=
  geqTerm (ubvToIntTerm x) n

private abbrev ufGeqElimConclusion (x n w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (ufGeqElimLhs x n)) (ufGeqElimRhs x n w)

/-! ## Private eval / typeof term-equation rewrites (not in Support) -/

private theorem smtx_eval_boolean_term_eq
    (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_geq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_lt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.lt x y) =
      __smtx_model_eval_lt (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_int_pow2_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.int_pow2 x) =
      __smtx_model_eval_int_pow2 (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvuge_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvuge x y) =
      __smtx_model_eval_bvuge (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_typeof_geq_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.geq x y) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x) (__smtx_typeof y)
        SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_lt_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.lt x y) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x) (__smtx_typeof y)
        SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_int_pow2_term_eq
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.int_pow2 x) =
      native_ite (native_Teq (__smtx_typeof x) SmtType.Int) SmtType.Int
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_bvuge_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvuge x y) =
      __smtx_typeof_bv_op_2_ret (__smtx_typeof x) (__smtx_typeof y)
        SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_ite_term_eq
    (c t e : SmtTerm) :
    __smtx_typeof (SmtTerm.ite c t e) =
      __smtx_typeof_ite (__smtx_typeof c) (__smtx_typeof t) (__smtx_typeof e) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-! ## Requires-guard / premise-shape helpers -/

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true := hProg'.1
  have hBoth :
      __eo_eq x1 x2 = Term.Boolean true ∧ __eo_eq y1 y2 = Term.Boolean true := by
    have eq_stuck_or_bool :
        ∀ a b : Term, __eo_eq a b = Term.Stuck ∨
          ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
      intro a b
      by_cases ha : a = Term.Stuck
      · subst a
        exact Or.inl (by simp [__eo_eq])
      · by_cases hb : b = Term.Stuck
        · subst b
          exact Or.inl (by simp [__eo_eq])
        · exact Or.inr ⟨native_teq b a, by simp [__eo_eq]⟩
    rcases eq_stuck_or_bool x1 x2 with hX | ⟨b1, hX⟩
    · simp [__eo_and, hX] at hAnd
    rcases eq_stuck_or_bool y1 y2 with hY | ⟨b2, hY⟩
    · simp [__eo_and, hX, hY] at hAnd
    cases b1 <;> cases b2 <;> simp [__eo_and, hX, hY, native_and] at hAnd ⊢
  exact ⟨eq_of_eo_eq_true x1 x2 hBoth.1, eq_of_eo_eq_true y1 y2 hBoth.2⟩

private theorem requires_and_eq_self_true_body
    (w x body : Term)
    (hWNotStuck : w ≠ Term.Stuck)
    (hXNotStuck : x ≠ Term.Stuck) :
    __eo_requires (__eo_and (__eo_eq w w) (__eo_eq x x))
      (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and, eo_eq_self_true_of_ne_stuck w hWNotStuck,
    eo_eq_self_true_of_ne_stuck x hXNotStuck, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

/-- A non-stuck program forces all three args to be non-stuck. -/
private theorem args_ne_stuck_of_prog_not_stuck
    (x1 n1 w1 p : Term)
    (h : __eo_prog_uf_bv2nat_geq_elim x1 n1 w1 (Proof.pf p) ≠ Term.Stuck) :
    x1 ≠ Term.Stuck ∧ n1 ≠ Term.Stuck ∧ w1 ≠ Term.Stuck := by
  refine ⟨?_, ?_, ?_⟩
  · intro hX; subst x1; simp [__eo_prog_uf_bv2nat_geq_elim] at h
  · intro hN; subst n1
    cases x1 <;> simp [__eo_prog_uf_bv2nat_geq_elim] at h
  · intro hW; subst w1
    cases x1 <;> cases n1 <;> simp [__eo_prog_uf_bv2nat_geq_elim] at h

/-- The program is `Stuck` whenever the premise term does not have the expected
    `eq _ (bvsize _)` shape. Proven without casing the (non-stuck) args: every
    match arm that can fire under a non-matching `p` returns `Stuck`. -/
private theorem prog_stuck_of_p_not_shape
    (x1 n1 w1 p : Term)
    (hP : ∀ lw lx : Term, p ≠
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) lw)
          (Term.Apply (Term.UOp UserOp._at_bvsize) lx)) :
    __eo_prog_uf_bv2nat_geq_elim x1 n1 w1 (Proof.pf p) = Term.Stuck := by
  rw [__eo_prog_uf_bv2nat_geq_elim.eq_def]
  split
  case h_1 => rfl
  case h_2 => rfl
  case h_3 => rfl
  case h_4 =>
    -- body arm: the discriminant forced `p` to the expected shape, contradiction.
    exfalso
    rename_i lw lx _ _ _ heq
    have hp : p = Term.Apply (Term.Apply (Term.UOp UserOp.eq) lw)
        (Term.Apply (Term.UOp UserOp._at_bvsize) lx) := by injection heq
    exact hP lw lx hp
  case h_5 => rfl

/-- Shape lemma: a non-stuck program forces the premise to be an equality of
    a term and a `bvsize` term. -/
private theorem shape_of_prog_uf_bv2nat_geq_elim_not_stuck
    (x1 n1 w1 p : Term)
    (hX : x1 ≠ Term.Stuck) (hN : n1 ≠ Term.Stuck) (hW : w1 ≠ Term.Stuck)
    (h : __eo_prog_uf_bv2nat_geq_elim x1 n1 w1 (Proof.pf p) ≠ Term.Stuck) :
    ∃ lw lx : Term,
      p =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) lw)
          (Term.Apply (Term.UOp UserOp._at_bvsize) lx) := by
  apply Classical.byContradiction
  intro hC
  apply h
  apply prog_stuck_of_p_not_shape x1 n1 w1 p
  intro lw lx hp
  exact hC ⟨lw, lx, hp⟩

/-- When all args are non-stuck and the premise has the expected shape, the
    program reduces to the requires-guarded conclusion. -/
private theorem prog_uf_bv2nat_geq_elim_eq (x1 n1 w1 lw lx : Term)
    (hX : x1 ≠ Term.Stuck) (hN : n1 ≠ Term.Stuck) (hW : w1 ≠ Term.Stuck) :
    __eo_prog_uf_bv2nat_geq_elim x1 n1 w1
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) lw)
          (Term.Apply (Term.UOp UserOp._at_bvsize) lx))) =
      __eo_requires (__eo_and (__eo_eq w1 lw) (__eo_eq x1 lx))
        (Term.Boolean true) (ufGeqElimConclusion x1 n1 w1) := by
  rw [__eo_prog_uf_bv2nat_geq_elim.eq_4 x1 n1 w1 lw lx
    (fun hc => hX hc) (fun hc => hN hc) (fun hc => hW hc)]

/-! ## Typing inversion (factored into small lemmas) -/

/-- Inversion for `__eo_typeof_eq`: a `Bool` result forces both operand types
    to be equal. -/
private theorem typeof_eq_bool_inv (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    B = A := by
  have hNeStuck : __eo_typeof_eq A B ≠ Term.Stuck := by
    rw [h]; intro hc; cases hc
  by_cases hAStuck : A = Term.Stuck
  · subst A; simp [__eo_typeof_eq] at hNeStuck
  · by_cases hBStuck : B = Term.Stuck
    · subst B
      cases A <;> simp [__eo_typeof_eq] at hNeStuck
    · have hReqEq : __eo_typeof_eq A B =
          __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool := by
        cases A <;> cases B <;> simp_all [__eo_typeof_eq]
      rw [hReqEq] at hNeStuck
      have hReq' := hNeStuck
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hReq'
      exact eq_of_eo_eq_true A B hReq'.1

/-- Inversion for `__eo_typeof_lt`: a `Bool` result forces both operand types
    to be equal and an arithmetic type (`Int` or `Real`). -/
private theorem typeof_lt_bool_inv (A B : Term)
    (h : __eo_typeof_lt A B = Term.Bool) :
    B = A ∧ (A = Term.UOp UserOp.Int ∨ A = Term.UOp UserOp.Real) := by
  by_cases hA : A = Term.Stuck
  · subst A; simp [__eo_typeof_lt] at h
  · by_cases hB : B = Term.Stuck
    · subst B; cases A <;> simp [__eo_typeof_lt] at h
    · -- `lt A B = requires (eq A B) true (requires (arith A) true Bool)`
      have hForm : __eo_typeof_lt A B =
          __eo_requires (__eo_eq A B) (Term.Boolean true)
            (__eo_requires (__is_arith_type A) (Term.Boolean true) Term.Bool) := by
        cases A <;> cases B <;> simp_all [__eo_typeof_lt]
      rw [hForm] at h
      have hNe : __eo_requires (__eo_eq A B) (Term.Boolean true)
            (__eo_requires (__is_arith_type A) (Term.Boolean true) Term.Bool)
            ≠ Term.Stuck := by rw [h]; intro hc; cases hc
      have hNe' := hNe
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hNe'
      have hBA : B = A := eq_of_eo_eq_true A B hNe'.1
      -- now arith A must be true (non-stuck), forcing A = Int or Real
      have hArith : __is_arith_type A = Term.Boolean true := hNe'.2.2.1
      have hAArith : A = Term.UOp UserOp.Int ∨ A = Term.UOp UserOp.Real := by
        match A, hArith with
        | Term.UOp UserOp.Int, _ => exact Or.inl rfl
        | Term.UOp UserOp.Real, _ => exact Or.inr rfl
      exact ⟨hBA, hAArith⟩

/-- `__eo_requires g v body` is either `body` or `Stuck`. -/
private theorem requires_body_or_stuck (g v body : Term) :
    __eo_requires g v body = body ∨ __eo_requires g v body = Term.Stuck := by
  unfold __eo_requires
  by_cases hG : native_teq g v = true
  · by_cases hNe : native_not (native_teq g Term.Stuck) = true
    · left; simp [native_ite, hG, hNe]
    · right; simp [native_ite, hG, hNe]
  · right; simp [native_ite, hG]

/-- `__eo_typeof_lt` always returns `Bool` or `Stuck`. -/
private theorem typeof_lt_bool_or_stuck (A B : Term) :
    __eo_typeof_lt A B = Term.Bool ∨ __eo_typeof_lt A B = Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A; right; simp [__eo_typeof_lt]
  · by_cases hB : B = Term.Stuck
    · subst B; right; cases A <;> simp [__eo_typeof_lt]
    · have hForm : __eo_typeof_lt A B =
          __eo_requires (__eo_eq A B) (Term.Boolean true)
            (__eo_requires (__is_arith_type A) (Term.Boolean true) Term.Bool) := by
        cases A <;> cases B <;> simp_all [__eo_typeof_lt]
      rw [hForm]
      rcases requires_body_or_stuck (__eo_eq A B) (Term.Boolean true)
          (__eo_requires (__is_arith_type A) (Term.Boolean true) Term.Bool) with hO | hO
      · rw [hO]
        rcases requires_body_or_stuck (__is_arith_type A) (Term.Boolean true) Term.Bool
          with hI | hI
        · left; exact hI
        · right; exact hI
      · right; exact hO

/-- Inversion for `__eo_typeof_ite Bool U V = Bool`: forces both branches `Bool`. -/
private theorem typeof_ite_bool_inv (U V : Term)
    (h : __eo_typeof_ite Term.Bool U V = Term.Bool) :
    U = Term.Bool ∧ V = Term.Bool := by
  by_cases hU : U = Term.Stuck
  · subst U; simp [__eo_typeof_ite] at h
  · by_cases hV : V = Term.Stuck
    · subst V; simp [__eo_typeof_ite] at h
    · have hForm : __eo_typeof_ite Term.Bool U V =
          __eo_requires (__eo_eq U V) (Term.Boolean true) U := by
        cases U <;> cases V <;> simp_all [__eo_typeof_ite]
      rw [hForm] at h
      have hNe : __eo_requires (__eo_eq U V) (Term.Boolean true) U ≠ Term.Stuck := by
        rw [h]; intro hc; cases hc
      have hNe' := hNe
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hNe'
      have hVU : V = U := eq_of_eo_eq_true U V hNe'.1
      have hEqTrue : __eo_eq U V = Term.Boolean true := hNe'.1
      -- The requires now reduces to its body `U`, so `U = Bool`.
      have hUBool : U = Term.Bool := by
        rw [hEqTrue] at h
        simpa [__eo_requires, native_ite, native_teq, native_not,
          SmtEval.native_not, hU] using h
      exact ⟨hUBool, by rw [hVU]; exact hUBool⟩

/-- `__eo_typeof_ite C U V = Stuck` whenever the guard type `C` is not `Bool`. -/
private theorem typeof_ite_stuck_of_guard_ne_bool (C U V : Term)
    (hC : C ≠ Term.Bool) :
    __eo_typeof_ite C U V = Term.Stuck := by
  unfold __eo_typeof_ite
  split <;> simp_all

/-- `__eo_typeof_ite C U V = Bool` forces the guard type `C` to be `Bool`. -/
private theorem typeof_ite_guard_bool (C U V : Term)
    (h : __eo_typeof_ite C U V = Term.Bool) :
    C = Term.Bool := by
  apply Classical.byContradiction
  intro hC
  rw [typeof_ite_stuck_of_guard_ne_bool C U V hC] at h
  cases h

/-- Inversion for `__eo_typeof_bvult A B = Bool`: forces both `BitVec` of the
    same width. -/
private theorem typeof_bvult_bool_inv (A B : Term)
    (h : __eo_typeof_bvult A B = Term.Bool) :
    ∃ m, A = Term.Apply (Term.UOp UserOp.BitVec) m ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) m := by
  cases A with
  | Apply fA mA =>
      cases fA with
      | UOp opA =>
          cases opA <;> try (simp [__eo_typeof_bvult] at h)
          case BitVec =>
            cases B with
            | Apply fB mB =>
                cases fB with
                | UOp opB =>
                    cases opB <;> try (simp [__eo_typeof_bvult] at h)
                    case BitVec =>
                      by_cases hEq : mA = mB
                      · subst mB; exact ⟨mA, rfl, rfl⟩
                      · exfalso
                        -- `h : __eo_requires (__eo_eq mA mB) (Boolean true) Bool = Bool`
                        -- (already reduced by the `BitVec`/`BitVec` match).
                        have hEqMm : __eo_typeof_bvult
                              (Term.Apply (Term.UOp UserOp.BitVec) mA)
                              (Term.Apply (Term.UOp UserOp.BitVec) mB) = Term.Bool := h
                        rw [show __eo_typeof_bvult
                              (Term.Apply (Term.UOp UserOp.BitVec) mA)
                              (Term.Apply (Term.UOp UserOp.BitVec) mB) =
                            __eo_requires (__eo_eq mA mB) (Term.Boolean true)
                              Term.Bool from by simp [__eo_typeof_bvult]] at hEqMm
                        have hNe : __eo_requires (__eo_eq mA mB)
                              (Term.Boolean true) Term.Bool ≠ Term.Stuck := by
                          rw [hEqMm]; intro hc; cases hc
                        have hNe' := hNe
                        simp [__eo_requires, native_ite, native_teq,
                          native_not, SmtEval.native_not] at hNe'
                        exact hEq (eq_of_eo_eq_true mA mB hNe'.1).symm
                | _ => simp [__eo_typeof_bvult] at h
            | _ => simp [__eo_typeof_bvult] at h
      | _ => simp [__eo_typeof_bvult] at h
  | _ => simp [__eo_typeof_bvult] at h

/-- `int_to_bv` typing yields `Stuck` whenever the width type is not `Int`. -/
private theorem typeof_int_to_bv_stuck_of_width_ty_ne_int (A w B : Term)
    (hA : A ≠ Term.UOp UserOp.Int) :
    __eo_typeof_int_to_bv A w B = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

/-- Inversion for `int_to_bv` typing: a `BitVec` result with `Int` operand-type
    forces an `Int` width-type, a nonnegative-numeral width and matching width. -/
private theorem int_to_bv_type_bitvec_inv (A w m : Term)
    (h : __eo_typeof_int_to_bv A w (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    A = Term.UOp UserOp.Int ∧
      ∃ k, w = Term.Numeral k ∧ native_zlt (-1 : native_Int) k = true ∧
        m = Term.Numeral k := by
  by_cases hA : A = Term.UOp UserOp.Int
  · subst A
    refine ⟨rfl, ?_⟩
    cases hw : w <;> rw [hw] at h <;>
      first
      | (rename_i k
         have hRed :
             __eo_typeof_int_to_bv (Term.UOp UserOp.Int) (Term.Numeral k)
                 (Term.UOp UserOp.Int) =
               native_ite (native_zlt (-1 : native_Int) k)
                 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k))
                 Term.Stuck := by
           simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
             native_teq, native_not, SmtEval.native_not]
         rw [hRed] at h
         cases hPos : native_zlt (-1 : native_Int) k <;>
           simp [native_ite, hPos] at h
         exact ⟨k, rfl, hPos, h.symm⟩)
      | (exfalso
         simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
           native_teq, native_not, SmtEval.native_not] at h)
  · exfalso
    rw [typeof_int_to_bv_stuck_of_width_ty_ne_int A w (Term.UOp UserOp.Int) hA] at h
    simp at h

/-- From the result type being `Bool`, recover the width as a nonnegative
    numeral, the bit-vector type of `x` and the `Int` type of `n`. -/
private theorem typeof_args_of_conclusion_bool (x n w : Term) :
    __eo_typeof (ufGeqElimConclusion x n w) = Term.Bool ->
    ∃ k, w = Term.Numeral k ∧ native_zleq 0 k = true ∧
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k) ∧
      __eo_typeof n = Term.UOp UserOp.Int := by
  intro hTy
  -- Reduce the typeof of the top eq.
  have hTopEq : __eo_typeof (ufGeqElimConclusion x n w) =
      __eo_typeof_eq (__eo_typeof (ufGeqElimLhs x n))
        (__eo_typeof (ufGeqElimRhs x n w)) := by
    rfl
  rw [hTopEq] at hTy
  -- Both sides have the same type.
  have hSameTy :
      __eo_typeof (ufGeqElimRhs x n w) = __eo_typeof (ufGeqElimLhs x n) :=
    typeof_eq_bool_inv _ _ hTy
  -- The LHS type computes to `__eo_typeof_lt (bvsize (typeof x)) (typeof n)`.
  have hLhsTy : __eo_typeof (ufGeqElimLhs x n) =
      __eo_typeof_lt (__eo_typeof__at_bvsize (__eo_typeof x)) (__eo_typeof n) := by
    rfl
  -- The LHS type is `Bool` or `Stuck`; if `Stuck`, the eq result would be `Stuck`.
  have hLhsBool : __eo_typeof (ufGeqElimLhs x n) = Term.Bool := by
    rcases typeof_lt_bool_or_stuck
        (__eo_typeof__at_bvsize (__eo_typeof x)) (__eo_typeof n) with hB | hS
    · rw [hLhsTy]; exact hB
    · exfalso
      have hStuck : __eo_typeof (ufGeqElimLhs x n) = Term.Stuck := by
        rw [hLhsTy]; exact hS
      rw [hStuck] at hTy
      simp [__eo_typeof_eq] at hTy
  -- From lhs = Bool, invert the lt to get x : BitVec _, n : Int.
  rw [hLhsTy] at hLhsBool
  rcases typeof_lt_bool_inv _ _ hLhsBool with ⟨hBA, hArith⟩
  -- `bvsize (typeof x)` is `Int` or `Stuck`; the arith branch rules out `Real`.
  have hBvsizeInt : __eo_typeof__at_bvsize (__eo_typeof x) = Term.UOp UserOp.Int := by
    rcases hArith with hI | hR
    · exact hI
    · exfalso
      revert hR
      cases hxc : __eo_typeof x with
      | Apply f m =>
          cases f with
          | UOp op => cases op <;> simp [__eo_typeof__at_bvsize]
          | _ => simp [__eo_typeof__at_bvsize]
      | _ => simp [__eo_typeof__at_bvsize]
  -- `typeof n = bvsize (typeof x) = Int`.
  have hnInt : __eo_typeof n = Term.UOp UserOp.Int := by
    rw [hBA, hBvsizeInt]
  -- `bvsize (typeof x) = Int` ⟹ typeof x is a BitVec.
  have hxBv : ∃ m, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) m := by
    revert hBvsizeInt
    cases hxc : __eo_typeof x with
    | Apply f m =>
        cases f with
        | UOp op =>
            cases op <;> intro hBvsizeInt <;>
              simp_all [__eo_typeof__at_bvsize] <;>
              (first | (exact ⟨m, rfl⟩) | (simp_all [__eo_typeof__at_bvsize]))
        | _ => intro hBvsizeInt; simp_all [__eo_typeof__at_bvsize]
    | _ => intro hBvsizeInt; simp_all [__eo_typeof__at_bvsize]
  rcases hxBv with ⟨m, hxBvm⟩
  -- Now use the RHS = Bool to pin down `w = Numeral k` and `m = Numeral k`.
  have hRhsBool : __eo_typeof (ufGeqElimRhs x n w) = Term.Bool := by
    rw [hSameTy]; rw [hLhsTy]; exact hLhsBool
  -- Invert the outer ite.
  have hRhsForm : __eo_typeof (ufGeqElimRhs x n w) =
      __eo_typeof_ite
        (__eo_typeof (geqTerm n (int_pow2Term w)))
        (__eo_typeof (Term.Boolean false))
        (__eo_typeof (iteTerm (ltTerm n (Term.Numeral 0)) (Term.Boolean true)
          (bvugeTerm x (intToBvTerm w n)))) := by
    rfl
  rw [hRhsForm] at hRhsBool
  -- The ite requires its condition to be Bool; otherwise the ite is Stuck.
  have hGuardBool :
      __eo_typeof (geqTerm n (int_pow2Term w)) = Term.Bool :=
    typeof_ite_guard_bool _ _ _ hRhsBool
  rw [hGuardBool] at hRhsBool
  -- typeof (Boolean false) = Bool, so ite reduces and forces the inner ite = Bool.
  have hBoolFalse : __eo_typeof (Term.Boolean false) = Term.Bool := rfl
  rw [hBoolFalse] at hRhsBool
  rcases typeof_ite_bool_inv _ _ hRhsBool with ⟨_hBoolFalse2, hInnerBool⟩
  -- Invert the inner ite.
  have hInnerForm :
      __eo_typeof (iteTerm (ltTerm n (Term.Numeral 0)) (Term.Boolean true)
          (bvugeTerm x (intToBvTerm w n))) =
        __eo_typeof_ite
          (__eo_typeof (ltTerm n (Term.Numeral 0)))
          (__eo_typeof (Term.Boolean true))
          (__eo_typeof (bvugeTerm x (intToBvTerm w n))) := by
    rfl
  rw [hInnerForm] at hInnerBool
  have hGuard2Bool :
      __eo_typeof (ltTerm n (Term.Numeral 0)) = Term.Bool :=
    typeof_ite_guard_bool _ _ _ hInnerBool
  rw [hGuard2Bool] at hInnerBool
  have hBoolTrue : __eo_typeof (Term.Boolean true) = Term.Bool := rfl
  rw [hBoolTrue] at hInnerBool
  rcases typeof_ite_bool_inv _ _ hInnerBool with ⟨_hBoolTrue2, hBvugeBool⟩
  -- Invert the bvuge.
  have hBvugeForm : __eo_typeof (bvugeTerm x (intToBvTerm w n)) =
      __eo_typeof_bvult (__eo_typeof x) (__eo_typeof (intToBvTerm w n)) := by
    rfl
  rw [hBvugeForm] at hBvugeBool
  rcases typeof_bvult_bool_inv _ _ hBvugeBool with ⟨mm, hxMm, hIntToBvMm⟩
  -- `intToBvTerm w n` has type computed by `__eo_typeof_int_to_bv`.
  have hIntToBvForm : __eo_typeof (intToBvTerm w n) =
      __eo_typeof_int_to_bv (__eo_typeof w) w (__eo_typeof n) := by
    rfl
  rw [hIntToBvForm, hnInt] at hIntToBvMm
  rcases int_to_bv_type_bitvec_inv (__eo_typeof w) w mm hIntToBvMm with
    ⟨_hWTyInt, k, hwk, hPosk, hmmk⟩
  -- Now: typeof x = BitVec mm (from hxMm), and mm = Numeral k.
  subst hmmk
  -- So typeof x = BitVec (Numeral k).
  have hxFinal : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec)
      (Term.Numeral k) := hxMm
  -- Nonnegativity of k from `-1 < k`.
  have hNonneg : native_zleq 0 k = true := by
    have hLt' : (-1 : native_Int) < k := by
      simpa [native_zlt, SmtEval.native_zlt] using hPosk
    have hStep : (-1 : native_Int) + 1 <= k := (Int.add_one_le_iff).2 hLt'
    have : (0 : native_Int) <= k := by simpa using hStep
    simpa [native_zleq, SmtEval.native_zleq] using this
  exact ⟨k, hwk, hNonneg, hxFinal, hnInt⟩

/-! ## SMT typing of `x` -/

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 w : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ k, w = Term.Numeral k ∧ native_zleq 0 k = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat k) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x1) rfl
      hX1Trans hX1Type
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral k =>
    cases hNonneg : native_zleq 0 k <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hX1Trans hSmtType)
    · exact ⟨k, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hX1Trans hSmtType)

/-! ## Semantic crux: the two sides evaluate to the same Boolean. -/

private theorem eval_lhs_matches_rhs
    (M : SmtModel) (hM : model_wf M) (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    __eo_typeof (ufGeqElimConclusion x n w) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (ufGeqElimLhs x n)) =
      __smtx_model_eval M (__eo_to_smt (ufGeqElimRhs x n w)) := by
  intro hXTrans hNTrans hResultTy
  rcases typeof_args_of_conclusion_bool x n w hResultTy with
    ⟨k, hWk, hNonneg, hxTy, hnTy⟩
  subst hWk
  -- SMT type of `x` is a BitVec of width k.
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x (Term.Numeral k) hXTrans hxTy
    with ⟨k', hkk, _hNonneg', hxSmtTy⟩
  injection hkk with hkk'
  subst hkk'
  -- Evaluate `x` to a canonical `Binary k a`.
  have hEvalXTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat k) := by
    simpa [hxSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hXTrans)
  rcases bitvec_value_canonical hEvalXTy with ⟨a, hEvalX⟩
  -- width as int.
  have hWidthInt : native_nat_to_int (native_int_to_nat k) = k := by
    have hnNonneg : 0 <= k := by simpa [SmtEval.native_zleq] using hNonneg
    have hInt : (Int.ofNat (Int.toNat k) : Int) = k := Int.toNat_of_nonneg hnNonneg
    simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  rw [hWidthInt] at hEvalX
  -- canonicity payload in range.
  have hCanon :
      native_zeq a (native_mod_total a (native_int_pow2 k)) = true :=
    bitvec_payload_canonical (u := native_int_to_nat k)
      (by rw [hEvalX] at hEvalXTy; exact hEvalXTy)
  have hRange : 0 <= a ∧ a < native_int_pow2 k :=
    bitvec_payload_range_of_canonical hNonneg hCanon
  obtain ⟨hRange0, hRangeLt⟩ := hRange
  -- `n` evaluates to a Numeral.
  have hEvalNTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    have hnSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
      have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hnTy
      simpa [__eo_to_smt_type] using this
    simpa [hnSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hNTrans)
  rcases int_value_canonical hEvalNTy with ⟨nv, hEvalN⟩
  -- Now evaluate both sides.
  -- LHS = geq (ubv_to_int x) n
  have hLhsToSmt : __eo_to_smt (ufGeqElimLhs x n) =
      SmtTerm.geq (SmtTerm.ubv_to_int (__eo_to_smt x)) (__eo_to_smt n) := by rfl
  have hRhsToSmt : __eo_to_smt (ufGeqElimRhs x n (Term.Numeral k)) =
      SmtTerm.ite
        (SmtTerm.geq (__eo_to_smt n) (SmtTerm.int_pow2 (SmtTerm.Numeral k)))
        (SmtTerm.Boolean false)
        (SmtTerm.ite
          (SmtTerm.lt (__eo_to_smt n) (SmtTerm.Numeral 0))
          (SmtTerm.Boolean true)
          (SmtTerm.bvuge (__eo_to_smt x)
            (SmtTerm.int_to_bv (SmtTerm.Numeral k) (__eo_to_smt n)))) := by rfl
  rw [hLhsToSmt, hRhsToSmt]
  -- evaluate LHS.
  rw [smtx_eval_geq_term_eq, smtx_eval_ubv_to_int_term_eq, hEvalX, hEvalN]
  simp only [__smtx_model_eval_ubv_to_int]
  -- LHS value = geq (Numeral a) (Numeral nv) = leq nv a = Boolean (zleq nv a)
  have hLhsVal :
      __smtx_model_eval_geq (SmtValue.Numeral a) (SmtValue.Numeral nv) =
        SmtValue.Boolean (native_zleq nv a) := by
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq]
  rw [hLhsVal]
  -- evaluate RHS.
  rw [smtx_eval_ite_term_eq, smtx_eval_geq_term_eq, smtx_eval_int_pow2_term_eq,
    hEvalN]
  have hPow : __smtx_model_eval M (SmtTerm.Numeral k) = SmtValue.Numeral k := by
    rw [__smtx_model_eval.eq_2]
  rw [hPow]
  simp only [__smtx_model_eval_int_pow2]
  have hGuard1 :
      __smtx_model_eval_geq (SmtValue.Numeral nv)
          (SmtValue.Numeral (native_int_pow2 k)) =
        SmtValue.Boolean (native_zleq (native_int_pow2 k) nv) := by
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq]
  rw [hGuard1]
  -- case split on guard1
  by_cases hG1 : native_zleq (native_int_pow2 k) nv = true
  · -- 2^k <= nv ⟹ a < 2^k <= nv ⟹ ¬ nv <= a ⟹ zleq nv a = false
    rw [hG1]
    simp only [__smtx_model_eval_ite]
    rw [smtx_eval_boolean_term_eq]
    have hle : native_int_pow2 k <= nv := by simpa [SmtEval.native_zleq] using hG1
    have : native_zleq nv a = false := by
      have : ¬ (nv <= a) := by simp only [native_Int] at *; omega
      simpa [SmtEval.native_zleq] using this
    rw [this]
  · -- nv < 2^k
    have hG1f : native_zleq (native_int_pow2 k) nv = false := by
      cases h : native_zleq (native_int_pow2 k) nv
      · rfl
      · exact absurd h hG1
    rw [hG1f]
    simp only [__smtx_model_eval_ite]
    have hltPow : nv < native_int_pow2 k := by
      have hnle : ¬ (native_int_pow2 k <= nv) := by
        intro hc; exact hG1 (by simpa [SmtEval.native_zleq] using hc)
      simp only [native_Int] at *; omega
    -- evaluate inner guard2 = lt n 0
    rw [smtx_eval_ite_term_eq, smtx_eval_lt_term_eq, hEvalN]
    have hZero : __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
      rw [__smtx_model_eval.eq_2]
    rw [hZero]
    have hGuard2 :
        __smtx_model_eval_lt (SmtValue.Numeral nv) (SmtValue.Numeral 0) =
          SmtValue.Boolean (native_zlt nv 0) := by
      simp [__smtx_model_eval_lt]
    rw [hGuard2]
    by_cases hG2 : native_zlt nv 0 = true
    · -- nv < 0 ≤ a ⟹ nv <= a ⟹ zleq nv a = true
      rw [hG2]
      simp only [__smtx_model_eval_ite]
      rw [smtx_eval_boolean_term_eq]
      have hlt0 : nv < 0 := by simpa [SmtEval.native_zlt] using hG2
      have : native_zleq nv a = true := by
        have : nv <= a := by simp only [native_Int] at *; omega
        simpa [SmtEval.native_zleq] using this
      rw [this]
    · -- 0 <= nv < 2^k ⟹ bvuge x (int_to_bv k n)
      have hG2f : native_zlt nv 0 = false := by
        cases h : native_zlt nv 0
        · rfl
        · exact absurd h hG2
      rw [hG2f]
      simp only [__smtx_model_eval_ite]
      have hnv0 : 0 <= nv := by
        have hnlt : ¬ (nv < 0) := by
          intro hc; exact hG2 (by simpa [SmtEval.native_zlt] using hc)
        simp only [native_Int] at *; omega
      -- evaluate bvuge x (int_to_bv k n)
      rw [smtx_eval_bvuge_term_eq, smtx_eval_int_to_bv_term_eq, hEvalX, hEvalN,
        hPow]
      simp only [__smtx_model_eval_int_to_bv]
      -- int_to_bv k nv = Binary k (mod nv 2^k) = Binary k nv (since 0<=nv<2^k)
      have hMod : native_mod_total nv (native_int_pow2 k) = nv := by
        simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hnv0 hltPow
      rw [hMod]
      -- bvuge (Binary k a) (Binary k nv)
      have hBvuge :
          __smtx_model_eval_bvuge (SmtValue.Binary k a) (SmtValue.Binary k nv) =
            SmtValue.Boolean (native_zleq nv a) := by
        simp only [__smtx_model_eval_bvuge, __smtx_model_eval_bvugt,
          __smtx_model_eval_eq, __smtx_model_eval_or]
        -- or (zlt nv a) (veq (Binary k a) (Binary k nv)) = zleq nv a
        have hVeq : native_veq (SmtValue.Binary k a) (SmtValue.Binary k nv) =
            decide (a = nv) := by
          simp only [native_veq, SmtValue.Binary.injEq, true_and]
        rw [hVeq]
        congr 1
        simp only [SmtEval.native_or, SmtEval.native_zlt, SmtEval.native_zleq]
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        simp only [native_Int] at *
        omega
      rw [hBvuge]

/-! ## Bool-typedness and interpretation of the conclusion -/

private theorem facts_conclusion_impl
    (M : SmtModel) (hM : model_wf M) (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    __eo_typeof (ufGeqElimConclusion x n w) = Term.Bool ->
    eo_interprets M (ufGeqElimConclusion x n w) true := by
  intro hXTrans hNTrans hResultTy
  -- Bool-typedness of the eq comes from equal smt types of both sides.
  -- We obtain it by showing both sides evaluate equal (rel) and have the
  -- same smt type via the eq inversion machinery.
  -- Use `eo_interprets_eq_of_rel`, which needs bool-typedness; derive that from
  -- the smt types of both operands.
  -- The two operands have the SAME smt type because they evaluate to equal
  -- values of Bool type. We compute their smt types directly.
  have hLhsSmtTy : __smtx_typeof (__eo_to_smt (ufGeqElimLhs x n)) = SmtType.Bool := by
    rcases typeof_args_of_conclusion_bool x n w hResultTy with
      ⟨k, hWk, hNonneg, hxTy, hnTy⟩
    rcases smt_bitvec_type_of_eo_bitvec_type_with_width x (Term.Numeral k) hXTrans hxTy
      with ⟨k', hkk, _hNonneg', hxSmtTy⟩
    have hnSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
      have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hnTy
      simpa [__eo_to_smt_type] using this
    have hToSmt : __eo_to_smt (ufGeqElimLhs x n) =
        SmtTerm.geq (SmtTerm.ubv_to_int (__eo_to_smt x)) (__eo_to_smt n) := by rfl
    rw [hToSmt, smtx_typeof_geq_term_eq, smtx_typeof_ubv_to_int_term_eq,
      hxSmtTy, hnSmtTy]
    simp [__smtx_typeof_bv_op_1_ret, __smtx_typeof_arith_overload_op_2_ret]
  have hRhsSmtTy : __smtx_typeof (__eo_to_smt (ufGeqElimRhs x n w)) = SmtType.Bool := by
    rcases typeof_args_of_conclusion_bool x n w hResultTy with
      ⟨k, hWk, hNonneg, hxTy, hnTy⟩
    subst hWk
    rcases smt_bitvec_type_of_eo_bitvec_type_with_width x (Term.Numeral k) hXTrans hxTy
      with ⟨k', hkk, _hNonneg', hxSmtTy⟩
    injection hkk with hkk'
    subst hkk'
    have hnSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
      have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hnTy
      simpa [__eo_to_smt_type] using this
    have hToSmt : __eo_to_smt (ufGeqElimRhs x n (Term.Numeral k)) =
        SmtTerm.ite
          (SmtTerm.geq (__eo_to_smt n) (SmtTerm.int_pow2 (SmtTerm.Numeral k)))
          (SmtTerm.Boolean false)
          (SmtTerm.ite
            (SmtTerm.lt (__eo_to_smt n) (SmtTerm.Numeral 0))
            (SmtTerm.Boolean true)
            (SmtTerm.bvuge (__eo_to_smt x)
              (SmtTerm.int_to_bv (SmtTerm.Numeral k) (__eo_to_smt n)))) := by rfl
    rw [hToSmt]
    rw [smtx_typeof_ite_term_eq, smtx_typeof_geq_term_eq, smtx_typeof_int_pow2_term_eq,
      smtx_typeof_ite_term_eq, smtx_typeof_lt_term_eq, smtx_typeof_bvuge_term_eq,
      smtx_typeof_int_to_bv_term_eq]
    rw [hnSmtTy, hxSmtTy]
    have hNumTy : __smtx_typeof (SmtTerm.Numeral k) = SmtType.Int := by
      rw [__smtx_typeof.eq_2]
    have hNum0Ty : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
      rw [__smtx_typeof.eq_2]
    rw [hNumTy, hNum0Ty]
    have hBoolFalseTy : __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool := by
      rw [__smtx_typeof.eq_def] <;> simp only
    have hBoolTrueTy : __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool := by
      rw [__smtx_typeof.eq_def] <;> simp only
    rw [hBoolFalseTy, hBoolTrueTy]
    have hNonnegK : native_zleq 0 k = true := hNonneg
    simp [__smtx_typeof_int_to_bv, __smtx_typeof_arith_overload_op_2_ret,
      __smtx_typeof_bv_op_2_ret, __smtx_typeof_ite, __smtx_typeof_bv_op_1_ret,
      native_ite, native_Teq, native_nateq, hNonnegK]
  have hSameSmtTy :
      __smtx_typeof (__eo_to_smt (ufGeqElimLhs x n)) =
        __smtx_typeof (__eo_to_smt (ufGeqElimRhs x n w)) := by
    rw [hLhsSmtTy, hRhsSmtTy]
  have hBoolType : RuleProofs.eo_has_bool_type (ufGeqElimConclusion x n w) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (ufGeqElimLhs x n) (ufGeqElimRhs x n w) hSameSmtTy
      (by rw [hLhsSmtTy]; intro hc; cases hc)
  apply RuleProofs.eo_interprets_eq_of_rel M
    (ufGeqElimLhs x n) (ufGeqElimRhs x n w) hBoolType
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt (ufGeqElimLhs x n)))
    (__smtx_model_eval M (__eo_to_smt (ufGeqElimRhs x n w)))
  rw [eval_lhs_matches_rhs M hM x n w hXTrans hNTrans hResultTy]
  exact RuleProofs.smt_value_rel_refl _

private theorem typed_conclusion_impl
    (M : SmtModel) (hM : model_wf M) (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    __eo_typeof (ufGeqElimConclusion x n w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (ufGeqElimConclusion x n w) :=
  fun hX hN hTy =>
    RuleProofs.eo_has_bool_type_of_interprets_true M (ufGeqElimConclusion x n w)
      (facts_conclusion_impl M hM x n w hX hN hTy)

/-! ## Top-level dispatch -/

public theorem cmd_step_uf_bv2nat_geq_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_geq_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_bv2nat_geq_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_geq_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.uf_bv2nat_geq_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n1 premises =>
                      cases premises with
                      | nil =>
                          let P1 := __eo_state_proven_nth s n1
                          have hATransPair :
                              RuleProofs.eo_has_smt_translation a1 ∧
                                RuleProofs.eo_has_smt_translation a2 ∧
                                RuleProofs.eo_has_smt_translation a3 ∧ True := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                            hATransPair.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                            hATransPair.2.1
                          change __eo_typeof
                              (__eo_prog_uf_bv2nat_geq_elim a1 a2 a3 (Proof.pf P1)) =
                            Term.Bool at hResultTy
                          have hProgArg :
                              __eo_prog_uf_bv2nat_geq_elim a1 a2 a3 (Proof.pf P1)
                                ≠ Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          obtain ⟨hA1NS, hA2NS, hA3NS⟩ :=
                            args_ne_stuck_of_prog_not_stuck a1 a2 a3 P1 hProgArg
                          rcases shape_of_prog_uf_bv2nat_geq_elim_not_stuck a1 a2 a3 P1
                            hA1NS hA2NS hA3NS hProgArg with ⟨lw, lx, hP1⟩
                          rw [hP1] at hProgArg hResultTy
                          have hProgEq :
                              __eo_prog_uf_bv2nat_geq_elim a1 a2 a3
                                (Proof.pf
                                  (Term.Apply
                                    (Term.Apply (Term.UOp UserOp.eq) lw)
                                    (Term.Apply (Term.UOp UserOp._at_bvsize) lx))) =
                                __eo_requires (__eo_and (__eo_eq a3 lw) (__eo_eq a1 lx))
                                  (Term.Boolean true) (ufGeqElimConclusion a1 a2 a3) :=
                            prog_uf_bv2nat_geq_elim_eq a1 a2 a3 lw lx hA1NS hA2NS hA3NS
                          rw [hProgEq] at hProgArg hResultTy
                          have hAlign : lw = a3 ∧ lx = a1 :=
                            eqs_of_requires_and_eq_true_not_stuck a3 a1 lw lx
                              (ufGeqElimConclusion a1 a2 a3) hProgArg
                          obtain ⟨hLw, hLx⟩ := hAlign
                          subst lw
                          subst lx
                          rw [requires_and_eq_self_true_body a3 a1
                            (ufGeqElimConclusion a1 a2 a3) hA3NS hA1NS]
                            at hResultTy
                          have hStepEq :
                              __eo_cmd_step_proven s CRule.uf_bv2nat_geq_elim
                                  (CArgList.cons a1 (CArgList.cons a2
                                    (CArgList.cons a3 CArgList.nil)))
                                  (CIndexList.cons n1 CIndexList.nil) =
                                ufGeqElimConclusion a1 a2 a3 := by
                            change __eo_prog_uf_bv2nat_geq_elim a1 a2 a3 (Proof.pf P1) =
                              ufGeqElimConclusion a1 a2 a3
                            rw [hP1, hProgEq,
                              requires_and_eq_self_true_body a3 a1
                                (ufGeqElimConclusion a1 a2 a3) hA3NS hA1NS]
                          rw [hStepEq]
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            exact facts_conclusion_impl M hM a1 a2 a3
                              hA1Trans hA2Trans hResultTy
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed_conclusion_impl M hM a1 a2 a3
                                hA1Trans hA2Trans hResultTy)
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
