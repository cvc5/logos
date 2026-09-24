module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000

/-! ## Term abbreviations -/

private abbrev sbvToIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.sbv_to_int) t

private abbrev ubvToIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.ubv_to_int) t

private abbrev extractTerm (hi lo t : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract hi lo) t

private abbrev bvOneZeroTerm : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)

private abbrev negTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y

private abbrev eqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev iteTerm (c a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b

private abbrev bvsizeTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_bvsize) t

private abbrev intPow2Term (w : Term) : Term :=
  Term.Apply (Term.UOp UserOp.int_pow2) w

/-- The body of the rule's conclusion (the equation proven by the rule). -/
private abbrev ufSbvToIntElimBody (t wm n : Term) : Term :=
  eqTerm (sbvToIntTerm t)
    (iteTerm (eqTerm (extractTerm wm wm t) bvOneZeroTerm)
      (ubvToIntTerm t)
      (negTerm (ubvToIntTerm t) n))

/-! ## Program reduction and guard handling -/

/-- When all args are non-stuck and both premises have the expected shape, the
    program reduces to the requires-guarded conclusion. -/
private theorem prog_uf_sbv_to_int_elim_eq
    (t wm n wm2 t2 n2 t3 : Term)
    (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck) (hN : n ≠ Term.Stuck) :
    __eo_prog_uf_sbv_to_int_elim t wm n
      (Proof.pf (eqTerm wm2 (negTerm (bvsizeTerm t2) (Term.Numeral 1))))
      (Proof.pf (eqTerm n2 (intPow2Term (bvsizeTerm t3)))) =
      __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq wm wm2) (__eo_eq t t2)) (__eo_eq n n2))
          (__eo_eq t t3))
        (Term.Boolean true) (ufSbvToIntElimBody t wm n) := by
  unfold __eo_prog_uf_sbv_to_int_elim
  split
  · exact absurd rfl hT
  · exact absurd rfl hWm
  · exact absurd rfl hN
  · rename_i heq1 heq2
    injection heq1 with heq1
    injection heq2 with heq2
    simp only [eqTerm, negTerm, bvsizeTerm, intPow2Term,
      Term.Apply.injEq, true_and, and_true] at heq1 heq2
    obtain ⟨hwm2, ht2⟩ := heq1
    obtain ⟨hn2, ht3⟩ := heq2
    subst hwm2; subst ht2; subst hn2; subst ht3
    rfl
  · rename_i hcontra
    exact (hcontra wm2 t2 n2 t3 rfl rfl).elim

/-- A non-stuck program forces all three args to be non-stuck. -/
private theorem args_ne_stuck_of_prog_not_stuck
    (t wm n p1 p2 : Term)
    (h : __eo_prog_uf_sbv_to_int_elim t wm n (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    t ≠ Term.Stuck ∧ wm ≠ Term.Stuck ∧ n ≠ Term.Stuck := by
  refine ⟨?_, ?_, ?_⟩
  · intro hT; subst t; simp [__eo_prog_uf_sbv_to_int_elim] at h
  · intro hWm; subst wm; cases t <;> simp [__eo_prog_uf_sbv_to_int_elim] at h
  · intro hN; subst n
    cases t <;> cases wm <;> simp [__eo_prog_uf_sbv_to_int_elim] at h

/-- A non-stuck program forces both premises to be equalities of the expected
    shape. -/
private theorem shape_of_prog_uf_sbv_to_int_elim_not_stuck
    (t wm n p1 p2 : Term)
    (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck) (hN : n ≠ Term.Stuck)
    (h : __eo_prog_uf_sbv_to_int_elim t wm n (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    ∃ wm2 t2 n2 t3 : Term,
      p1 = eqTerm wm2 (negTerm (bvsizeTerm t2) (Term.Numeral 1)) ∧
      p2 = eqTerm n2 (intPow2Term (bvsizeTerm t3)) := by
  unfold __eo_prog_uf_sbv_to_int_elim at h
  split at h
  · exact absurd rfl hT
  · exact absurd rfl hWm
  · exact absurd rfl hN
  · rename_i lwm lt2 ln lt3 _ _ _ heq1 heq2
    injection heq1 with heq1
    injection heq2 with heq2
    exact ⟨lwm, lt2, ln, lt3, heq1, heq2⟩
  · exact absurd rfl h

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x; simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y; simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

/-- Stuck-or-Boolean dichotomy for `__eo_eq`. -/
private theorem eo_eq_stuck_or_bool (a b : Term) :
    __eo_eq a b = Term.Stuck ∨
      ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
  by_cases ha : a = Term.Stuck
  · subst a; exact Or.inl (by simp [__eo_eq])
  · by_cases hb : b = Term.Stuck
    · subst b; exact Or.inl (by simp [__eo_eq])
    · exact Or.inr ⟨native_teq b a, by simp [__eo_eq]⟩

/-- From the four-way conjunction guard being non-stuck, recover the four
    equalities. -/
private theorem eqs_of_requires_and4_eq_true_not_stuck
    (x1 x2 y1 y2 z1 z2 w1 w2 B : Term) :
    __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2)) (__eo_eq z1 z2))
          (__eo_eq w1 w2))
        (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 ∧ z2 = z1 ∧ w2 = w1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd :
      __eo_and
        (__eo_and (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2)) (__eo_eq z1 z2))
        (__eo_eq w1 w2) = Term.Boolean true := hProg'.1
  -- Each leaf must be `Boolean true`.
  rcases eo_eq_stuck_or_bool x1 x2 with hX | ⟨bx, hX⟩
  · simp [__eo_and, hX] at hAnd
  rcases eo_eq_stuck_or_bool y1 y2 with hY | ⟨by1, hY⟩
  · simp [__eo_and, hX, hY] at hAnd
  rcases eo_eq_stuck_or_bool z1 z2 with hZ | ⟨bz, hZ⟩
  · simp [__eo_and, hX, hY, hZ] at hAnd
  rcases eo_eq_stuck_or_bool w1 w2 with hW | ⟨bw, hW⟩
  · simp [__eo_and, hX, hY, hZ, hW] at hAnd
  cases bx <;> cases by1 <;> cases bz <;> cases bw <;>
    simp [__eo_and, hX, hY, hZ, hW, native_and] at hAnd
  exact ⟨eq_of_eo_eq_true x1 x2 hX, eq_of_eo_eq_true y1 y2 hY,
    eq_of_eo_eq_true z1 z2 hZ, eq_of_eo_eq_true w1 w2 hW⟩

/-- Discharge the guard when all leaves are reflexive. -/
private theorem requires_and4_eq_self_true_body
    (t wm n body : Term)
    (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck) (hN : n ≠ Term.Stuck) :
    __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq wm wm) (__eo_eq t t)) (__eo_eq n n))
          (__eo_eq t t))
        (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and,
    eo_eq_self_true_of_ne_stuck wm hWm, eo_eq_self_true_of_ne_stuck t hT,
    eo_eq_self_true_of_ne_stuck n hN, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

/-! ## SMT-level facts -/

/-- Stable rewrite for typing SMT signed bit-vector-to-int terms. -/
private theorem smtx_typeof_sbv_to_int_term_eq (x : SmtTerm) :
    __smtx_typeof (SmtTerm.sbv_to_int x) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof x) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- From an EO bit-vector type with a numeral width, get the SMT type. -/
private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 : Term) (w : native_Int) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    native_zleq 0 w = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat w) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type
          (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
      (__eo_to_smt x1) rfl hX1Trans hX1Type
  cases hNonneg : native_zleq 0 w <;>
    simp [__eo_to_smt_type, hNonneg] at hSmtType
  · exact False.elim (hX1Trans hSmtType)
  · exact ⟨rfl, hSmtType⟩

/-- From `eval_eq (Numeral a) (Numeral b) = Boolean true`, conclude `a = b`. -/
private theorem smtx_model_eval_eq_true_iff_numeral {a b : native_Int}
    (h : __smtx_model_eval_eq (SmtValue.Numeral a) (SmtValue.Numeral b) =
      SmtValue.Boolean true) : a = b := by
  have := (RuleProofs.smt_value_rel_iff_eq (SmtValue.Numeral a) (SmtValue.Numeral b)
    (by rintro ⟨r1, r2, hc, _⟩; cases hc)).1 h
  injection this

/-! ## The crux arithmetic: `native_binary_uts` versus the sign bit -/

private theorem native_int_pow2_pos_of_nonneg
    {w : native_Int} (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

private theorem native_int_pow2_succ_pred
    {w : native_Int} (hwpos : 0 < w) :
    native_int_pow2 w = 2 * native_int_pow2 (w - 1) := by
  have hw0 : 0 <= w := Int.le_of_lt hwpos
  have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
  have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
  have hnotW : ¬ w < 0 := Int.not_lt_of_ge hw0
  have hnotP : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
  have hNat : w.toNat = (w - 1).toNat + 1 := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.natCast_one]
    rw [Int.toNat_of_nonneg hw0, Int.toNat_of_nonneg hwp0]
    omega
  rw [native_int_pow2, native_int_pow2, native_zexp_total, native_zexp_total]
  simp [hnotW, hnotP]
  rw [hNat]
  have hSub : (w - 1).toNat + 1 - 1 = (w - 1).toNat :=
    Nat.add_sub_cancel (w - 1).toNat 1
  rw [hSub]
  rw [← Nat.succ_eq_add_one]
  rw [Int.pow_succ]
  rw [Int.mul_comm]

/--
The key arithmetic lemma.  For a payload `n` canonical for width `w` (so
`0 <= n < 2^w`), let `q := n / 2^(w-1)` be the sign bit.  Then:
* `q = 0` exactly when `native_binary_uts w n = n`, and
* `q = 1` exactly when `native_binary_uts w n = n - 2^w`.

We return the value of `q` together with both arithmetic identities.
-/
private theorem sign_bit_and_uts_of_canonical
    {w n : native_Int}
    (hwpos : 0 < w)
    (hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    (native_div_total n (native_int_pow2 (w - 1)) = 0 ∧
        native_binary_uts w n = n) ∨
      (native_div_total n (native_int_pow2 (w - 1)) = 1 ∧
        native_binary_uts w n = n - native_int_pow2 w) := by
  have hw0 : native_zleq 0 w = true := by
    have : 0 <= w := Int.le_of_lt hwpos
    simpa [native_zleq, SmtEval.native_zleq] using this
  let p := native_int_pow2 (w - 1)
  let q := native_div_total n p
  let r := native_mod_total n p
  have hpPos : 0 < p := by
    have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
    have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
    exact native_int_pow2_pos_of_nonneg hwp0
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hPow : native_int_pow2 w = 2 * p := by
    simpa [p] using native_int_pow2_succ_pred (w := w) hwpos
  have hqNonneg : 0 <= q := Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
  have hqLt2 : q < 2 := by
    have hlt : n < 2 * p := by simpa [hPow] using hRange.2
    exact Int.ediv_lt_of_lt_mul hpPos hlt
  have hqCases : q = 0 ∨ q = 1 := by
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · have hqPos : 0 < q := by
        rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
        · exact hlt
        · exact False.elim (hq0 heq.symm)
      have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
      have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
      exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
  have hDivMod : p * q + r = n := by
    simpa [q, r, p, native_div_total, native_mod_total] using
      Int.mul_ediv_add_emod n p
  have hRRange : 0 <= r ∧ r < p := by
    constructor
    · simpa [r, native_mod_total] using Int.emod_nonneg n (Int.ne_of_gt hpPos)
    · simpa [r, native_mod_total] using Int.emod_lt_of_pos n hpPos
  have hRMod : native_mod_total r p = r := by
    simpa [native_mod_total] using Int.emod_eq_of_lt hRRange.1 hRRange.2
  rcases hqCases with hq | hq
  · -- sign bit 0: uts = n
    refine Or.inl ⟨hq, ?_⟩
    have hnEq : n = r := by
      rw [hq] at hDivMod; simp at hDivMod; exact hDivMod.symm
    rw [native_binary_uts]
    change native_zplus (native_zmult 2 (native_mod_total n p)) (native_zneg n) = n
    rw [hnEq]
    change native_zplus (native_zmult 2 (native_mod_total r p)) (native_zneg r) = r
    rw [hRMod]
    have key : ∀ x : native_Int, native_zplus (native_zmult 2 x) (native_zneg x) = x := by
      intro x; simp only [native_zplus, native_zmult, native_zneg, native_Int]; omega
    exact key r
  · -- sign bit 1: uts = n - 2^w
    refine Or.inr ⟨hq, ?_⟩
    have hnEq : n = p + r := by
      rw [hq] at hDivMod; simp at hDivMod; exact hDivMod.symm
    have hPAddMod : native_mod_total (p + r) p = r := by
      have hRModInt : r % p = r := by simpa [native_mod_total] using hRMod
      have hPModInt : p % p = 0 := Int.emod_eq_zero_of_dvd ⟨1, by simp⟩
      change (p + r) % p = r
      rw [Int.add_emod, hPModInt, hRModInt]
      simpa using hRModInt
    rw [native_binary_uts]
    change native_zplus (native_zmult 2 (native_mod_total n p)) (native_zneg n)
      = n - native_int_pow2 w
    rw [hnEq, hPAddMod, hPow]
    have key : ∀ x y : native_Int,
        native_zplus (native_zmult 2 x) (native_zneg (y + x)) = (y + x) - 2 * y := by
      intro x y; simp only [native_zplus, native_zmult, native_zneg, native_Int]; omega
    exact key r p

/-- The width-1 extract payload (the sign bit), expressed via `native_div_total`. -/
private theorem extract_sign_bit_payload
    (w n wm : native_Int) :
    native_mod_total
        (native_binary_extract w n wm wm)
        (native_int_pow2 (native_zplus (native_zplus wm 1) (native_zneg wm)))
      = native_mod_total (native_div_total n (native_int_pow2 wm)) 2 := by
  have hExp : native_zplus (native_zplus wm 1) (native_zneg wm) = 1 := by
    simp only [native_zplus, native_zneg, native_Int]
    omega
  rw [hExp]
  have hPow1 : native_int_pow2 (1 : native_Int) = 2 := by decide
  rw [hPow1, native_binary_extract]

/-! ## Typing inversion for the conclusion body -/

/-- Inversion of `__eo_typeof_eq A B = Bool`: both sides equal (and non-stuck). -/
private theorem typeof_eq_bool_inv (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) : B = A := by
  have hNeStuck : __eo_typeof_eq A B ≠ Term.Stuck := by rw [h]; intro hc; cases hc
  by_cases hAStuck : A = Term.Stuck
  · subst A; simp [__eo_typeof_eq] at hNeStuck
  · by_cases hBStuck : B = Term.Stuck
    · subst B; cases A <;> simp [__eo_typeof_eq] at hNeStuck
    · have hReqEq : __eo_typeof_eq A B =
          __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool := by
        cases A <;> cases B <;> simp_all [__eo_typeof_eq]
      rw [hReqEq] at hNeStuck
      have hReq' := hNeStuck
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hReq'
      exact eq_of_eo_eq_true A B hReq'.1

/-- `__eo_typeof_ite Bool A B = T` forces `A = B` and `T = A`. -/
private theorem typeof_ite_inv (A B : Term)
    (h : __eo_typeof_ite Term.Bool A B = Term.UOp UserOp.Int) :
    A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int := by
  by_cases hA : A = Term.Stuck
  · subst A; simp [__eo_typeof_ite] at h
  · by_cases hB : B = Term.Stuck
    · subst B; cases A <;> simp [__eo_typeof_ite] at h
    · have hRed : __eo_typeof_ite Term.Bool A B
          = __eo_requires (__eo_eq A B) (Term.Boolean true) A := by
        cases A <;> cases B <;> simp_all [__eo_typeof_ite]
      rw [hRed] at h
      have hNeStuck : __eo_requires (__eo_eq A B) (Term.Boolean true) A ≠ Term.Stuck := by
        rw [h]; intro hc; cases hc
      have hReq' := hNeStuck
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hReq'
      have hBA : B = A := eq_of_eo_eq_true A B hReq'.1
      subst B
      -- now requires (eq A A) true A reduces to A, and that = Int
      have hAEq : __eo_requires (__eo_eq A A) (Term.Boolean true) A = A := by
        cases A <;> simp [__eo_requires, __eo_eq, native_ite, native_teq,
          native_not, SmtEval.native_not] at hA ⊢
      rw [hAEq] at h
      exact ⟨h, h⟩

/-- `__eo_typeof_plus Int (typeof n) = Int` forces `typeof n = Int`. -/
private theorem typeof_plus_int_inv (B : Term)
    (h : __eo_typeof_plus (Term.UOp UserOp.Int) B = Term.UOp UserOp.Int) :
    B = Term.UOp UserOp.Int := by
  by_cases hB : B = Term.Stuck
  · subst B; simp [__eo_typeof_plus] at h
  · have hRed : __eo_typeof_plus (Term.UOp UserOp.Int) B
        = __eo_requires (__eo_eq (Term.UOp UserOp.Int) B) (Term.Boolean true)
            (__eo_requires (__is_arith_type (Term.UOp UserOp.Int)) (Term.Boolean true)
              (Term.UOp UserOp.Int)) := by
      cases B <;> simp_all [__eo_typeof_plus]
    rw [hRed] at h
    have hNeStuck := by
      show __eo_requires (__eo_eq (Term.UOp UserOp.Int) B) (Term.Boolean true)
          (__eo_requires (__is_arith_type (Term.UOp UserOp.Int)) (Term.Boolean true)
            (Term.UOp UserOp.Int)) ≠ Term.Stuck
      rw [h]; intro hc; cases hc
    have hReq' := hNeStuck
    simp [__eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at hReq'
    exact eq_of_eo_eq_true (Term.UOp UserOp.Int) B hReq'.1

/-- Reduction of the diagonal extract typeof for a numeral `wm` over a `BitVec`
    operand of numeral width. -/
private theorem typeof_extract_diag_numeral (wmv w : native_Int) :
    __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmv)
        (Term.UOp UserOp.Int) (Term.Numeral wmv)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
      = (native_ite (native_zlt (-1 : native_Int) wmv)
          (native_ite (native_zlt wmv w)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_zplus (native_zplus wmv (native_zneg wmv)) 1)))
            Term.Stuck)
          Term.Stuck) := by
  unfold __eo_typeof_extract
  simp only [__eo_mk_apply, __eo_requires, __eo_gt, __eo_add, __eo_neg, native_ite,
    native_teq, native_not, SmtEval.native_not]
  have hLenPos :
      native_zlt 0
          (native_zplus (native_zplus wmv (native_zneg wmv)) 1) = true := by
    have hLen :
        native_zplus (native_zplus wmv (native_zneg wmv)) 1 = 1 := by
      change (wmv + -wmv) + 1 = 1
      rw [Int.add_right_neg]
      rfl
    rw [hLen]
    native_decide
  by_cases hg1 : native_zlt (-1 : native_Int) wmv = true <;>
    by_cases hg2 : native_zlt wmv w = true <;>
    simp [hg1, hg2, hLenPos, native_ite, native_teq]

/-- The `gt wm (-1)` guard is `Stuck` when `wm` is not a numeral. -/
private theorem eo_gt_neg_one_stuck_of_not_numeral (wm : Term)
    (hwm : ∀ k, wm ≠ Term.Numeral k) :
    __eo_gt wm (Term.Numeral (-1 : native_Int)) = Term.Stuck := by
  cases hw : wm with
  | Numeral k => exact absurd hw (hwm k)
  | _ => rfl

/-- `__eo_requires` with a `Stuck` condition is `Stuck`. -/
private theorem requires_stuck_cond (b c : Term) :
    __eo_requires Term.Stuck b c = Term.Stuck := by
  by_cases hb : Term.Stuck = b
  · subst hb
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  · simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not,
      hb]

/-- `__eo_mk_apply` with a `Stuck` right argument is `Stuck`. -/
private theorem mk_apply_stuck_right (x : Term) :
    __eo_mk_apply x Term.Stuck = Term.Stuck := by
  cases x <;> rfl

/-- General reduction: with the `gt wm (-1)` guard `Stuck`, the `Int/Int/BitVec`
    extract arm collapses to `Stuck`; combined with all other arms this gives a
    `Stuck` result whenever that guard is stuck. -/
private theorem typeof_extract_diag_stuck_of_gt_stuck (A wm B : Term)
    (hA : A = Term.UOp UserOp.Int)
    (hgt : __eo_gt wm (Term.Numeral (-1 : native_Int)) = Term.Stuck) :
    __eo_typeof_extract A wm A wm B = Term.Stuck := by
  subst A
  by_cases hwmS : wm = Term.Stuck
  · subst wm; rfl
  · cases hB : B with
    | Apply f a =>
        cases f with
        | UOp o =>
            cases o <;>
              simp only [__eo_typeof_extract, hwmS, hgt, requires_stuck_cond,
                mk_apply_stuck_right]
        | _ => simp only [__eo_typeof_extract, hwmS]
    | _ => simp only [__eo_typeof_extract, hwmS]

/-- The diagonal extract typeof is `Stuck` when `wm` is not a numeral term. -/
private theorem typeof_extract_diag_not_numeral_stuck (wm t : Term)
    (hwm : ∀ k, wm ≠ Term.Numeral k) :
    __eo_typeof_extract (__eo_typeof wm) wm (__eo_typeof wm) wm (__eo_typeof t)
      = Term.Stuck := by
  by_cases hWmTy : __eo_typeof wm = Term.UOp UserOp.Int
  · exact typeof_extract_diag_stuck_of_gt_stuck (__eo_typeof wm) wm (__eo_typeof t)
      hWmTy (eo_gt_neg_one_stuck_of_not_numeral wm hwm)
  · by_cases hwmS : wm = Term.Stuck
    · subst wm
      simp [__eo_typeof_extract]
    · cases hwt : __eo_typeof wm with
      | UOp o => cases o <;> simp_all [__eo_typeof_extract, hwmS]
      | _ => simp_all [__eo_typeof_extract, hwmS]

/-- The diagonal extract typeof for a numeral `wm` over a non-`BitVec(Numeral)`
    operand type is `Stuck`. -/
private theorem typeof_extract_diag_numeral_stuck_of_not_bv
    (wmv : native_Int) (B : Term)
    (hB : ∀ w, B ≠ Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) :
    __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmv)
        (Term.UOp UserOp.Int) (Term.Numeral wmv) B = Term.Stuck := by
  cases hB' : B with
  | Apply f a =>
      cases f with
      | UOp o =>
          by_cases hOBv : o = UserOp.BitVec
          · subst o
            cases ha : a with
            | Numeral w =>
                exfalso
                exact hB w (by rw [hB', ha])
            | _ =>
                simp [__eo_typeof_extract, __eo_mk_apply, __eo_requires,
                  __eo_gt, native_ite, native_teq, native_not,
                  SmtEval.native_not, ha]
          · cases o <;> simp [__eo_typeof_extract] at hOBv ⊢
      | _ => simp only [__eo_typeof_extract]
  | _ => simp only [__eo_typeof_extract]

/-- Inversion of the extract-typeof being a `BitVec`: `wm` is a numeral, the
    operand is a `BitVec (Numeral w)`, with `-1 < wm` and `wm < w`. -/
private theorem typeof_extract_diag_bitvec_inv (wm t : Term) (m : Term)
    (h : __eo_typeof_extract (__eo_typeof wm) wm (__eo_typeof wm) wm (__eo_typeof t)
      = Term.Apply (Term.UOp UserOp.BitVec) m) :
    ∃ wmv w, wm = Term.Numeral wmv ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      native_zlt (-1 : native_Int) wmv = true ∧ native_zlt wmv w = true := by
  by_cases hNum : ∃ k, wm = Term.Numeral k
  · rcases hNum with ⟨wmv, hwm⟩
    subst wm
    rw [show __eo_typeof (Term.Numeral wmv) = Term.UOp UserOp.Int from rfl] at h
    by_cases hBv : ∃ w, __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)
    · rcases hBv with ⟨w, hT⟩
      rw [hT, typeof_extract_diag_numeral] at h
      by_cases hg1 : native_zlt (-1 : native_Int) wmv = true
      · by_cases hg2 : native_zlt wmv w = true
        · exact ⟨wmv, w, rfl, hT, hg1, hg2⟩
        · have hFalse : Term.Stuck = Term.Apply (Term.UOp UserOp.BitVec) m := by
            simpa [native_ite, hg1, hg2] using h
          cases hFalse
      · have hFalse : Term.Stuck = Term.Apply (Term.UOp UserOp.BitVec) m := by
          simpa [native_ite, hg1] using h
        cases hFalse
    · rw [typeof_extract_diag_numeral_stuck_of_not_bv wmv (__eo_typeof t)
        (by intro w hw; exact hBv ⟨w, hw⟩)] at h
      exact absurd h (by simp)
  · exfalso
    rw [typeof_extract_diag_not_numeral_stuck wm t
      (by intro k hk; exact hNum ⟨k, hk⟩)] at h
    exact absurd h (by simp)

/-- `__eo_typeof_ite X A B = Int` forces the condition type `X = Bool`. -/
private theorem typeof_ite_int_forces_bool (X A B : Term)
    (h : __eo_typeof_ite X A B = Term.UOp UserOp.Int) :
    X = Term.Bool := by
  by_cases hA : A = Term.Stuck
  · subst A; simp [__eo_typeof_ite] at h
  · by_cases hB : B = Term.Stuck
    · subst B; cases X <;> cases A <;> simp [__eo_typeof_ite] at h
    · cases hX : X with
      | Bool => rfl
      | _ => simp_all [__eo_typeof_ite]

/-- The `@bv 0 1` constant has EO type `BitVec (Numeral 1)`. -/
private theorem typeof_bv_zero_one :
    __eo_typeof bvOneZeroTerm = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  rfl

/-- From the body's type being `Bool`, recover all the arg-shape facts. -/
private theorem typeof_args_of_body_bool (t wm n : Term) :
    __eo_typeof (ufSbvToIntElimBody t wm n) = Term.Bool ->
    ∃ wmv w,
      wm = Term.Numeral wmv ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      __eo_typeof n = Term.UOp UserOp.Int ∧
      native_zlt (-1 : native_Int) wmv = true ∧
      native_zlt wmv w = true := by
  intro hTy
  -- typeof body = typeof_eq (typeof L) (typeof R)
  have hBodyRed :
      __eo_typeof (ufSbvToIntElimBody t wm n) =
        __eo_typeof_eq
          (__eo_typeof__at_bvsize (__eo_typeof t))
          (__eo_typeof_ite
            (__eo_typeof_eq
              (__eo_typeof_extract (__eo_typeof wm) wm (__eo_typeof wm) wm (__eo_typeof t))
              (__eo_typeof bvOneZeroTerm))
            (__eo_typeof__at_bvsize (__eo_typeof t))
            (__eo_typeof_plus
              (__eo_typeof__at_bvsize (__eo_typeof t)) (__eo_typeof n))) := rfl
  rw [hBodyRed] at hTy
  -- Both sides of top eq agree.
  have hLeqR := typeof_eq_bool_inv _ _ hTy
  -- LHS type must be Int (so typeof t is BitVec): show by cases on typeof t.
  -- First establish typeof t is a BitVec.
  have hLNonStuck : __eo_typeof__at_bvsize (__eo_typeof t) ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hTy
    simp [__eo_typeof_eq] at hTy
  have hTBitVec : ∃ m, __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) m := by
    cases hT : __eo_typeof t with
    | Apply f m =>
        cases f with
        | UOp o =>
            cases o <;>
              first
              | exact ⟨m, rfl⟩
              | (exfalso; apply hLNonStuck; rw [hT]; rfl)
        | _ => exfalso; apply hLNonStuck; rw [hT]; rfl
    | _ => exfalso; apply hLNonStuck; rw [hT]; rfl
  rcases hTBitVec with ⟨mt, hTty⟩
  have hLInt : __eo_typeof__at_bvsize (__eo_typeof t) = Term.UOp UserOp.Int := by
    rw [hTty]; rfl
  -- So typeof R = Int.
  rw [hLInt] at hLeqR
  -- hLeqR : typeof_ite (...) Int (typeof_plus Int (typeof n)) = Int
  have hREq := hLeqR
  -- condition type is Bool
  have hCondBool := typeof_ite_int_forces_bool _ _ _ hREq
  -- destructure ite: branches are Int
  rw [hCondBool] at hREq
  obtain ⟨_hA, hB⟩ := typeof_ite_inv _ _ hREq
  -- hB : typeof_plus Int (typeof n) = Int  ⟹ typeof n = Int
  have hNInt := typeof_plus_int_inv _ hB
  -- condition type Bool : eq (typeof extract) (typeof @bv) = Bool
  have hCondEq := typeof_eq_bool_inv _ _ hCondBool
  -- hCondEq : typeof @bv = typeof extract
  rw [typeof_bv_zero_one] at hCondEq
  -- so typeof extract = BitVec (Numeral 1)
  rcases typeof_extract_diag_bitvec_inv wm t (Term.Numeral 1) hCondEq.symm with
    ⟨wmv, w, hwm, hTty', hg1, hg2⟩
  exact ⟨wmv, w, hwm, hTty', hNInt, hg1, hg2⟩

/-! ## SMT eval rewrites for the operators in the conclusion -/

private theorem smtx_eval_neg_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__ (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_int_pow2_term_eq (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.int_pow2 x) =
      __smtx_model_eval_int_pow2 (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_purify_term_eq (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm._at_purify x) =
      __smtx_model_eval__at_purify (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- The translation of `@bv 0 1` evaluates to `Binary 1 0`. -/
private theorem eval_bv_zero_one (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt bvOneZeroTerm) = SmtValue.Binary 1 0 := by
  have hTrans : __eo_to_smt bvOneZeroTerm =
      SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral 0) := rfl
  rw [hTrans, smtx_eval_int_to_bv_numerals]
  native_decide

/-- The SMT type of `bvsize t` is `Int` and its value is the static width. -/
private theorem eval_bvsize_eq (M : SmtModel) (t : Term) (w : native_Int)
    (hNonneg : native_zleq 0 w = true)
    (hTSmt : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat w)) :
    __eo_to_smt (bvsizeTerm t) =
      SmtTerm._at_purify (SmtTerm.Numeral (native_nat_to_int (native_int_to_nat w))) ∧
    __smtx_model_eval M (__eo_to_smt (bvsizeTerm t)) =
      SmtValue.Numeral (native_nat_to_int (native_int_to_nat w)) := by
  have hSize : __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t)) =
      native_nat_to_int (native_int_to_nat w) := by
    rw [hTSmt]; rfl
  have hNN : native_zleq 0 (native_nat_to_int (native_int_to_nat w)) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int]
  have hTrans : __eo_to_smt (bvsizeTerm t) =
      SmtTerm._at_purify (SmtTerm.Numeral (native_nat_to_int (native_int_to_nat w))) := by
    change (native_ite
        (native_zleq 0 (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt t)))))
        SmtTerm.None) = _
    rw [hSize]
    simp [native_ite, hNN]
  refine ⟨hTrans, ?_⟩
  rw [hTrans, smtx_eval_purify_term_eq, smtx_eval_numeral_eq]
  rfl

/-! ## SMT typing of the two sides of the top equation -/

/-- SMT typing of the LHS `sbv_to_int t` is `Int`. -/
private theorem smt_typeof_sbv_to_int_int (t : Term) (w : native_Int)
    (hNonneg : native_zleq 0 w = true)
    (hTSmt : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat w)) :
    __smtx_typeof (__eo_to_smt (sbvToIntTerm t)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.sbv_to_int (__eo_to_smt t)) = SmtType.Int
  rw [smtx_typeof_sbv_to_int_term_eq, hTSmt]
  rfl

/-- The two sides of the conclusion's top equation evaluate to equal values.
    This is the semantic crux, driven by the premise facts and canonicity.
    Here `wmv` is the (numeral) value of `wm`, `nT` is the third arg `n`, and the
    premise facts give `eval wm = w - 1`, `eval n = 2^w`. -/
private theorem eval_sides_rel
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (nT : Term) (wmv w : native_Int)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNonneg : native_zleq 0 w = true)
    (hwpos : 0 < w)
    (hTSmt : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat w))
    (hWfit : native_nat_to_int (native_int_to_nat w) = w)
    (hWmVal : wmv = w - 1)
    (hNEval :
      __smtx_model_eval M (__eo_to_smt nT) =
        SmtValue.Numeral (native_int_pow2 w)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (sbvToIntTerm t)))
      (__smtx_model_eval M
        (__eo_to_smt
          (iteTerm
            (eqTerm (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t) bvOneZeroTerm)
            (ubvToIntTerm t)
            (negTerm (ubvToIntTerm t) nT)))) := by
  -- `t` evaluates to a canonical `Binary w p`.
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hTSmt] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hTTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨p, hEvalT⟩
  rw [hWfit] at hEvalT
  have hCanon :
      native_zeq p (native_mod_total p (native_int_pow2 w)) = true :=
    bitvec_payload_canonical (u := native_int_to_nat w)
      (by rw [hEvalT] at hEvalTy; exact hEvalTy)
  -- Evaluate the LHS.
  have hEvalLhs :
      __smtx_model_eval M (__eo_to_smt (sbvToIntTerm t)) =
        SmtValue.Numeral (native_binary_uts w p) := by
    change __smtx_model_eval M (SmtTerm.sbv_to_int (__eo_to_smt t)) = _
    rw [smtx_eval_sbv_to_int_term_eq, hEvalT]
    rfl
  -- Evaluate the extract (sign-bit) sub-term.
  have hEvalExtract :
      __smtx_model_eval M
          (__eo_to_smt (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t)) =
        SmtValue.Binary 1 (native_mod_total (native_div_total p (native_int_pow2 wmv)) 2) := by
    change __smtx_model_eval M
        (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t)) = _
    rw [smtx_eval_extract_term_eq, hEvalT, smtx_eval_numeral_eq]
    simp only [__smtx_model_eval_extract]
    have hWidth1 : native_zplus (native_zplus wmv 1) (native_zneg wmv) = 1 := by
      simp only [native_zplus, native_zneg, native_Int]; omega
    rw [hWidth1]
    have hExtractPayload :
        native_mod_total (native_binary_extract w p wmv wmv) (native_int_pow2 1)
          = native_mod_total (native_div_total p (native_int_pow2 wmv)) 2 := by
      have h := extract_sign_bit_payload w p wmv
      rw [show native_zplus (native_zplus wmv 1) (native_zneg wmv) = (1 : native_Int) from
        hWidth1] at h
      exact h
    rw [hExtractPayload]
  -- The arithmetic case split.
  have hPowEq : native_int_pow2 w = 2 * native_int_pow2 (w - 1) :=
    native_int_pow2_succ_pred hwpos
  rcases sign_bit_and_uts_of_canonical (w := w) (n := p) hwpos hCanon with
    ⟨hq, hUts⟩ | ⟨hq, hUts⟩
  · -- sign bit 0
    -- div p 2^(w-1) = 0, uts = p
    have hSignPayload :
        native_mod_total (native_div_total p (native_int_pow2 wmv)) 2 = 0 := by
      rw [hWmVal, hq]
      simp [native_mod_total]
    have hCondEval :
        __smtx_model_eval M
            (__eo_to_smt
              (eqTerm (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t) bvOneZeroTerm)) =
          SmtValue.Boolean true := by
      change __smtx_model_eval M
          (SmtTerm.eq
            (__eo_to_smt (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t))
            (__eo_to_smt bvOneZeroTerm)) = _
      rw [smtx_eval_eq_term_eq, hEvalExtract, eval_bv_zero_one, hSignPayload]
      simp [__smtx_model_eval_eq, native_veq]
    -- ite picks the then-branch: ubv_to_int t = p
    have hEvalA :
        __smtx_model_eval M (__eo_to_smt (ubvToIntTerm t)) = SmtValue.Numeral p := by
      change __smtx_model_eval M (SmtTerm.ubv_to_int (__eo_to_smt t)) = _
      rw [smtx_eval_ubv_to_int_term_eq, hEvalT]
      rfl
    have hEvalRhs :
        __smtx_model_eval M
            (__eo_to_smt
              (iteTerm
                (eqTerm (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t) bvOneZeroTerm)
                (ubvToIntTerm t) (negTerm (ubvToIntTerm t) nT))) =
          SmtValue.Numeral p := by
      change __smtx_model_eval M
          (SmtTerm.ite
            (__eo_to_smt
              (eqTerm (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t) bvOneZeroTerm))
            (__eo_to_smt (ubvToIntTerm t))
            (__eo_to_smt (negTerm (ubvToIntTerm t) nT))) = _
      rw [smtx_eval_ite_term_eq, hCondEval, hEvalA]
      rfl
    rw [hEvalLhs, hEvalRhs, hUts]
    exact RuleProofs.smt_value_rel_refl _
  · -- sign bit 1
    have hSignPayload :
        native_mod_total (native_div_total p (native_int_pow2 wmv)) 2 = 1 := by
      rw [hWmVal, hq]
      simp [native_mod_total]
    have hCondEval :
        __smtx_model_eval M
            (__eo_to_smt
              (eqTerm (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t) bvOneZeroTerm)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M
          (SmtTerm.eq
            (__eo_to_smt (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t))
            (__eo_to_smt bvOneZeroTerm)) = _
      rw [smtx_eval_eq_term_eq, hEvalExtract, eval_bv_zero_one, hSignPayload]
      simp [__smtx_model_eval_eq, native_veq]
    have hEvalA :
        __smtx_model_eval M (__eo_to_smt (ubvToIntTerm t)) = SmtValue.Numeral p := by
      change __smtx_model_eval M (SmtTerm.ubv_to_int (__eo_to_smt t)) = _
      rw [smtx_eval_ubv_to_int_term_eq, hEvalT]
      rfl
    -- else-branch: neg (ubv_to_int t) n = p - 2^w
    have hEvalRhs :
        __smtx_model_eval M
            (__eo_to_smt
              (iteTerm
                (eqTerm (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t) bvOneZeroTerm)
                (ubvToIntTerm t) (negTerm (ubvToIntTerm t) nT))) =
          SmtValue.Numeral (native_zplus p (native_zneg (native_int_pow2 w))) := by
      change __smtx_model_eval M
          (SmtTerm.ite
            (__eo_to_smt
              (eqTerm (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t) bvOneZeroTerm))
            (__eo_to_smt (ubvToIntTerm t))
            (__eo_to_smt (negTerm (ubvToIntTerm t) nT))) = _
      rw [smtx_eval_ite_term_eq, hCondEval]
      change __smtx_model_eval M
          (SmtTerm.neg (__eo_to_smt (ubvToIntTerm t)) (__eo_to_smt nT)) = _
      rw [smtx_eval_neg_term_eq, hEvalA, hNEval]
      rfl
    rw [hEvalLhs, hEvalRhs]
    have hUtsEq : native_binary_uts w p = native_zplus p (native_zneg (native_int_pow2 w)) := by
      rw [hUts]; simp only [native_zplus, native_zneg, native_Int]; omega
    rw [hUtsEq]
    exact RuleProofs.smt_value_rel_refl _

/-- SMT type of the third arg `n` is `Int`, from its EO type being `Int`. -/
private theorem smt_typeof_n_int (n : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hNty : __eo_typeof n = Term.UOp UserOp.Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  have hSmtType :
      __smtx_typeof (__eo_to_smt n) = __eo_to_smt_type (Term.UOp UserOp.Int) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hNty
  rw [hSmtType]; rfl

/-- SMT typing of the RHS `ite (...) (ubv_to_int t) (neg (ubv_to_int t) n)` is `Int`. -/
private theorem smt_typeof_rhs_int
    (t wm n : Term) (wmv w : native_Int)
    (hwm : wm = Term.Numeral wmv)
    (hNonneg : native_zleq 0 w = true)
    (hTSmt : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat w))
    (hNSmt : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hg1 : native_zlt (-1 : native_Int) wmv = true)
    (hg2 : native_zlt wmv w = true) :
    __smtx_typeof
        (__eo_to_smt
          (iteTerm (eqTerm (extractTerm wm wm t) bvOneZeroTerm)
            (ubvToIntTerm t) (negTerm (ubvToIntTerm t) n))) = SmtType.Int := by
  subst wm
  change __smtx_typeof
      (SmtTerm.ite
        (SmtTerm.eq
          (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t))
          (__eo_to_smt bvOneZeroTerm))
        (SmtTerm.ubv_to_int (__eo_to_smt t))
        (SmtTerm.neg (SmtTerm.ubv_to_int (__eo_to_smt t)) (__eo_to_smt n))) = SmtType.Int
  have hBvTrans : __eo_to_smt bvOneZeroTerm =
      SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral 0) := rfl
  have hExtractTy :
      __smtx_typeof
          (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t)) =
        SmtType.BitVec 1 := by
    rw [show __smtx_typeof
          (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t)) =
        __smtx_typeof_extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv)
          (__smtx_typeof (__eo_to_smt t)) by rw [__smtx_typeof.eq_def] <;> simp only]
    rw [hTSmt]
    have hge0 : native_zleq 0 wmv = true := by
      have hlt : (-1 : Int) < wmv := by simpa [native_zlt, SmtEval.native_zlt] using hg1
      have : (0 : Int) ≤ wmv := by omega
      simpa [native_zleq, SmtEval.native_zleq] using this
    have hle : native_zleq wmv wmv = true := by
      simp [native_zleq, SmtEval.native_zleq]
    have hlt : native_zlt wmv (native_nat_to_int (native_int_to_nat w)) = true := by
      have hwlt : (wmv : Int) < w := by simpa [native_zlt, SmtEval.native_zlt] using hg2
      have hwfit : native_nat_to_int (native_int_to_nat w) = w := by
        have : 0 <= w := by simpa [SmtEval.native_zleq] using hNonneg
        simpa [native_int_to_nat, native_nat_to_int] using Int.toNat_of_nonneg this
      rw [hwfit]; simpa [native_zlt, SmtEval.native_zlt] using hwlt
    have hsum :
        native_zplus (native_zplus wmv 1) (native_zneg wmv) =
          (1 : native_Int) := by
      change (wmv + 1) + -wmv = (1 : Int)
      calc
        (wmv + 1) + -wmv = (wmv + -wmv) + 1 := by ac_rfl
        _ = 0 + 1 := by rw [Int.add_right_neg]
        _ = 1 := rfl
    have hwidthPos :
        native_zlt 0
          (native_zplus (native_zplus wmv 1) (native_zneg wmv)) = true := by
      rw [hsum]
      native_decide
    have hwidth : native_int_to_nat
        (native_zplus (native_zplus wmv 1) (native_zneg wmv)) = 1 := by
      rw [hsum]
      native_decide
    have hNatOne : native_int_to_nat (1 : native_Int) = 1 := by
      native_decide
    simpa only [__smtx_typeof_extract, native_ite, hge0, hle, hlt, hwidthPos,
      if_true, hwidth]
      using hNatOne
  have hBvTy :
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)) =
        SmtType.BitVec 1 := by
    rw [typeof_int_to_bv_eq]
    native_decide
  have hUbvTy : __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt t)) = SmtType.Int := by
    rw [show __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt t)) =
        __smtx_typeof_bv_op_1_ret (__smtx_typeof (__eo_to_smt t)) SmtType.Int by
        rw [__smtx_typeof.eq_def] <;> simp only]
    rw [hTSmt]; rfl
  -- condition type: eq of two BitVec 1 => Bool
  have hCondTy :
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t))
            (__eo_to_smt bvOneZeroTerm)) = SmtType.Bool := by
    rw [show __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t))
            (__eo_to_smt bvOneZeroTerm)) =
        __smtx_typeof_eq
          (__smtx_typeof
            (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t)))
          (__smtx_typeof (__eo_to_smt bvOneZeroTerm)) by
        rw [__smtx_typeof.eq_def] <;> simp only]
    rw [hExtractTy, hBvTrans, hBvTy]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  -- neg type: arith_overload_op_2 Int Int = Int
  have hNegTy :
      __smtx_typeof (SmtTerm.neg (SmtTerm.ubv_to_int (__eo_to_smt t)) (__eo_to_smt n)) =
        SmtType.Int := by
    rw [show __smtx_typeof
          (SmtTerm.neg (SmtTerm.ubv_to_int (__eo_to_smt t)) (__eo_to_smt n)) =
        __smtx_typeof_arith_overload_op_2
          (__smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt t)))
          (__smtx_typeof (__eo_to_smt n)) by
        rw [__smtx_typeof.eq_def] <;> simp only]
    rw [hUbvTy, hNSmt]; rfl
  rw [show __smtx_typeof
        (SmtTerm.ite
          (SmtTerm.eq
            (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t))
            (__eo_to_smt bvOneZeroTerm))
          (SmtTerm.ubv_to_int (__eo_to_smt t))
          (SmtTerm.neg (SmtTerm.ubv_to_int (__eo_to_smt t)) (__eo_to_smt n))) =
      __smtx_typeof_ite
        (__smtx_typeof
          (SmtTerm.eq
            (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral wmv) (__eo_to_smt t))
            (__eo_to_smt bvOneZeroTerm)))
        (__smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt t)))
        (__smtx_typeof
          (SmtTerm.neg (SmtTerm.ubv_to_int (__eo_to_smt t)) (__eo_to_smt n))) by
      rw [__smtx_typeof.eq_def] <;> simp only]
  rw [hCondTy, hUbvTy, hNegTy]
  simp [__smtx_typeof_ite, native_ite, native_Teq]

/-- `eo_has_bool_type` of the conclusion body from its EO type being `Bool`. -/
private theorem typed_body_impl
    (t wm n : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hResultTy : __eo_typeof (ufSbvToIntElimBody t wm n) = Term.Bool) :
    RuleProofs.eo_has_bool_type (ufSbvToIntElimBody t wm n) := by
  rcases typeof_args_of_body_bool t wm n hResultTy with
    ⟨wmv, w, hwm, hTty, hNty, hg1, hg2⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t w hTTrans hTty with
    ⟨hNonneg, hTSmt⟩
  have hNSmt : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    smt_typeof_n_int n hNTrans hNty
  have hLhsTy := smt_typeof_sbv_to_int_int t w hNonneg hTSmt
  have hRhsTy := smt_typeof_rhs_int t wm n wmv w hwm hNonneg hTSmt hNSmt hg1 hg2
  refine RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (sbvToIntTerm t)
    (iteTerm (eqTerm (extractTerm wm wm t) bvOneZeroTerm)
      (ubvToIntTerm t) (negTerm (ubvToIntTerm t) n)) ?_ ?_
  · rw [hLhsTy, hRhsTy]
  · rw [hLhsTy]; simp

/-- Facts: the conclusion body interprets `true` in `M`, given the premise
    evidence. -/
private theorem facts_body_impl
    (M : SmtModel) (hM : model_wf M)
    (t wm n : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hResultTy : __eo_typeof (ufSbvToIntElimBody t wm n) = Term.Bool)
    (hP1 : eo_interprets M (eqTerm wm (negTerm (bvsizeTerm t) (Term.Numeral 1))) true)
    (hP2 : eo_interprets M (eqTerm n (intPow2Term (bvsizeTerm t))) true) :
    eo_interprets M (ufSbvToIntElimBody t wm n) true := by
  rcases typeof_args_of_body_bool t wm n hResultTy with
    ⟨wmv, w, hwm, hTty, hNty, hg1, hg2⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t w hTTrans hTty with
    ⟨hNonneg, hTSmt⟩
  have hwfit : native_nat_to_int (native_int_to_nat w) = w := by
    have : 0 <= w := by simpa [SmtEval.native_zleq] using hNonneg
    simpa [native_int_to_nat, native_nat_to_int] using Int.toNat_of_nonneg this
  -- Width is positive: wmv satisfies -1 < wmv < w, so 0 ≤ wmv < w hence w ≥ 1.
  have hwpos : (0 : Int) < w := by
    have h1 : (-1 : Int) < wmv := by simpa [native_zlt, SmtEval.native_zlt] using hg1
    have h2 : (wmv : Int) < w := by simpa [native_zlt, SmtEval.native_zlt] using hg2
    have h0 : (0 : Int) ≤ wmv := by omega
    exact Int.lt_of_le_of_lt h0 h2
  -- From premise 1: eval(wm) = w - 1.
  have hBvsize := eval_bvsize_eq M t w hNonneg hTSmt
  -- eval of neg (bvsize t) 1
  have hNegEval :
      __smtx_model_eval M (__eo_to_smt (negTerm (bvsizeTerm t) (Term.Numeral 1))) =
        SmtValue.Numeral (native_zplus w (native_zneg 1)) := by
    change __smtx_model_eval M
        (SmtTerm.neg (__eo_to_smt (bvsizeTerm t)) (SmtTerm.Numeral 1)) = _
    rw [smtx_eval_neg_term_eq, hBvsize.2, smtx_eval_numeral_eq]
    rw [hwfit]
    rfl
  have hWmRel := RuleProofs.eo_interprets_eq_rel M wm
    (negTerm (bvsizeTerm t) (Term.Numeral 1)) hP1
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hWmRel
  rw [hNegEval] at hWmRel
  subst hwm
  change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Numeral wmv))
      (SmtValue.Numeral (native_zplus w (native_zneg 1))) =
    SmtValue.Boolean true at hWmRel
  rw [smtx_eval_numeral_eq] at hWmRel
  have hWmEq : wmv = native_zplus w (native_zneg 1) := by
    have := (smtx_model_eval_eq_true_iff_numeral hWmRel)
    exact this
  have hWmVal : wmv = w - 1 := by
    rw [hWmEq]
    simp [native_zplus, native_zneg, Int.sub_eq_add_neg]
  -- From premise 2: eval(n) = 2^w.
  have hPow2Eval :
      __smtx_model_eval M (__eo_to_smt (intPow2Term (bvsizeTerm t))) =
        SmtValue.Numeral (native_int_pow2 w) := by
    change __smtx_model_eval M (SmtTerm.int_pow2 (__eo_to_smt (bvsizeTerm t))) = _
    rw [smtx_eval_int_pow2_term_eq, hBvsize.2]
    rw [hwfit]
    rfl
  have hNRel := RuleProofs.eo_interprets_eq_rel M n
    (intPow2Term (bvsizeTerm t)) hP2
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hNRel
  rw [hPow2Eval] at hNRel
  have hNEval :
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral (native_int_pow2 w) := by
    have hNSmt : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
      smt_typeof_n_int n hNTrans hNty
    -- n evals to a Numeral
    have hNValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
      rw [smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hNTrans), hNSmt]
    rcases int_value_canonical hNValTy with ⟨nv, hnv⟩
    rw [hnv] at hNRel ⊢
    have : nv = native_int_pow2 w := by
      have := smtx_model_eval_eq_true_iff_numeral hNRel
      exact this
    rw [this]
  -- Conclude via the eval crux.
  have hBoolTy : RuleProofs.eo_has_bool_type
      (ufSbvToIntElimBody t (Term.Numeral wmv) n) := by
    have := typed_body_impl t (Term.Numeral wmv) n hTTrans hNTrans hResultTy
    exact this
  change eo_interprets M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (sbvToIntTerm t))
      (iteTerm (eqTerm (extractTerm (Term.Numeral wmv) (Term.Numeral wmv) t) bvOneZeroTerm)
        (ubvToIntTerm t) (negTerm (ubvToIntTerm t) n))) true
  apply RuleProofs.eo_interprets_eq_of_rel M (sbvToIntTerm t) _ hBoolTy
  exact eval_sides_rel M hM t n wmv w hTTrans hNonneg hwpos hTSmt hwfit hWmVal hNEval

public theorem cmd_step_uf_sbv_to_int_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_sbv_to_int_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_sbv_to_int_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_sbv_to_int_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.uf_sbv_to_int_elim args premises ≠ Term.Stuck :=
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
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons n2 premises =>
                          cases premises with
                          | nil =>
                              let P1 := __eo_state_proven_nth s n1
                              let P2 := __eo_state_proven_nth s n2
                              have hTransTriple :
                                  RuleProofs.eo_has_smt_translation a1 ∧
                                    RuleProofs.eo_has_smt_translation a2 ∧
                                      RuleProofs.eo_has_smt_translation a3 ∧ True := by
                                simpa [cmdTranslationOk, cArgListTranslationOk,
                                  eoHasSmtTranslation,
                                  RuleProofs.eo_has_smt_translation] using hCmdTrans
                              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                                hTransTriple.1
                              have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                                hTransTriple.2.2.1
                              change __eo_typeof
                                  (__eo_prog_uf_sbv_to_int_elim a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2)) = Term.Bool at hResultTy
                              have hProgArg :
                                  __eo_prog_uf_sbv_to_int_elim a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              obtain ⟨hA1NS, hA2NS, hA3NS⟩ :=
                                args_ne_stuck_of_prog_not_stuck a1 a2 a3 P1 P2 hProgArg
                              rcases shape_of_prog_uf_sbv_to_int_elim_not_stuck a1 a2 a3
                                P1 P2 hA1NS hA2NS hA3NS hProgArg with
                                ⟨wm2, t2, nTerm2, t3, hP1eq, hP2eq⟩
                              have hProgEq :
                                  __eo_prog_uf_sbv_to_int_elim a1 a2 a3
                                      (Proof.pf P1) (Proof.pf P2) =
                                    __eo_requires
                                      (__eo_and
                                        (__eo_and (__eo_and (__eo_eq a2 wm2) (__eo_eq a1 t2))
                                          (__eo_eq a3 nTerm2))
                                        (__eo_eq a1 t3))
                                      (Term.Boolean true)
                                      (ufSbvToIntElimBody a1 a2 a3) := by
                                rw [hP1eq, hP2eq]
                                exact prog_uf_sbv_to_int_elim_eq a1 a2 a3 wm2 t2 nTerm2 t3
                                  hA1NS hA2NS hA3NS
                              rw [hProgEq] at hProgArg hResultTy
                              obtain ⟨hwm2, ht2, hn2, ht3⟩ :=
                                eqs_of_requires_and4_eq_true_not_stuck a2 wm2 a1 t2 a3 nTerm2
                                  a1 t3 _ hProgArg
                              rw [hwm2, ht2] at hP1eq
                              rw [hn2, ht3] at hP2eq
                              rw [hwm2, ht2, hn2, ht3] at hProgEq hResultTy
                              rw [requires_and4_eq_self_true_body a1 a2 a3 _
                                hA1NS hA2NS hA3NS] at hResultTy
                              have hStepEq :
                                  __eo_cmd_step_proven s CRule.uf_sbv_to_int_elim
                                      (CArgList.cons a1
                                        (CArgList.cons a2 (CArgList.cons a3 CArgList.nil)))
                                      (CIndexList.cons n1
                                        (CIndexList.cons n2 CIndexList.nil)) =
                                    ufSbvToIntElimBody a1 a2 a3 := by
                                change __eo_prog_uf_sbv_to_int_elim a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2) =
                                  ufSbvToIntElimBody a1 a2 a3
                                rw [hProgEq, requires_and4_eq_self_true_body a1 a2 a3 _
                                  hA1NS hA2NS hA3NS]
                              rw [hStepEq]
                              refine ⟨?_, ?_⟩
                              · intro hPrem
                                have hAll : AllInterpretedTrue M (premiseTermList s
                                    (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil))) :=
                                  hPrem.true_here
                                have hP1true : eo_interprets M P1 true :=
                                  hAll P1 (by left)
                                have hP2true : eo_interprets M P2 true :=
                                  hAll P2 (by right; left)
                                rw [hP1eq] at hP1true
                                rw [hP2eq] at hP2true
                                exact facts_body_impl M hM a1 a2 a3 hA1Trans hA3Trans
                                  hResultTy hP1true hP2true
                              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (typed_body_impl a1 a2 a3 hA1Trans hA3Trans hResultTy)
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
