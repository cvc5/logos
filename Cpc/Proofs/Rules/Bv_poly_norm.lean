module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private theorem native_int_pow2_pos_nat (w : native_Nat) :
    0 < native_int_pow2 (native_nat_to_int w) := by
  rw [native_int_pow2_nat]
  have hPow : 0 < (2 ^ w : Nat) :=
    Nat.pow_pos (by decide : 0 < (2 : Nat))
  exact Int.natCast_pos.mpr hPow

private theorem native_to_int_to_real
    (n : native_Int) :
  native_to_int (native_to_real n) = n := by
  rw [native_to_int, native_to_real, native_mk_rational]
  change Rat.floor ((n : Rat) / (1 : Rat)) = n
  have hDiv : ((n : Rat) / (1 : Rat)) = (n : Rat) := by
    change (n : Rat) * ((1 : Rat)⁻¹) = (n : Rat)
    rw [Rat.inv_def]
    change (n : Rat) * Rat.divInt 1 1 = (n : Rat)
    rw [show Rat.divInt 1 1 = (1 : Rat) by rfl]
    exact Rat.mul_one _
  rw [hDiv]
  exact Rat.floor_intCast n

private theorem native_to_int_one :
  native_to_int (native_mk_rational 1 1) = 1 := by
  change native_to_int (native_to_real 1) = 1
  exact native_to_int_to_real 1

private theorem native_to_real_inj
    {m n : native_Int} :
  native_to_real m = native_to_real n ->
  m = n := by
  intro h
  have h' := congrArg native_to_int h
  simpa [native_to_int_to_real] using h'

private theorem native_to_int_qneg_to_real
    (n : native_Int) :
  native_to_int (native_qneg (native_to_real n)) = native_zneg n := by
  rw [← native_to_real_neg]
  exact native_to_int_to_real _

private theorem native_to_int_qplus_to_real
    (m n : native_Int) :
  native_to_int (native_qplus (native_to_real m) (native_to_real n)) =
    native_zplus m n := by
  rw [← native_to_real_add]
  exact native_to_int_to_real _

private theorem native_qplus_to_real_eq_zero_iff
    (m n : native_Int) :
  native_qplus (native_to_real m) (native_to_real n) = native_mk_rational 0 1 ↔
    native_zplus m n = 0 := by
  constructor
  · intro h
    apply native_to_real_inj
    rw [native_to_real_add]
    simpa [native_to_real] using h
  · intro h
    rw [← native_to_real_add, h]
    rfl

private theorem emod_mul_left_congr
    (c v m : native_Int) :
  ((c % m) * v) % m = (c * v) % m := by
  rw [Int.mul_emod]
  rw [Int.emod_emod]
  exact (Int.mul_emod c v m).symm

private theorem emod_add_congr
    {a b c d m : native_Int}
    (ha : a % m = c % m)
    (hb : b % m = d % m) :
  (a + b) % m = (c + d) % m := by
  calc
    (a + b) % m = (a % m + b % m) % m := Int.add_emod a b m
    _ = (c % m + d % m) % m := by rw [ha, hb]
    _ = (c + d) % m := (Int.add_emod c d m).symm

private theorem emod_mul_congr
    {a b c d m : native_Int}
    (ha : a % m = c % m)
    (hb : b % m = d % m) :
  (a * b) % m = (c * d) % m := by
  calc
    (a * b) % m = (a % m * (b % m)) % m := Int.mul_emod a b m
    _ = (c % m * (d % m)) % m := by rw [ha, hb]
    _ = (c * d) % m := (Int.mul_emod c d m).symm

private theorem emod_neg_congr
    {a b m : native_Int}
    (h : a % m = b % m) :
  (-a) % m = (-b) % m := by
  have hZero : (a - b) % m = 0 :=
    (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp h
  have hDvd : m ∣ a - b :=
    Int.dvd_of_emod_eq_zero hZero
  have hDvdNeg : m ∣ - (a - b) := by
    rcases hDvd with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [hk]
    simp [Int.mul_neg]
  have hZeroNeg : ((-a) - (-b)) % m = 0 := by
    have hEq : (-a) - (-b) = - (a - b) := by
      simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_comm]
    rw [hEq]
    exact Int.emod_eq_zero_of_dvd hDvdNeg
  exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr hZeroNeg

private noncomputable def bv_atom_denote (M : SmtModel) (t : Term) : native_Int :=
  match __smtx_model_eval M (__eo_to_smt t) with
  | SmtValue.Binary _ n => n
  | _ => 0

private noncomputable def bv_mvar_denote (M : SmtModel) : Term -> native_Int
  | Term.__eo_List_nil => 1
  | Term.Apply (Term.Apply Term.__eo_List_cons a) rest =>
      bv_atom_denote M a * bv_mvar_denote M rest
  | _ => 0

private noncomputable def bv_mon_denote (M : SmtModel) : Term -> native_Int
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational q) =>
      native_to_int q * bv_mvar_denote M vars
  | _ => 0

private noncomputable def bv_poly_denote (M : SmtModel) : Term -> native_Int
  | Term.UOp UserOp._at__at_poly_zero => 0
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p =>
      bv_mon_denote M m + bv_poly_denote M p
  | _ => 0

private inductive bv_mvar_wf : Term -> Prop where
  | nil : bv_mvar_wf Term.__eo_List_nil
  | cons (a rest : Term) :
      a ≠ Term.Stuck ->
      bv_mvar_wf rest ->
      bv_mvar_wf (Term.Apply (Term.Apply Term.__eo_List_cons a) rest)

private inductive bv_mon_int_wf : Term -> Prop where
  | mk (vars : Term) (c : native_Int) :
      bv_mvar_wf vars ->
      bv_mon_int_wf
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
          (Term.Rational (native_to_real c)))

private inductive bv_poly_int_wf : Term -> Prop where
  | zero : bv_poly_int_wf (Term.UOp UserOp._at__at_poly_zero)
  | cons (m p : Term) :
      bv_mon_int_wf m ->
      bv_poly_int_wf p ->
      bv_poly_int_wf (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p)

private theorem bv_mvar_wf_ne_stuck
    {vars : Term}
    (hvars : bv_mvar_wf vars) :
  vars ≠ Term.Stuck := by
  intro hSt
  cases hvars <;> cases hSt

private theorem bv_mon_int_wf_ne_stuck
    {m : Term}
    (hm : bv_mon_int_wf m) :
  m ≠ Term.Stuck := by
  intro hSt
  cases hm <;> cases hSt

private theorem bv_poly_int_wf_ne_stuck
    {p : Term}
    (hp : bv_poly_int_wf p) :
  p ≠ Term.Stuck := by
  intro hSt
  cases hp <;> cases hSt

private def bv_var_poly (t : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at__at_poly)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_mon)
          (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil))
        (Term.Rational (native_mk_rational 1 1))))
    (Term.UOp UserOp._at__at_poly_zero)

private theorem bv_poly_int_wf_var
    {t : Term}
    (hNotStuck : t ≠ Term.Stuck) :
  bv_poly_int_wf (bv_var_poly t) := by
  simpa [bv_var_poly, native_to_real] using
    (bv_poly_int_wf.cons
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_mon)
          (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil))
        (Term.Rational (native_to_real 1)))
      (Term.UOp UserOp._at__at_poly_zero)
      (bv_mon_int_wf.mk
        (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil)
        1 (bv_mvar_wf.cons t Term.__eo_List_nil hNotStuck bv_mvar_wf.nil))
      bv_poly_int_wf.zero)

private theorem bv_poly_denote_var
    (M : SmtModel) (t : Term) :
  bv_poly_denote M (bv_var_poly t) = bv_atom_denote M t := by
  simp [bv_var_poly, bv_poly_denote, bv_mon_denote, bv_mvar_denote,
    native_to_int_one]

private theorem bv_atom_ne_stuck_of_smt_bitvec_type
    {t : Term} {w : native_Nat}
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
  t ≠ Term.Stuck := by
  intro hSt
  subst t
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
    TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

private theorem mvar_mul_mvar_nil_left
    (vars : Term) :
  __mvar_mul_mvar Term.__eo_List_nil vars = vars := by
  cases vars <;> simp [__mvar_mul_mvar]

private theorem mvar_mul_mvar_nil_right
    (vars : Term) :
  __mvar_mul_mvar vars Term.__eo_List_nil = vars := by
  cases vars <;> simp [__mvar_mul_mvar]

private theorem mvar_mul_mvar_cons_cons_true
    (a1 rest1 c1 rest2 : Term)
    (hA1 : a1 ≠ Term.Stuck)
    (hC1 : c1 ≠ Term.Stuck)
    (hCmp : native_tcmp c1 a1 = true) :
  __mvar_mul_mvar
      (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1)
      (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) =
    __eo_mk_apply (Term.Apply Term.__eo_List_cons a1)
      (__mvar_mul_mvar rest1
        (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2)) := by
  simp [__mvar_mul_mvar, __eo_cmp, __eo_ite, native_ite, native_teq, hCmp,
    __eo_mk_apply]

private theorem mvar_mul_mvar_cons_cons_false
    (a1 rest1 c1 rest2 : Term)
    (hA1 : a1 ≠ Term.Stuck)
    (hC1 : c1 ≠ Term.Stuck)
    (hCmp : native_tcmp c1 a1 = false) :
  __mvar_mul_mvar
      (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1)
      (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) =
    __eo_mk_apply (Term.Apply Term.__eo_List_cons c1)
      (__mvar_mul_mvar
        (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2) := by
  simp [__mvar_mul_mvar, __eo_cmp, __eo_ite, native_ite, native_teq, hCmp,
    __eo_mk_apply]

private theorem bv_mvar_wf_of_mvar_mul_mvar
    {vars1 vars2 : Term}
    (hvars1 : bv_mvar_wf vars1)
    (hvars2 : bv_mvar_wf vars2) :
  bv_mvar_wf (__mvar_mul_mvar vars1 vars2) := by
  cases hvars1 with
  | nil =>
      rw [mvar_mul_mvar_nil_left]
      exact hvars2
  | cons a1 rest1 hA1 hRest1 =>
      cases hvars2 with
      | nil =>
          rw [mvar_mul_mvar_nil_right]
          exact bv_mvar_wf.cons a1 rest1 hA1 hRest1
      | cons c1 rest2 hC1 hRest2 =>
          by_cases hCmp : native_tcmp c1 a1 = true
          · have hTail :
                __mvar_mul_mvar rest1
                  (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) ≠ Term.Stuck :=
              bv_mvar_wf_ne_stuck
                (bv_mvar_wf_of_mvar_mul_mvar hRest1
                  (bv_mvar_wf.cons c1 rest2 hC1 hRest2))
            rw [mvar_mul_mvar_cons_cons_true a1 rest1 c1 rest2 hA1 hC1 hCmp]
            simpa [__eo_mk_apply, hTail] using
              (bv_mvar_wf.cons a1
                (__mvar_mul_mvar rest1
                  (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2))
                hA1
                (bv_mvar_wf_of_mvar_mul_mvar hRest1
                  (bv_mvar_wf.cons c1 rest2 hC1 hRest2)))
          · have hCmp' : native_tcmp c1 a1 = false := by
              cases hT : native_tcmp c1 a1 with
              | false => rfl
              | true => exact False.elim (hCmp hT)
            have hTail :
                __mvar_mul_mvar
                  (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2 ≠
                    Term.Stuck :=
              bv_mvar_wf_ne_stuck
                (bv_mvar_wf_of_mvar_mul_mvar
                  (bv_mvar_wf.cons a1 rest1 hA1 hRest1) hRest2)
            rw [mvar_mul_mvar_cons_cons_false a1 rest1 c1 rest2 hA1 hC1 hCmp']
            simpa [__eo_mk_apply, hTail] using
              (bv_mvar_wf.cons c1
                (__mvar_mul_mvar
                  (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2)
                hC1
                (bv_mvar_wf_of_mvar_mul_mvar
                  (bv_mvar_wf.cons a1 rest1 hA1 hRest1) hRest2))
termination_by sizeOf vars1 + sizeOf vars2
decreasing_by
  simp_wf
  · have hSize :
        sizeOf rest1 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf rest2 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) := by
        simp
        omega
    omega

private theorem bv_mvar_denote_of_mvar_mul_mvar
    (M : SmtModel) {vars1 vars2 : Term}
    (hvars1 : bv_mvar_wf vars1)
    (hvars2 : bv_mvar_wf vars2) :
  bv_mvar_denote M (__mvar_mul_mvar vars1 vars2) =
    bv_mvar_denote M vars1 * bv_mvar_denote M vars2 := by
  cases hvars1 with
  | nil =>
      rw [mvar_mul_mvar_nil_left]
      simp [bv_mvar_denote]
  | cons a1 rest1 hA1 hRest1 =>
      cases hvars2 with
      | nil =>
          rw [mvar_mul_mvar_nil_right]
          simp [bv_mvar_denote]
      | cons c1 rest2 hC1 hRest2 =>
          let vars1' := Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1
          let vars2' := Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2
          by_cases hCmp : native_tcmp c1 a1 = true
          · have hRec :
                bv_mvar_denote M (__mvar_mul_mvar rest1 vars2') =
                  bv_mvar_denote M rest1 * bv_mvar_denote M vars2' :=
              bv_mvar_denote_of_mvar_mul_mvar M hRest1
                (bv_mvar_wf.cons c1 rest2 hC1 hRest2)
            have hTail :
                __mvar_mul_mvar rest1 vars2' ≠ Term.Stuck :=
              bv_mvar_wf_ne_stuck
                (bv_mvar_wf_of_mvar_mul_mvar hRest1
                  (bv_mvar_wf.cons c1 rest2 hC1 hRest2))
            rw [mvar_mul_mvar_cons_cons_true a1 rest1 c1 rest2 hA1 hC1 hCmp]
            simp [vars2', __eo_mk_apply, bv_mvar_denote, hRec]
            ac_rfl
          · have hCmp' : native_tcmp c1 a1 = false := by
              cases hT : native_tcmp c1 a1 with
              | false => rfl
              | true => exact False.elim (hCmp hT)
            have hRec :
                bv_mvar_denote M (__mvar_mul_mvar vars1' rest2) =
                  bv_mvar_denote M vars1' * bv_mvar_denote M rest2 :=
              bv_mvar_denote_of_mvar_mul_mvar M
                (bv_mvar_wf.cons a1 rest1 hA1 hRest1) hRest2
            have hTail :
                __mvar_mul_mvar vars1' rest2 ≠ Term.Stuck :=
              bv_mvar_wf_ne_stuck
                (bv_mvar_wf_of_mvar_mul_mvar
                  (bv_mvar_wf.cons a1 rest1 hA1 hRest1) hRest2)
            rw [mvar_mul_mvar_cons_cons_false a1 rest1 c1 rest2 hA1 hC1 hCmp']
            simp [vars1', __eo_mk_apply, bv_mvar_denote, hRec]
            ac_rfl
termination_by sizeOf vars1 + sizeOf vars2
decreasing_by
  simp_wf
  · have hSize :
        sizeOf rest1 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf rest2 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) := by
        simp
        omega
    omega

private theorem bv_mon_int_wf_of_mon_mul_mon
    {m1 m2 : Term}
    (hm1 : bv_mon_int_wf m1)
    (hm2 : bv_mon_int_wf m2) :
  bv_mon_int_wf (__mon_mul_mon m1 m2) := by
  cases hm1 with
  | mk vars1 c1 hvars1 =>
      cases hm2 with
      | mk vars2 c2 hvars2 =>
          have hVars :
              __mvar_mul_mvar vars1 vars2 ≠ Term.Stuck :=
            bv_mvar_wf_ne_stuck (bv_mvar_wf_of_mvar_mul_mvar hvars1 hvars2)
          rw [show __mon_mul_mon
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational (native_to_real c1)))
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational (native_to_real c2))) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_mon) (__mvar_mul_mvar vars1 vars2))
                    (Term.Rational (native_to_real (native_zmult c1 c2))) by
                simp [__mon_mul_mon, __eo_mul, __eo_mk_apply, native_to_real_mul]]
          exact bv_mon_int_wf.mk (__mvar_mul_mvar vars1 vars2)
            (native_zmult c1 c2) (bv_mvar_wf_of_mvar_mul_mvar hvars1 hvars2)

private theorem bv_mon_denote_of_mon_mul_mon
    (M : SmtModel) {m1 m2 : Term}
    (hm1 : bv_mon_int_wf m1)
    (hm2 : bv_mon_int_wf m2) :
  bv_mon_denote M (__mon_mul_mon m1 m2) =
    bv_mon_denote M m1 * bv_mon_denote M m2 := by
  cases hm1 with
  | mk vars1 c1 hvars1 =>
      cases hm2 with
      | mk vars2 c2 hvars2 =>
          have hVars :
              __mvar_mul_mvar vars1 vars2 ≠ Term.Stuck :=
            bv_mvar_wf_ne_stuck (bv_mvar_wf_of_mvar_mul_mvar hvars1 hvars2)
          rw [show __mon_mul_mon
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational (native_to_real c1)))
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational (native_to_real c2))) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_mon) (__mvar_mul_mvar vars1 vars2))
                    (Term.Rational (native_to_real (native_zmult c1 c2))) by
                simp [__mon_mul_mon, __eo_mul, __eo_mk_apply, native_to_real_mul]]
          simp [bv_mon_denote, native_to_int_to_real,
            bv_mvar_denote_of_mvar_mul_mvar M hvars1 hvars2,
            SmtEval.native_zmult]
          ac_rfl

private theorem bv_poly_int_wf_of_poly_neg
    {p : Term}
    (hp : bv_poly_int_wf p) :
  bv_poly_int_wf (__poly_neg p) := by
  induction hp with
  | zero =>
      simpa [__poly_neg] using bv_poly_int_wf.zero
  | cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hTail : __poly_neg p ≠ Term.Stuck :=
            bv_poly_int_wf_ne_stuck ih
          simpa [__poly_neg, __eo_mk_apply, __eo_neg, hTail,
            ← native_to_real_neg] using
            (bv_poly_int_wf.cons
              (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_to_real (native_zneg c))))
              (__poly_neg p)
              (bv_mon_int_wf.mk vars (native_zneg c) hvars)
              ih)

private theorem bv_poly_denote_of_poly_neg
    (M : SmtModel) {p : Term}
    (hp : bv_poly_int_wf p) :
  bv_poly_denote M (__poly_neg p) = - bv_poly_denote M p := by
  induction hp with
  | zero =>
      simp [__poly_neg, bv_poly_denote]
  | cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hTail : __poly_neg p ≠ Term.Stuck :=
            bv_poly_int_wf_ne_stuck (bv_poly_int_wf_of_poly_neg hp)
          simp [__poly_neg, __eo_mk_apply, __eo_neg, bv_poly_denote,
            bv_mon_denote, native_to_int_to_real, native_to_int_qneg_to_real, ih,
            SmtEval.native_zneg]
          simp [Int.neg_add, Int.neg_mul]

private theorem bv_poly_int_wf_of_poly_add
    {P1 P2 : Term}
    (h1 : bv_poly_int_wf P1)
    (h2 : bv_poly_int_wf P2) :
  bv_poly_int_wf (__poly_add P1 P2) := by
  cases h1 with
  | zero =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using bv_poly_int_wf.zero
      | cons m2 p2 hm2 hp2 =>
          simpa [__poly_add] using bv_poly_int_wf.cons m2 p2 hm2 hp2
  | cons m1 p1 hm1 hp1 =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using bv_poly_int_wf.cons m1 p1 hm1 hp1
      | cons m2 p2 hm2 hp2 =>
          cases hm1 with
          | mk vars1 c1 hvars1 =>
              cases hm2 with
              | mk vars2 c2 hvars2 =>
                  have hVars1 : vars1 ≠ Term.Stuck := bv_mvar_wf_ne_stuck hvars1
                  have hVars2 : vars2 ≠ Term.Stuck := bv_mvar_wf_ne_stuck hvars2
                  by_cases hEq : vars1 = vars2
                  · subst vars2
                    have hRec : bv_poly_int_wf (__poly_add p1 p2) :=
                      bv_poly_int_wf_of_poly_add hp1 hp2
                    by_cases hZero :
                        native_qplus (native_to_real c1) (native_to_real c2) =
                          native_mk_rational 0 1
                    · have hZero' :
                          native_mk_rational 0 1 =
                            native_qplus (native_to_real c1) (native_to_real c2) := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero'] using hRec
                    · have hTail : __poly_add p1 p2 ≠ Term.Stuck :=
                        bv_poly_int_wf_ne_stuck hRec
                      have hZero' :
                          native_mk_rational 0 1 ≠
                            native_qplus (native_to_real c1) (native_to_real c2) := by
                        simpa [eq_comm] using hZero
                      have hZeroRat :
                          native_mk_rational 0 1 ≠
                            native_to_real (native_zplus c1 c2) := by
                        intro h
                        apply hZero
                        rw [← native_to_real_add]
                        exact h.symm
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero', hZeroRat, __eo_mk_apply, hTail,
                        ← native_to_real_add] using
                        (bv_poly_int_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational (native_to_real (native_zplus c1 c2))))
                          (__poly_add p1 p2)
                          (bv_mon_int_wf.mk vars1 (native_zplus c1 c2) hvars1)
                          hRec)
                  · have hEq' : vars2 ≠ vars1 := by
                      simpa [eq_comm] using hEq
                    by_cases hCmp : native_tcmp vars2 vars1
                    · have hRec : bv_poly_int_wf
                            (__poly_add p1
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                    (Term.Rational (native_to_real c2))))
                                p2)) :=
                          bv_poly_int_wf_of_poly_add hp1
                            (bv_poly_int_wf.cons
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                (Term.Rational (native_to_real c2)))
                              p2
                              (bv_mon_int_wf.mk vars2 c2 hvars2)
                              hp2)
                      have hTail :
                          __poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational (native_to_real c2))))
                              p2) ≠ Term.Stuck :=
                        bv_poly_int_wf_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail, __eo_add, hRec, native_ite, native_mk_rational] using
                        (bv_poly_int_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational (native_to_real c1)))
                          (__poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational (native_to_real c2))))
                              p2))
                          (bv_mon_int_wf.mk vars1 c1 hvars1)
                          hRec)
                    · have hRec : bv_poly_int_wf
                            (__poly_add
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                    (Term.Rational (native_to_real c1))))
                                p1)
                              p2) :=
                          bv_poly_int_wf_of_poly_add
                            (bv_poly_int_wf.cons
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                (Term.Rational (native_to_real c1)))
                              p1
                              (bv_mon_int_wf.mk vars1 c1 hvars1)
                              hp1)
                            hp2
                      have hTail :
                          __poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational (native_to_real c1))))
                              p1)
                            p2 ≠ Term.Stuck :=
                        bv_poly_int_wf_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail, __eo_add, hRec, native_ite, native_mk_rational] using
                        (bv_poly_int_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                            (Term.Rational (native_to_real c2)))
                          (__poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational (native_to_real c1))))
                              p1)
                            p2)
                          (bv_mon_int_wf.mk vars2 c2 hvars2)
                          hRec)
termination_by sizeOf P1 + sizeOf P2
decreasing_by
  simp_wf
  · omega
  · have hSize :
        sizeOf p1 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational (native_to_real c1))))
              p1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf p2 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational (native_to_real c2))))
              p2) := by
        simp
        omega
    omega

private theorem bv_poly_denote_of_poly_add
    (M : SmtModel) {P1 P2 : Term}
    (h1 : bv_poly_int_wf P1)
    (h2 : bv_poly_int_wf P2) :
  bv_poly_denote M (__poly_add P1 P2) =
    bv_poly_denote M P1 + bv_poly_denote M P2 := by
  cases h1 with
  | zero =>
      cases h2 with
      | zero =>
          simp [__poly_add, bv_poly_denote]
      | cons m2 p2 hm2 hp2 =>
          simp [__poly_add, bv_poly_denote]
  | cons m1 p1 hm1 hp1 =>
      cases h2 with
      | zero =>
          simp [__poly_add, bv_poly_denote]
      | cons m2 p2 hm2 hp2 =>
          cases hm1 with
          | mk vars1 c1 hvars1 =>
              cases hm2 with
              | mk vars2 c2 hvars2 =>
                  have hVars1 : vars1 ≠ Term.Stuck := bv_mvar_wf_ne_stuck hvars1
                  have hVars2 : vars2 ≠ Term.Stuck := bv_mvar_wf_ne_stuck hvars2
                  let mon1 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                      (Term.Rational (native_to_real c1))
                  let mon2 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                      (Term.Rational (native_to_real c2))
                  let poly1 : Term := Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) mon1) p1
                  let poly2 : Term := Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) mon2) p2
                  by_cases hEq : vars1 = vars2
                  · subst vars2
                    have hRec :
                        bv_poly_denote M (__poly_add p1 p2) =
                          bv_poly_denote M p1 + bv_poly_denote M p2 :=
                      bv_poly_denote_of_poly_add M hp1 hp2
                    by_cases hZero :
                        native_qplus (native_to_real c1) (native_to_real c2) =
                          native_mk_rational 0 1
                    · have hZero' :
                          native_mk_rational 0 1 =
                            native_qplus (native_to_real c1) (native_to_real c2) := by
                        simpa [eq_comm] using hZero
                      have hZeroInt : native_zplus c1 c2 = 0 :=
                        (native_qplus_to_real_eq_zero_iff c1 c2).mp hZero
                      simp [__poly_add, __eo_eq, __eo_ite,
                        __eo_add, native_ite, native_teq, hZero',
                        bv_poly_denote, bv_mon_denote, native_to_int_to_real, hRec,
                        SmtEval.native_zplus] at hZeroInt ⊢
                      let v := bv_mvar_denote M vars1
                      have hCoeff : c1 * v + c2 * v = 0 := by
                        rw [← Int.add_mul, hZeroInt]
                        simp
                      calc
                        bv_poly_denote M p1 + bv_poly_denote M p2 =
                            (c1 * v + c2 * v) +
                              (bv_poly_denote M p1 + bv_poly_denote M p2) := by
                          rw [hCoeff]
                          simp
                        _ = c1 * v + bv_poly_denote M p1 +
                              (c2 * v + bv_poly_denote M p2) := by
                          ac_rfl
                    · have hTail : __poly_add p1 p2 ≠ Term.Stuck :=
                        bv_poly_int_wf_ne_stuck (bv_poly_int_wf_of_poly_add hp1 hp2)
                      have hZero' :
                          native_mk_rational 0 1 ≠
                            native_qplus (native_to_real c1) (native_to_real c2) := by
                        simpa [eq_comm] using hZero
                      simp [__poly_add, __eo_eq, __eo_ite,
                        __eo_add, native_ite, native_teq, hZero',
                        __eo_mk_apply, bv_poly_denote, bv_mon_denote,
                        native_to_int_to_real, native_to_int_qplus_to_real, hRec,
                        SmtEval.native_zplus]
                      rw [Int.add_mul]
                      ac_rfl
                  · have hEq' : vars2 ≠ vars1 := by
                      simpa [eq_comm] using hEq
                    by_cases hCmp : native_tcmp vars2 vars1
                    · have hRec :
                        bv_poly_denote M
                            (__poly_add p1
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                    (Term.Rational (native_to_real c2))))
                                p2)) =
                          bv_poly_denote M p1 +
                            bv_poly_denote M
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                    (Term.Rational (native_to_real c2))))
                                p2) :=
                      bv_poly_denote_of_poly_add M hp1
                        (bv_poly_int_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                            (Term.Rational (native_to_real c2)))
                          p2 (bv_mon_int_wf.mk vars2 c2 hvars2) hp2)
                      have hTail :
                          __poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational (native_to_real c2))))
                              p2) ≠ Term.Stuck :=
                        bv_poly_int_wf_ne_stuck
                          (bv_poly_int_wf_of_poly_add hp1
                            (bv_poly_int_wf.cons
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                (Term.Rational (native_to_real c2)))
                              p2 (bv_mon_int_wf.mk vars2 c2 hvars2) hp2))
                      simp [__poly_add, __eo_eq, __eo_ite,
                        native_teq, hEq', __eo_cmp, hCmp,
                        native_ite, __eo_mk_apply, bv_poly_denote, bv_mon_denote,
                        native_to_int_to_real, hRec]
                      ac_rfl
                    · have hRec :
                        bv_poly_denote M
                            (__poly_add
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                    (Term.Rational (native_to_real c1))))
                                p1)
                              p2) =
                          bv_poly_denote M
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                    (Term.Rational (native_to_real c1))))
                                p1) +
                            bv_poly_denote M p2 :=
                      bv_poly_denote_of_poly_add M
                        (bv_poly_int_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational (native_to_real c1)))
                          p1 (bv_mon_int_wf.mk vars1 c1 hvars1) hp1)
                        hp2
                      have hTail :
                          __poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational (native_to_real c1))))
                              p1)
                            p2 ≠ Term.Stuck :=
                        bv_poly_int_wf_ne_stuck
                          (bv_poly_int_wf_of_poly_add
                            (bv_poly_int_wf.cons
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                (Term.Rational (native_to_real c1)))
                              p1 (bv_mon_int_wf.mk vars1 c1 hvars1) hp1)
                            hp2)
                      have hCmpFalse : native_tcmp vars2 vars1 = false := by
                        cases hT : native_tcmp vars2 vars1 <;> simp [hT] at hCmp ⊢
                      simp [__poly_add, __eo_eq, __eo_ite,
                        native_teq, hEq', __eo_cmp, hCmpFalse,
                        __eo_mk_apply, bv_poly_denote, bv_mon_denote,
                        native_ite, native_to_int_to_real, hRec]
                      ac_rfl
termination_by sizeOf P1 + sizeOf P2
decreasing_by
  simp_wf
  · omega
  · have hSize :
        sizeOf p1 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational (native_to_real c1))))
              p1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf p2 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational (native_to_real c2))))
              p2) := by
        simp
        omega
    omega

private theorem bv_poly_int_wf_of_poly_mul_mon
    {m p : Term}
    (hm : bv_mon_int_wf m)
    (hp : bv_poly_int_wf p) :
  bv_poly_int_wf (__poly_mul_mon m p) := by
  have hMNe : m ≠ Term.Stuck := bv_mon_int_wf_ne_stuck hm
  induction hp with
  | zero =>
      simpa [__poly_mul_mon, hMNe] using bv_poly_int_wf.zero
  | cons m2 p2 hm2 hp2 ih =>
      have hMul : bv_mon_int_wf (__mon_mul_mon m m2) :=
        bv_mon_int_wf_of_mon_mul_mon hm hm2
      have hMulNe : __mon_mul_mon m m2 ≠ Term.Stuck :=
        bv_mon_int_wf_ne_stuck hMul
      have hHead :
          bv_poly_int_wf
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
              (Term.UOp UserOp._at__at_poly_zero)) := by
        simpa [__eo_mk_apply, hMulNe] using
          (bv_poly_int_wf.cons
            (__mon_mul_mon m m2)
            (Term.UOp UserOp._at__at_poly_zero)
            hMul
            bv_poly_int_wf.zero)
      simpa [__poly_mul_mon, hMNe] using bv_poly_int_wf_of_poly_add hHead ih

private theorem bv_poly_denote_of_poly_mul_mon
    (M : SmtModel) {m p : Term}
    (hm : bv_mon_int_wf m)
    (hp : bv_poly_int_wf p) :
  bv_poly_denote M (__poly_mul_mon m p) =
    bv_mon_denote M m * bv_poly_denote M p := by
  have hMNe : m ≠ Term.Stuck := bv_mon_int_wf_ne_stuck hm
  induction hp with
  | zero =>
      simp [__poly_mul_mon, bv_poly_denote]
  | cons m2 p2 hm2 hp2 ih =>
      have hMul : bv_mon_int_wf (__mon_mul_mon m m2) :=
        bv_mon_int_wf_of_mon_mul_mon hm hm2
      have hMulNe : __mon_mul_mon m m2 ≠ Term.Stuck :=
        bv_mon_int_wf_ne_stuck hMul
      have hHead :
          bv_poly_int_wf
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
              (Term.UOp UserOp._at__at_poly_zero)) := by
        simpa [__eo_mk_apply, hMulNe] using
          (bv_poly_int_wf.cons
            (__mon_mul_mon m m2)
            (Term.UOp UserOp._at__at_poly_zero)
            hMul
            bv_poly_int_wf.zero)
      rw [show
        __poly_mul_mon m
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m2) p2) =
          __poly_add
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
              (Term.UOp UserOp._at__at_poly_zero))
            (__poly_mul_mon m p2) by
        simp [__poly_mul_mon]]
      rw [bv_poly_denote_of_poly_add M hHead
        (bv_poly_int_wf_of_poly_mul_mon hm hp2)]
      simp [bv_poly_denote, __eo_mk_apply, bv_mon_denote_of_mon_mul_mon M hm hm2, ih]
      rw [Int.mul_add]

private theorem bv_poly_int_wf_of_poly_mul
    {p1 p2 : Term}
    (hp1 : bv_poly_int_wf p1)
    (hp2 : bv_poly_int_wf p2) :
  bv_poly_int_wf (__poly_mul p1 p2) := by
  have hP2Ne : p2 ≠ Term.Stuck := bv_poly_int_wf_ne_stuck hp2
  induction hp1 with
  | zero =>
      simpa [__poly_mul, hP2Ne] using bv_poly_int_wf.zero
  | cons m p1 hm hp1 ih =>
      simpa [__poly_mul, hP2Ne] using
        bv_poly_int_wf_of_poly_add
          (bv_poly_int_wf_of_poly_mul_mon hm hp2)
          ih

private theorem bv_poly_denote_of_poly_mul
    (M : SmtModel) {p1 p2 : Term}
    (hp1 : bv_poly_int_wf p1)
    (hp2 : bv_poly_int_wf p2) :
  bv_poly_denote M (__poly_mul p1 p2) =
    bv_poly_denote M p1 * bv_poly_denote M p2 := by
  have hP2Ne : p2 ≠ Term.Stuck := bv_poly_int_wf_ne_stuck hp2
  induction hp1 with
  | zero =>
      simp [__poly_mul, bv_poly_denote]
  | cons m p1 hm hp1 ih =>
      simp [__poly_mul, bv_poly_denote_of_poly_add M
          (bv_poly_int_wf_of_poly_mul_mon hm hp2)
          (bv_poly_int_wf_of_poly_mul hp1 hp2),
        bv_poly_denote_of_poly_mul_mon M hm hp2, ih,
        bv_poly_denote]
      rw [Int.add_mul]

private theorem bv_poly_int_wf_of_poly_mod_coeffs
    {p : Term} (m : native_Int)
    (hm0 : m ≠ 0)
    (hp : bv_poly_int_wf p) :
  bv_poly_int_wf (__poly_mod_coeffs p (Term.Numeral m)) := by
  induction hp with
  | zero =>
      rw [show
        __poly_mod_coeffs (Term.UOp UserOp._at__at_poly_zero) (Term.Numeral m) =
          Term.UOp UserOp._at__at_poly_zero by
        simp [__poly_mod_coeffs]]
      exact bv_poly_int_wf.zero
  | cons mon p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hMNeSym : 0 ≠ m := by
            intro h
            exact hm0 h.symm
          have hModNonzero : native_zeq 0 m = false := by
            simp [SmtEval.native_zeq, hMNeSym]
          by_cases hZero : c % m = 0
          · have hEq :
                __eo_eq (Term.Numeral (c % m)) (Term.Numeral 0) =
                  Term.Boolean true := by
              simp [__eo_eq, native_teq, hZero]
            have hStep :
                __poly_mod_coeffs
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_poly)
                        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                          (Term.Rational (native_to_real c))))
                      p)
                    (Term.Numeral m) =
                  __poly_mod_coeffs p (Term.Numeral m) := by
              simp [__poly_mod_coeffs, __eo_zmod, __eo_to_z, __eo_ite,
                native_ite, hModNonzero, hEq, native_to_int_to_real,
                SmtEval.native_mod_total, native_teq]
            rw [hStep]
            exact ih
          · have hEq :
                __eo_eq (Term.Numeral (c % m)) (Term.Numeral 0) =
                  Term.Boolean false := by
              have hZeroSym : 0 ≠ c % m := by
                intro h
                exact hZero h.symm
              simp [__eo_eq, native_teq, hZeroSym]
            have hTail : __poly_mod_coeffs p (Term.Numeral m) ≠ Term.Stuck :=
              bv_poly_int_wf_ne_stuck ih
            have hStep :
                __poly_mod_coeffs
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_poly)
                        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                          (Term.Rational (native_to_real c))))
                      p)
                    (Term.Numeral m) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_poly)
                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                        (Term.Rational (native_to_real (c % m)))))
                    (__poly_mod_coeffs p (Term.Numeral m)) := by
              simp [__poly_mod_coeffs, __eo_zmod, __eo_to_z, __eo_to_q, __eo_ite,
                native_ite, hModNonzero, __eo_mk_apply, hEq, native_to_int_to_real, SmtEval.native_mod_total, native_teq]
            rw [hStep]
            exact
              bv_poly_int_wf.cons
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                  (Term.Rational (native_to_real (c % m))))
                (__poly_mod_coeffs p (Term.Numeral m))
                (bv_mon_int_wf.mk vars (c % m) hvars)
                ih

private theorem bv_poly_mod_coeffs_mod_denote
    (M : SmtModel) {p : Term} {m : native_Int}
    (hm0 : m ≠ 0)
    (hp : bv_poly_int_wf p) :
  bv_poly_denote M (__poly_mod_coeffs p (Term.Numeral m)) % m =
    bv_poly_denote M p % m := by
  induction hp with
  | zero =>
      rw [show
        __poly_mod_coeffs (Term.UOp UserOp._at__at_poly_zero) (Term.Numeral m) =
          Term.UOp UserOp._at__at_poly_zero by
        simp [__poly_mod_coeffs]]
  | cons mon p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hRecWf : bv_poly_int_wf (__poly_mod_coeffs p (Term.Numeral m)) :=
            bv_poly_int_wf_of_poly_mod_coeffs m hm0 hp
          have hMNeSym : 0 ≠ m := by
            intro h
            exact hm0 h.symm
          have hModNonzero : native_zeq 0 m = false := by
            simp [SmtEval.native_zeq, hMNeSym]
          by_cases hZero : c % m = 0
          · have hEq :
                __eo_eq (Term.Numeral (c % m)) (Term.Numeral 0) =
                  Term.Boolean true := by
              simp [__eo_eq, native_teq, hZero]
            have hStep :
                __poly_mod_coeffs
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_poly)
                        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                          (Term.Rational (native_to_real c))))
                      p)
                    (Term.Numeral m) =
                  __poly_mod_coeffs p (Term.Numeral m) := by
              simp [__poly_mod_coeffs, __eo_zmod, __eo_to_z, __eo_ite,
                native_ite, hModNonzero, hEq, native_to_int_to_real,
                SmtEval.native_mod_total, native_teq]
            rw [hStep]
            simp [bv_poly_denote, bv_mon_denote, native_to_int_to_real]
            calc
              bv_poly_denote M (__poly_mod_coeffs p (Term.Numeral m)) % m =
                  bv_poly_denote M p % m := ih
              _ = (c * bv_mvar_denote M vars + bv_poly_denote M p) % m := by
                have hMulZero : (c * bv_mvar_denote M vars) % m = 0 := by
                  rw [← emod_mul_left_congr c (bv_mvar_denote M vars) m]
                  rw [hZero]
                  simp
                calc
                    bv_poly_denote M p % m =
                        (0 + bv_poly_denote M p) % m := by simp
                    _ = ((c * bv_mvar_denote M vars) + bv_poly_denote M p) % m := by
                      exact (emod_add_congr hMulZero rfl).symm
          · have hEq :
                __eo_eq (Term.Numeral (c % m)) (Term.Numeral 0) =
                  Term.Boolean false := by
              have hZeroSym : 0 ≠ c % m := by
                intro h
                exact hZero h.symm
              simp [__eo_eq, native_teq, hZeroSym]
            have hTail : __poly_mod_coeffs p (Term.Numeral m) ≠ Term.Stuck :=
              bv_poly_int_wf_ne_stuck hRecWf
            have hStep :
                __poly_mod_coeffs
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_poly)
                        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                          (Term.Rational (native_to_real c))))
                      p)
                    (Term.Numeral m) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_poly)
                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                        (Term.Rational (native_to_real (c % m)))))
                    (__poly_mod_coeffs p (Term.Numeral m)) := by
              simp [__poly_mod_coeffs, __eo_zmod, __eo_to_z, __eo_to_q, __eo_ite,
                native_ite, hModNonzero, __eo_mk_apply, hEq, native_to_int_to_real, SmtEval.native_mod_total, native_teq]
            rw [hStep]
            simp [bv_poly_denote, bv_mon_denote, native_to_int_to_real]
            exact emod_add_congr (emod_mul_left_congr c (bv_mvar_denote M vars) m) ih

private theorem model_eval_bitvec_payload
    (M : SmtModel) (hM : model_wf M) (t : Term) (w : native_Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    ∃ n : native_Int,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary (native_nat_to_int w) n ∧
      0 <= n ∧ n < native_int_pow2 (native_nat_to_int w) := by
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.BitVec w := by
    simpa [hTy] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hNN
  rcases Smtm.bitvec_value_canonical hEvalTy with ⟨n, hv⟩
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    exact Smtm.bitvec_width_nonneg (by simpa [hv] using hEvalTy)
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true := by
    exact Smtm.bitvec_payload_canonical (by simpa [hv] using hEvalTy)
  have hRange := Smtm.bitvec_payload_range_of_canonical hWidth hMod
  exact ⟨n, hv, hRange⟩

private theorem bvneg_arg_of_bitvec_type (x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x)) =
      SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvneg (__eo_to_smt x)) =
        SmtType.BitVec w := by
    rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x) =
      SmtTerm.bvneg (__eo_to_smt x) by rfl] at hTy
    exact hTy
  have hNN : term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_unop_arg_of_non_none (op := SmtTerm.bvneg)
      (show __smtx_typeof (SmtTerm.bvneg (__eo_to_smt x)) =
        __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_47]) hNN with ⟨w', hx⟩
  have hWidth : w' = w := by
    have hResult : SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show __smtx_typeof (SmtTerm.bvneg (__eo_to_smt x)) =
        __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_47]] at hTy'
      simpa [__smtx_typeof_bv_op_1, hx] using hTy'
    cases hResult
    rfl
  subst w'
  exact hx

private theorem bvadd_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x)) =
      SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x) =
      SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt x) by rfl] at hTy
    exact hTy
  have hNN : term_has_non_none_type (SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvadd)
      (show __smtx_typeof (SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_48]) hNN with ⟨w', hy, hx⟩
  have hWidth : w' = w := by
    have hResult : SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show __smtx_typeof (SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_48]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hy, hx, native_ite, native_nateq,
        SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hy, hx⟩

private theorem bvmul_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
      SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x) =
      SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x) by rfl] at hTy
    exact hTy
  have hNN : term_has_non_none_type (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvmul)
      (show __smtx_typeof (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_49]) hNN with ⟨w', hy, hx⟩
  have hWidth : w' = w := by
    have hResult : SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show __smtx_typeof (SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_49]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hy, hx, native_ite, native_nateq,
        SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hy, hx⟩

private theorem bvsub_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) =
      SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x) =
      SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x) by rfl] at hTy
    exact hTy
  have hNN : term_has_non_none_type (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvsub)
      (show __smtx_typeof (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_52]) hNN with ⟨w', hy, hx⟩
  have hWidth : w' = w := by
    have hResult : SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show __smtx_typeof (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_52]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hy, hx, native_ite, native_nateq,
        SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hy, hx⟩

private theorem bv_atom_denote_bvneg_mod
    (M : SmtModel) (hM : model_wf M) (x : Term) (w : native_Nat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x)) =
      SmtType.BitVec w) :
  bv_atom_denote M (Term.Apply (Term.UOp UserOp.bvneg) x) %
      native_int_pow2 (native_nat_to_int w) =
    (- bv_atom_denote M x) % native_int_pow2 (native_nat_to_int w) := by
  have hxTy := bvneg_arg_of_bitvec_type x w hTy
  rcases model_eval_bitvec_payload M hM x w hxTy with ⟨nx, hxEval, _⟩
  simp [bv_atom_denote]
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x) =
      SmtTerm.bvneg (__eo_to_smt x) by rfl]
  rw [__smtx_model_eval.eq_47, hxEval]
  simp [__smtx_model_eval_bvneg, SmtEval.native_zneg,
    SmtEval.native_mod_total]

private theorem bv_atom_denote_bvadd_mod
    (M : SmtModel) (hM : model_wf M) (y x : Term) (w : native_Nat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x)) =
      SmtType.BitVec w) :
  bv_atom_denote M (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x) %
      native_int_pow2 (native_nat_to_int w) =
    (bv_atom_denote M y + bv_atom_denote M x) % native_int_pow2 (native_nat_to_int w) := by
  rcases bvadd_args_of_bitvec_type y x w hTy with ⟨hyTy, hxTy⟩
  rcases model_eval_bitvec_payload M hM y w hyTy with ⟨ny, hyEval, _⟩
  rcases model_eval_bitvec_payload M hM x w hxTy with ⟨nx, hxEval, _⟩
  simp [bv_atom_denote]
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x) =
      SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt x) by rfl]
  rw [__smtx_model_eval.eq_48, hyEval, hxEval]
  simp [__smtx_model_eval_bvadd, SmtEval.native_zplus,
    SmtEval.native_mod_total]

private theorem bv_atom_denote_bvmul_mod
    (M : SmtModel) (hM : model_wf M) (y x : Term) (w : native_Nat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
      SmtType.BitVec w) :
  bv_atom_denote M (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x) %
      native_int_pow2 (native_nat_to_int w) =
    (bv_atom_denote M y * bv_atom_denote M x) % native_int_pow2 (native_nat_to_int w) := by
  rcases bvmul_args_of_bitvec_type y x w hTy with ⟨hyTy, hxTy⟩
  rcases model_eval_bitvec_payload M hM y w hyTy with ⟨ny, hyEval, _⟩
  rcases model_eval_bitvec_payload M hM x w hxTy with ⟨nx, hxEval, _⟩
  simp [bv_atom_denote]
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x) =
      SmtTerm.bvmul (__eo_to_smt y) (__eo_to_smt x) by rfl]
  rw [__smtx_model_eval.eq_49, hyEval, hxEval]
  simp [__smtx_model_eval_bvmul, SmtEval.native_zmult,
    SmtEval.native_mod_total]

private theorem bv_atom_denote_bvsub_mod
    (M : SmtModel) (hM : model_wf M) (y x : Term) (w : native_Nat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) =
      SmtType.BitVec w) :
  bv_atom_denote M (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x) %
      native_int_pow2 (native_nat_to_int w) =
    (bv_atom_denote M y + - bv_atom_denote M x) %
      native_int_pow2 (native_nat_to_int w) := by
  rcases bvsub_args_of_bitvec_type y x w hTy with ⟨hyTy, hxTy⟩
  rcases model_eval_bitvec_payload M hM y w hyTy with ⟨ny, hyEval, _⟩
  rcases model_eval_bitvec_payload M hM x w hxTy with ⟨nx, hxEval, _⟩
  simp [bv_atom_denote]
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x) =
      SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x) by rfl]
  rw [__smtx_model_eval.eq_52, hyEval, hxEval]
  simp [__smtx_model_eval_bvsub, __smtx_model_eval_bvadd, __smtx_model_eval_bvneg,
    SmtEval.native_zplus, SmtEval.native_zneg,
    SmtEval.native_mod_total]

private theorem bv_poly_norm_rec_sound
    (M : SmtModel) (hM : model_wf M) :
    (t : Term) -> (w : native_Nat) ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    bv_poly_int_wf (__get_bv_poly_norm_rec t) ∧
      bv_poly_denote M (__get_bv_poly_norm_rec t) %
          native_int_pow2 (native_nat_to_int w) =
        bv_atom_denote M t % native_int_pow2 (native_nat_to_int w) := by
  let rec go (t : Term) (w : native_Nat)
      (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
      bv_poly_int_wf (__get_bv_poly_norm_rec t) ∧
        bv_poly_denote M (__get_bv_poly_norm_rec t) %
            native_int_pow2 (native_nat_to_int w) =
          bv_atom_denote M t % native_int_pow2 (native_nat_to_int w) := by
    have fallback
        (hNorm : __get_bv_poly_norm_rec t = bv_var_poly t) :
        bv_poly_int_wf (__get_bv_poly_norm_rec t) ∧
          bv_poly_denote M (__get_bv_poly_norm_rec t) %
              native_int_pow2 (native_nat_to_int w) =
            bv_atom_denote M t % native_int_pow2 (native_nat_to_int w) := by
      have hNotStuck : t ≠ Term.Stuck := bv_atom_ne_stuck_of_smt_bitvec_type hTy
      refine ⟨?_, ?_⟩
      · rw [hNorm]
        exact bv_poly_int_wf_var hNotStuck
      · rw [hNorm, bv_poly_denote_var]
    cases hEq : t with
    | UOp op =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | UOp1 op a =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | UOp2 op a b =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | UOp3 op a b c =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | __eo_List =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | __eo_List_nil =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | __eo_List_cons =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | Bool =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | Boolean b =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | Numeral n =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | Rational q =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | String s =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | Binary bw n =>
        by_cases hn : n = 0
        · subst n
          have hNorm :
              __get_bv_poly_norm_rec (Term.Binary bw 0) =
                Term.UOp UserOp._at__at_poly_zero := by
            simp [__get_bv_poly_norm_rec, __eo_to_z, __eo_is_bin, __eo_is_bin_internal,
              __eo_is_eq, __eo_ite, native_ite, native_teq, SmtEval.native_and,
              SmtEval.native_not]
          refine ⟨?_, ?_⟩
          · rw [hNorm]
            exact bv_poly_int_wf.zero
          · rw [hNorm]
            have hAtom : bv_atom_denote M (Term.Binary bw 0) = 0 := by
              unfold bv_atom_denote
              rw [show __eo_to_smt (Term.Binary bw 0) = SmtTerm.Binary bw 0 by rfl]
              rw [__smtx_model_eval.eq_5]
            change 0 % native_int_pow2 (native_nat_to_int w) =
              bv_atom_denote M (Term.Binary bw 0) % native_int_pow2 (native_nat_to_int w)
            rw [hAtom]
        · have hZeroSym : ¬ 0 = n := by
            intro h
            exact hn h.symm
          let p :=
            Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) Term.__eo_List_nil)
                  (Term.Rational (native_to_real n))))
              (Term.UOp UserOp._at__at_poly_zero)
          have hNorm : __get_bv_poly_norm_rec (Term.Binary bw n) = p := by
            simp [__get_bv_poly_norm_rec, __eo_to_z, __eo_is_bin, __eo_is_bin_internal,
              __eo_is_eq, __eo_ite, native_ite, native_teq, hZeroSym, SmtEval.native_and,
              SmtEval.native_not, __eo_mk_apply, __eo_to_q, p]
          refine ⟨?_, ?_⟩
          · rw [hNorm]
            exact bv_poly_int_wf.cons
              (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) Term.__eo_List_nil)
                (Term.Rational (native_to_real n)))
              (Term.UOp UserOp._at__at_poly_zero)
              (bv_mon_int_wf.mk Term.__eo_List_nil n bv_mvar_wf.nil)
              bv_poly_int_wf.zero
          · rw [hNorm]
            have hDenP : bv_poly_denote M p = n := by
              simp [p, bv_poly_denote, bv_mon_denote, bv_mvar_denote,
                native_to_int_to_real]
            have hAtom : bv_atom_denote M (Term.Binary bw n) = n := by
              unfold bv_atom_denote
              rw [show __eo_to_smt (Term.Binary bw n) = SmtTerm.Binary bw n by rfl]
              rw [__smtx_model_eval.eq_5]
            rw [hDenP, hAtom]
    | «Type» =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | Stuck =>
        exfalso
        have hBad : __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.BitVec w := by
          simpa [hEq] using hTy
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hBad
        cases hBad
    | Apply f x =>
        cases f
        case UOp op =>
          by_cases hNeg : op = UserOp.bvneg
          · subst op
            have hxTy := bvneg_arg_of_bitvec_type x w (by simpa [hEq] using hTy)
            rcases go x w hxTy with ⟨hWfX, hRecX⟩
            have hWf :
                bv_poly_int_wf (__get_bv_poly_norm_rec (Term.Apply (Term.UOp UserOp.bvneg) x)) :=
              by simpa [__get_bv_poly_norm_rec] using bv_poly_int_wf_of_poly_neg hWfX
            refine ⟨hWf, ?_⟩
            have hDen :
                bv_poly_denote M
                    (__get_bv_poly_norm_rec (Term.Apply (Term.UOp UserOp.bvneg) x)) =
                  - bv_poly_denote M (__get_bv_poly_norm_rec x) := by
              simpa [__get_bv_poly_norm_rec] using bv_poly_denote_of_poly_neg M hWfX
            rw [hDen]
            calc
              (-bv_poly_denote M (__get_bv_poly_norm_rec x)) %
                  native_int_pow2 (native_nat_to_int w) =
                (-bv_atom_denote M x) % native_int_pow2 (native_nat_to_int w) :=
                  emod_neg_congr hRecX
              _ =
                bv_atom_denote M (Term.Apply (Term.UOp UserOp.bvneg) x) %
                  native_int_pow2 (native_nat_to_int w) :=
                  (bv_atom_denote_bvneg_mod M hM x w (by simpa [hEq] using hTy)).symm
          · simpa [hEq] using fallback (by
              simp [hEq, __get_bv_poly_norm_rec, hNeg, __eo_is_bin,
                __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not, bv_var_poly])
        case Apply g y =>
          cases g
          case UOp op =>
            by_cases hAdd : op = UserOp.bvadd
            · subst op
              have hTy' :
                  __smtx_typeof (__eo_to_smt
                    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x)) =
                    SmtType.BitVec w := by simpa [hEq] using hTy
              rcases bvadd_args_of_bitvec_type y x w hTy' with ⟨hyTy, hxTy⟩
              rcases go y w hyTy with ⟨hWfY, hRecY⟩
              rcases go x w hxTy with ⟨hWfX, hRecX⟩
              have hWf : bv_poly_int_wf
                  (__get_bv_poly_norm_rec
                    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x)) := by
                simpa [__get_bv_poly_norm_rec] using
                  bv_poly_int_wf_of_poly_add hWfY hWfX
              refine ⟨hWf, ?_⟩
              have hDen :
                  bv_poly_denote M
                      (__get_bv_poly_norm_rec
                        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x)) =
                    bv_poly_denote M (__get_bv_poly_norm_rec y) +
                      bv_poly_denote M (__get_bv_poly_norm_rec x) := by
                simpa [__get_bv_poly_norm_rec] using
                  bv_poly_denote_of_poly_add M hWfY hWfX
              rw [hDen]
              exact (emod_add_congr hRecY hRecX).trans
                (bv_atom_denote_bvadd_mod M hM y x w hTy').symm
            · by_cases hSub : op = UserOp.bvsub
              · subst op
                have hTy' :
                    __smtx_typeof (__eo_to_smt
                      (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) =
                      SmtType.BitVec w := by simpa [hEq] using hTy
                rcases bvsub_args_of_bitvec_type y x w hTy' with ⟨hyTy, hxTy⟩
                rcases go y w hyTy with ⟨hWfY, hRecY⟩
                rcases go x w hxTy with ⟨hWfX, hRecX⟩
                have hNegWf := bv_poly_int_wf_of_poly_neg hWfX
                have hWf : bv_poly_int_wf
                    (__get_bv_poly_norm_rec
                      (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) := by
                  simpa [__get_bv_poly_norm_rec] using
                    bv_poly_int_wf_of_poly_add hWfY hNegWf
                refine ⟨hWf, ?_⟩
                have hDen :
                    bv_poly_denote M
                        (__get_bv_poly_norm_rec
                          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) =
                      bv_poly_denote M (__get_bv_poly_norm_rec y) +
                        - bv_poly_denote M (__get_bv_poly_norm_rec x) := by
                  have hDen' :
                      bv_poly_denote M
                          (__poly_add (__get_bv_poly_norm_rec y)
                            (__poly_neg (__get_bv_poly_norm_rec x))) =
                        bv_poly_denote M (__get_bv_poly_norm_rec y) +
                          - bv_poly_denote M (__get_bv_poly_norm_rec x) := by
                    rw [bv_poly_denote_of_poly_add M hWfY hNegWf,
                      bv_poly_denote_of_poly_neg M hWfX]
                  simpa [__get_bv_poly_norm_rec] using hDen'
                rw [hDen]
                exact (emod_add_congr hRecY (emod_neg_congr hRecX)).trans
                  (bv_atom_denote_bvsub_mod M hM y x w hTy').symm
              · by_cases hMul : op = UserOp.bvmul
                · subst op
                  have hTy' :
                      __smtx_typeof (__eo_to_smt
                        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
                        SmtType.BitVec w := by simpa [hEq] using hTy
                  rcases bvmul_args_of_bitvec_type y x w hTy' with ⟨hyTy, hxTy⟩
                  rcases go y w hyTy with ⟨hWfY, hRecY⟩
                  rcases go x w hxTy with ⟨hWfX, hRecX⟩
                  have hWf : bv_poly_int_wf
                      (__get_bv_poly_norm_rec
                        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) := by
                    simpa [__get_bv_poly_norm_rec] using
                      bv_poly_int_wf_of_poly_mul hWfY hWfX
                  refine ⟨hWf, ?_⟩
                  have hDen :
                      bv_poly_denote M
                          (__get_bv_poly_norm_rec
                            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
                        bv_poly_denote M (__get_bv_poly_norm_rec y) *
                          bv_poly_denote M (__get_bv_poly_norm_rec x) := by
                    simpa [__get_bv_poly_norm_rec] using
                      bv_poly_denote_of_poly_mul M hWfY hWfX
                  rw [hDen]
                  exact (emod_mul_congr hRecY hRecX).trans
                    (bv_atom_denote_bvmul_mod M hM y x w hTy').symm
                · simpa [hEq] using fallback (by
                    simp [hEq, __get_bv_poly_norm_rec, hAdd, hSub, hMul,
                      __eo_is_bin, __eo_is_bin_internal, __eo_ite,
                      native_ite, native_teq, SmtEval.native_and, SmtEval.native_not,
                      bv_var_poly])
          all_goals
            simpa [hEq] using fallback (by
              simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
                __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not, bv_var_poly])
        all_goals
          simpa [hEq] using fallback (by
            simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
              __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
              SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | FunType =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | Var a b =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | DatatypeType s d =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | DatatypeTypeRef s =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | DtcAppType a b =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | DtCons s d i =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | DtSel s d i j =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | USort i =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
    | UConst i a =>
        simpa [hEq] using fallback (by
          simp [hEq, __get_bv_poly_norm_rec, __eo_is_bin,
            __eo_is_bin_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not, bv_var_poly])
  exact go

private theorem poly_mod_coeffs_ne_stuck_right
    {p w : Term} :
  __poly_mod_coeffs p w ≠ Term.Stuck ->
  w ≠ Term.Stuck := by
  intro h
  intro hw
  subst w
  simp [__poly_mod_coeffs] at h

private theorem bv_modulus_ne_stuck_bitwidth_ne_stuck
    {bw modulus : Term}
    (hModulus :
      modulus =
        __eo_ite (__eo_is_z bw)
          (__eo_ite (__eo_is_neg bw) (Term.Numeral 0) (__eo_pow (Term.Numeral 2) bw))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) bw))
    (hNe : modulus ≠ Term.Stuck) :
  bw ≠ Term.Stuck := by
  subst modulus
  intro hBw
  subst bw
  simp [__eo_is_z, __eo_is_z_internal, __eo_ite, native_ite,
    native_teq, SmtEval.native_and, SmtEval.native_not, __eo_mk_apply] at hNe

private theorem bv_bitwidth_ne_stuck_shape
    {T : Term} :
  __bv_bitwidth T ≠ Term.Stuck ->
  ∃ n, T = Term.Apply (Term.UOp UserOp.BitVec) n := by
  intro h
  cases T <;> try (exfalso; apply h; rfl)
  case Apply f n =>
    cases f <;> try (exfalso; apply h; rfl)
    case UOp op =>
      cases op <;> try (exfalso; apply h; rfl)
      exact ⟨n, rfl⟩

private theorem smt_bitvec_type_of_bv_bitwidth_ne_stuck
    (a : Term)
    (hTyNonNone : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None)
    (hBw : __bv_bitwidth (__eo_typeof a) ≠ Term.Stuck) :
  ∃ w : native_Nat, __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w := by
  rcases bv_bitwidth_ne_stuck_shape hBw with ⟨n, hEoTy⟩
  have hTransTy :
      __eo_to_smt_type (__eo_typeof a) = __smtx_typeof (__eo_to_smt a) :=
    TranslationProofs.eo_to_smt_type_typeof_of_smt_type a
      (by rfl) hTyNonNone
  rw [hEoTy] at hTransTy
  have hNumOrNone :
      (∃ k, n = Term.Numeral k) ∨
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) n) = SmtType.None := by
    cases n <;> simp [__eo_to_smt_type]
  rcases hNumOrNone with ⟨k, hk⟩ | hNone
  · subst n
    by_cases hk : 0 <= k
    · refine ⟨native_int_to_nat k, ?_⟩
      simpa [__eo_to_smt_type, SmtEval.native_zleq, hk, native_ite] using hTransTy.symm
    · exfalso
      have hNone : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k)) =
          SmtType.None := by
        simp [__eo_to_smt_type, SmtEval.native_zleq, hk, native_ite]
      rw [hNone] at hTransTy
      exact hTyNonNone hTransTy.symm
  · exfalso
    rw [hNone] at hTransTy
    exact hTyNonNone hTransTy.symm

private theorem prog_bv_poly_norm_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_bv_poly_norm a1) = Term.Bool ->
  __eo_prog_bv_poly_norm a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_bv_poly_norm a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1
  case Apply f b =>
    cases f
    case Apply g a =>
      cases g
      case UOp op =>
        by_cases hOp : op = UserOp.eq
        · subst op
          let bw := __bv_bitwidth (__eo_typeof a)
          let modulus :=
            __eo_ite (__eo_is_z bw)
              (__eo_ite (__eo_is_neg bw) (Term.Numeral 0) (__eo_pow (Term.Numeral 2) bw))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2) bw)
          let nA := __poly_mod_coeffs (__get_bv_poly_norm_rec a) modulus
          let nB := __poly_mod_coeffs (__get_bv_poly_norm_rec b) modulus
          have hReq :
              __eo_requires (__eo_eq nA nB) (Term.Boolean true)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ≠ Term.Stuck := by
            simpa [__eo_prog_bv_poly_norm, bw, modulus, nA, nB] using hProg
          have hGuard : __eo_eq nA nB = Term.Boolean true :=
            eo_requires_arg_eq_of_ne_stuck hReq
          change __eo_requires (__eo_eq nA nB) (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
              Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b
          simp [__eo_requires, hGuard, native_teq, native_ite,
            native_not, SmtEval.native_not]
        · exfalso
          apply hProg
          simp [__eo_prog_bv_poly_norm, hOp]
      all_goals
        exfalso
        apply hProg
        simp [__eo_prog_bv_poly_norm]
    all_goals
      exfalso
      apply hProg
      simp [__eo_prog_bv_poly_norm]
  all_goals
    exfalso
    apply hProg
    simp [__eo_prog_bv_poly_norm]

private theorem eq_args_of_prog_bv_poly_norm_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_bv_poly_norm a1) = Term.Bool ->
  ∃ a b modulus,
    a1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b ∧
    modulus =
      __eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof a)))
        (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof a))) (Term.Numeral 0)
          (__eo_pow (Term.Numeral 2) (__bv_bitwidth (__eo_typeof a))))
        (__eo_mk_apply (Term.UOp UserOp.int_pow2) (__bv_bitwidth (__eo_typeof a))) ∧
    __poly_mod_coeffs (__get_bv_poly_norm_rec a) modulus =
      __poly_mod_coeffs (__get_bv_poly_norm_rec b) modulus ∧
    __poly_mod_coeffs (__get_bv_poly_norm_rec a) modulus ≠ Term.Stuck := by
  intro hTy
  have hProg : __eo_prog_bv_poly_norm a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1
  case Apply f b =>
    cases f
    case Apply g a =>
      cases g
      case UOp op =>
        by_cases hOp : op = UserOp.eq
        · subst op
          let bw := __bv_bitwidth (__eo_typeof a)
          let modulus :=
            __eo_ite (__eo_is_z bw)
              (__eo_ite (__eo_is_neg bw) (Term.Numeral 0) (__eo_pow (Term.Numeral 2) bw))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2) bw)
          let nA := __poly_mod_coeffs (__get_bv_poly_norm_rec a) modulus
          let nB := __poly_mod_coeffs (__get_bv_poly_norm_rec b) modulus
          have hReq :
              __eo_requires (__eo_eq nA nB) (Term.Boolean true)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ≠ Term.Stuck := by
            simpa [__eo_prog_bv_poly_norm, bw, modulus, nA, nB] using hProg
          have hGuard : __eo_eq nA nB = Term.Boolean true :=
            eo_requires_arg_eq_of_ne_stuck hReq
          have hNormEq : nA = nB := eo_eq_true_eq hGuard
          have hNormNotStuck : nA ≠ Term.Stuck := by
            intro hSt
            have hGuard' := hGuard
            rw [hSt] at hGuard'
            cases nB <;> simp [__eo_eq] at hGuard'
          exact ⟨a, b, modulus, rfl, rfl, by simpa [nA, nB] using hNormEq,
            by simpa [nA] using hNormNotStuck⟩
        · exfalso
          apply hProg
          simp [__eo_prog_bv_poly_norm, hOp]
      all_goals
        exfalso
        apply hProg
        simp [__eo_prog_bv_poly_norm]
    all_goals
      exfalso
      apply hProg
      simp [__eo_prog_bv_poly_norm]
  all_goals
    exfalso
    apply hProg
    simp [__eo_prog_bv_poly_norm]

theorem typed___eo_prog_bv_poly_norm_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_bv_poly_norm a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_bv_poly_norm a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_bv_poly_norm a1 = a1 :=
    prog_bv_poly_norm_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem smt_value_rel_of_equal_bv_poly_norm
    (M : SmtModel) (hM : model_wf M)
    (a b modulus : Term) :
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  modulus =
    __eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof a)))
      (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof a))) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) (__bv_bitwidth (__eo_typeof a))))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) (__bv_bitwidth (__eo_typeof a))) ->
  __poly_mod_coeffs (__get_bv_poly_norm_rec a) modulus =
    __poly_mod_coeffs (__get_bv_poly_norm_rec b) modulus ->
  __poly_mod_coeffs (__get_bv_poly_norm_rec a) modulus ≠ Term.Stuck ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqBool hModulus hNormEq hNormNotStuck
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
    ⟨hTyAB, hATypeNonNone⟩
  have hModulusNe : modulus ≠ Term.Stuck :=
    poly_mod_coeffs_ne_stuck_right hNormNotStuck
  have hBwNe : __bv_bitwidth (__eo_typeof a) ≠ Term.Stuck :=
    bv_modulus_ne_stuck_bitwidth_ne_stuck hModulus hModulusNe
  rcases smt_bitvec_type_of_bv_bitwidth_ne_stuck a hATypeNonNone hBwNe with
    ⟨w, hATy⟩
  have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w := by
    rw [← hTyAB]
    exact hATy
  rcases model_eval_bitvec_payload M hM a w hATy with ⟨na, hAEval, hARange⟩
  rcases model_eval_bitvec_payload M hM b w hBTy with ⟨nb, hBEval, hBRange⟩
  have hSoundA := bv_poly_norm_rec_sound M hM a w hATy
  have hSoundB := bv_poly_norm_rec_sound M hM b w hBTy
  let m := native_int_pow2 (native_nat_to_int w)
  have hm0 : m ≠ 0 := by
    exact Int.ne_of_gt (by simpa [m] using native_int_pow2_pos_nat w)
  have hModulusEq : modulus = Term.Numeral m := by
    have hEoTy :
        __eo_typeof a =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) := by
      have hTransTy :
          __eo_to_smt_type (__eo_typeof a) = SmtType.BitVec w :=
        TranslationProofs.eo_to_smt_type_typeof_of_smt_type a hATy (by simp)
      exact TranslationProofs.eo_to_smt_type_eq_bitvec hTransTy
    rw [hModulus, hEoTy]
    have hwNonneg : 0 <= native_nat_to_int w := by
      simp [native_nat_to_int]
    have hwNotNeg : ¬ native_nat_to_int w < 0 := by
      simp [native_nat_to_int]
    simp [__bv_bitwidth, __eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
      __eo_ite, native_ite, native_teq, SmtEval.native_and, SmtEval.native_not,
      SmtEval.native_zlt, native_int_pow2, native_zexp_total, hwNotNeg, m]
  rw [hModulusEq] at hNormEq hNormNotStuck
  change __poly_mod_coeffs (__get_bv_poly_norm_rec a) (Term.Numeral m) =
      __poly_mod_coeffs (__get_bv_poly_norm_rec b) (Term.Numeral m) at hNormEq
  have hModDenEq :
      bv_poly_denote M (__poly_mod_coeffs (__get_bv_poly_norm_rec a) (Term.Numeral m)) =
        bv_poly_denote M (__poly_mod_coeffs (__get_bv_poly_norm_rec b) (Term.Numeral m)) := by
    rw [hNormEq]
  have hNormModEq :
      bv_poly_denote M (__get_bv_poly_norm_rec a) % m =
        bv_poly_denote M (__get_bv_poly_norm_rec b) % m := by
    calc
        bv_poly_denote M (__get_bv_poly_norm_rec a) % m =
            bv_poly_denote M (__poly_mod_coeffs (__get_bv_poly_norm_rec a) (Term.Numeral m)) % m :=
          (bv_poly_mod_coeffs_mod_denote M hm0 hSoundA.1).symm
        _ = bv_poly_denote M (__poly_mod_coeffs (__get_bv_poly_norm_rec b) (Term.Numeral m)) % m := by
          rw [hModDenEq]
        _ = bv_poly_denote M (__get_bv_poly_norm_rec b) % m :=
          bv_poly_mod_coeffs_mod_denote M hm0 hSoundB.1
  have hPayloadMod : na % m = nb % m := by
    have hAtomA : bv_atom_denote M a = na := by
      simp [bv_atom_denote, hAEval]
    have hAtomB : bv_atom_denote M b = nb := by
      simp [bv_atom_denote, hBEval]
    calc
      na % m = bv_poly_denote M (__get_bv_poly_norm_rec a) % m := by
        rw [← hAtomA]
        exact hSoundA.2.symm
      _ = bv_poly_denote M (__get_bv_poly_norm_rec b) % m := hNormModEq
      _ = nb % m := by
        rw [← hAtomB]
        exact hSoundB.2
  have hPayloadEq : na = nb := by
    have hAmod : na % m = na := by
      simpa [m] using Int.emod_eq_of_lt hARange.1 hARange.2
    have hBmod : nb % m = nb := by
      simpa [m] using Int.emod_eq_of_lt hBRange.1 hBRange.2
    simpa [hAmod, hBmod] using hPayloadMod
  simpa [hAEval, hBEval, hPayloadEq] using
    RuleProofs.smt_value_rel_refl (SmtValue.Binary (native_nat_to_int w) na)

theorem facts___eo_prog_bv_poly_norm_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_bv_poly_norm a1) = Term.Bool ->
  eo_interprets M (__eo_prog_bv_poly_norm a1) true := by
  intro hA1Trans hResultTy
  obtain ⟨a, b, modulus, rfl, hModulus, hNormEq, hNormNotStuck⟩ :=
    eq_args_of_prog_bv_poly_norm_typeof_bool a1 hResultTy
  have hProgEq :
      __eo_prog_bv_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b :=
    prog_bv_poly_norm_eq_arg_of_typeof_bool
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) hResultTy
  have hEqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hEqBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) hA1Trans hEqTy
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M a b hEqBool
    (smt_value_rel_of_equal_bv_poly_norm M hM a b modulus
      hEqBool hModulus hNormEq hNormNotStuck)

public theorem cmd_step_bv_poly_norm_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_poly_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_poly_norm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_poly_norm args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_poly_norm args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              let A1 := a1
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons A1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation A1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_bv_poly_norm A1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_bv_poly_norm A1) true
                exact facts___eo_prog_bv_poly_norm_impl M hM A1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_bv_poly_norm A1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_bv_poly_norm A1)
                  (typed___eo_prog_bv_poly_norm_impl A1 hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
