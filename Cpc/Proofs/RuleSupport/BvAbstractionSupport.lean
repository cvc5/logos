module

public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport
import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
import Lean.Elab.Tactic.Omega
import Init.GrindInstances.Ring.BitVec

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction

theorem mul_lsb {w : Nat} (x s : BitVec w) :
    (x * s).getLsbD 0 = (x.getLsbD 0 && s.getLsbD 0) := by
  -- The width-zero case is degenerate; otherwise multiplication at width one is conjunction.
  by_cases hw : 1 ≤ w
  · have hmul : (x * s).setWidth 1 = x.setWidth 1 &&& s.setWidth 1 := by
      rw [BitVec.setWidth_mul x s hw, BitVec.mul_eq_and]
    have := congrArg (fun z : BitVec 1 => z.getLsbD 0) hmul
    simpa using this
  · have hw0 : w = 0 := by omega
    subst w
    simp [BitVec.eq_nil x, BitVec.eq_nil s]
theorem udiv1 {w : Nat} (x s t : BitVec w) (i : Nat)
    (hs : s = BitVec.twoPow w i) (hi : i < w)
    (h : x.smtUDiv s = t) : t = x >>> i := by
  subst s
  subst t
  have hp : BitVec.twoPow w i ≠ 0#w := by
    intro h
    have := congrArg BitVec.toNat h
    simp [BitVec.toNat_twoPow_of_lt hi] at this
  rw [BitVec.smtUDiv_eq, if_neg hp]
  exact BitVec.udiv_twoPow_eq_of_lt hi

theorem mul1 {w : Nat} (x s t : BitVec w) (i : Nat)
    (hs : s = BitVec.twoPow w i) (h : x * s = t) :
    t = x <<< i := by
  subst s
  subst t
  exact BitVec.mul_twoPow_eq_shiftLeft x i

theorem mul2 {w : Nat} (x s t : BitVec w) (i : Nat)
    (hs : s = -BitVec.twoPow w i) (h : x * s = t) :
    t = (-x) <<< i := by
  subst s
  subst t
  simp [BitVec.shiftLeft_neg]

theorem udiv37 {w : Nat} (x s t : BitVec w)
    (hs : s = 1#w) (h : x.smtUDiv s = t) : t = x := by
  subst s
  subst t
  cases w with
  | zero => exact Subsingleton.elim _ _
  | succ w =>
      have hOne : (1#(w + 1)) ≠ 0#(w + 1) := by simp
      rw [BitVec.smtUDiv_eq, if_neg hOne, BitVec.udiv_one]

theorem urem2 {w : Nat} (x s t : BitVec w)
    (hs : s ≠ 0#w) (h : x % s = t) : t < s := by
  subst t
  exact BitVec.umod_lt x (by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod]
    exact Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs))
def low3 {w : Nat} (x : BitVec w) : BitVec 3 := x.setWidth 3

theorem low3_mul {w : Nat} (hw : 3 ≤ w) (x y : BitVec w) :
    low3 (x * y) = low3 x * low3 y := by
  exact BitVec.setWidth_mul x y hw

theorem low3_add {w : Nat} (hw : 3 ≤ w) (x y : BitVec w) :
    low3 (x + y) = low3 x + low3 y := by
  exact BitVec.setWidth_add x y hw

theorem low3_not {w : Nat} (hw : 3 ≤ w) (x : BitVec w) :
    low3 (~~~x) = ~~~low3 x := by
  exact BitVec.setWidth_not hw

theorem low3_and {w : Nat} (x y : BitVec w) :
    low3 (x &&& y) = low3 x &&& low3 y := by
  exact BitVec.setWidth_and

theorem low3_or {w : Nat} (x y : BitVec w) :
    low3 (x ||| y) = low3 x ||| low3 y := by
  exact BitVec.setWidth_or

theorem low3_xor {w : Nat} (x y : BitVec w) :
    low3 (x ^^^ y) = low3 x ^^^ low3 y := by
  exact BitVec.setWidth_xor

theorem low3_one {w : Nat} (hw : 3 ≤ w) : low3 (1#w) = 1#3 := by
  apply BitVec.eq_of_toNat_eq
  have hw0 : 0 < w := by omega
  have hpow : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  simp [low3, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpow]

theorem low3_neg {w : Nat} (hw : 3 ≤ w) (x : BitVec w) :
    low3 (-x) = -low3 x := by
  rw [BitVec.neg_eq_not_add, low3_add hw, low3_not hw, low3_one hw,
    ← BitVec.neg_eq_not_add]

theorem low3_sub {w : Nat} (hw : 3 ≤ w) (x y : BitVec w) :
    low3 (x - y) = low3 x - low3 y := by
  rw [BitVec.sub_eq_add_neg, low3_add hw, low3_neg hw,
    ← BitVec.sub_eq_add_neg]

theorem low3_one_and_ushiftRight_one {w : Nat} (hw : 3 ≤ w)
    (x : BitVec w) :
    low3 (1#w &&& (x >>> 1)) = 1#3 &&& (low3 x >>> 1) := by
  ext i hi
  have hw0 : 0 < w := by omega
  by_cases h : i = 0
  · subst i
    simp [low3, hw0]
  · simp [low3, hw0, h]

theorem self_amount_ne_shiftLeft {w : Nat} (k a : BitVec w)
    (hk : k ≠ 0#w) : k ≠ a <<< k.toNat := by
  intro h
  by_cases hkw : k.toNat ≤ w
  · have hlow := congrArg (BitVec.setWidth k.toNat) h
    have hzero : (a <<< k.toNat).setWidth k.toNat = 0#k.toNat := by
      rw [BitVec.setWidth_shiftLeft_of_le (i := k.toNat)
        (y := k.toNat) hkw]
      exact BitVec.shiftLeft_eq_zero (Nat.le_refl _)
    rw [hzero] at hlow
    have hnat := congrArg BitVec.toNat hlow
    simp [BitVec.toNat_setWidth, Nat.mod_two_pow_self] at hnat
    apply hk
    apply BitVec.eq_of_toNat_eq
    simpa using hnat
  · have hzero : a <<< k.toNat = 0#w :=
      BitVec.shiftLeft_eq_zero (by omega)
    exact hk (h.trans hzero)

theorem neg_self_amount_ne_shiftLeft {w : Nat} (k a : BitVec w)
    (hk : k ≠ 0#w) : -k ≠ a <<< k.toNat := by
  intro h
  apply self_amount_ne_shiftLeft k (-a) hk
  have := congrArg Neg.neg h
  simpa [BitVec.shiftLeft_neg] using this

theorem mul_eq_zero_of_lsb_true {w : Nat} (x s : BitVec w)
    (hx : x.getLsbD 0 = true) (h : x * s = 0#w) : s = 0#w := by
  have hxOdd : x.toNat % 2 = 1 := by
    rw [Nat.mod_two_eq_one_iff_testBit_zero]
    simpa [BitVec.getLsbD] using hx
  have hcop2 : Nat.Coprime x.toNat 2 := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hxOdd]
    simp
  have hcopPow : Nat.Coprime x.toNat (2 ^ w) := hcop2.pow_right w
  have hmod : (x.toNat * s.toNat) % 2 ^ w = 0 := by
    have := congrArg BitVec.toNat h
    simpa using this
  have hdvdProd : 2 ^ w ∣ x.toNat * s.toNat :=
    Nat.dvd_of_mod_eq_zero hmod
  have hdvdS : 2 ^ w ∣ s.toNat :=
    hcopPow.symm.dvd_of_dvd_mul_left hdvdProd
  have hsNat : s.toNat = 0 := Nat.eq_zero_of_dvd_of_lt hdvdS s.isLt
  apply BitVec.eq_of_toNat_eq
  simpa using hsNat

theorem one_ushiftRight_eq_zero_of_pos {w n : Nat} (hn : 0 < n) :
    (1#w) >>> n = 0#w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt : (1#w).toNat < 2 ^ n := by
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.one_lt_two_pow (by omega))
  rw [Nat.div_eq_of_lt hlt]
  rfl

theorem mul8 {w : Nat} (hw : 0 < w) (x s : BitVec w) :
    let t := x * s
    s = s <<< (x &&& ((1#w) >>> t.toNat)).toNat := by
  dsimp
  let t := x * s
  let k := x &&& ((1#w) >>> t.toNat)
  have hk : k = 0#w ∨ k = 1#w := by
    by_cases ht : t = 0#w
    · -- If `t` is zero the right shift is zero positions, and `x & 1`
      -- may be either zero or one; split on the low bit below.
      by_cases hx : x.getLsbD 0
      · right
        simp [k, t, ht, BitVec.and_twoPow, ← BitVec.twoPow_zero, hx]
      · left
        simp [k, t, ht, BitVec.and_twoPow, ← BitVec.twoPow_zero, hx]
    · left
      have htPos : 0 < t.toNat := Nat.pos_of_ne_zero (by
        intro htn
        apply ht
        apply BitVec.eq_of_toNat_eq
        simpa using htn)
      simp [k, one_ushiftRight_eq_zero_of_pos htPos]
  change s = s <<< k.toNat
  rcases hk with hk | hk
  · rw [hk]
    simp
  · have ht0 : t = 0#w := by
      by_cases ht : t = 0#w
      · exact ht
      · exfalso
        have hOneNe : (1#w) ≠ 0#w := by
          simpa using (Nat.ne_of_gt hw)
        have htPos : 0 < t.toNat := Nat.pos_of_ne_zero (by
          intro htn
          apply ht
          apply BitVec.eq_of_toNat_eq
          simpa using htn)
        have : k = 0#w := by simp [k, one_ushiftRight_eq_zero_of_pos htPos]
        exact hOneNe (hk.symm.trans this)
    have hx1 : x.getLsbD 0 = true := by
      have hkBit := congrArg (fun z : BitVec w => z.getLsbD 0) hk
      simp [k, t, ht0] at hkBit
      exact hkBit hw
    have hs0 : s = 0#w := mul_eq_zero_of_lsb_true x s hx1 (by simpa [t] using ht0)
    simp [hk, hs0]

theorem ne_of_low3_ne {w : Nat} {x y : BitVec w}
    (h : low3 x ≠ low3 y) : x ≠ y := by
  intro hxy
  exact h (congrArg low3 hxy)

theorem le_of_low3_le_of_lt_eight {w : Nat} {x y : BitVec w}
    (hx : x.toNat < 8) (h : low3 x ≤ low3 y) : x ≤ y := by
  simp only [BitVec.le_def, low3, BitVec.toNat_setWidth] at h ⊢
  rw [Nat.mod_eq_of_lt hx] at h
  exact Nat.le_trans h (Nat.mod_le _ _)

theorem mul5 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    s ≠ ~~~((x * s) ||| (1#w &&& (x ||| s))) := by
  apply ne_of_low3_ne
  rw [low3_not hw, low3_or, low3_and, low3_mul hw, low3_one hw, low3_or]
  bv_decide

theorem mul9' {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (1#w &&& ((x &&& s) >>> 1)) ≤ x * s := by
  apply le_of_low3_le_of_lt_eight
  · have hOne : (1#w &&& ((x &&& s) >>> 1)) ≤ 1#w := by
      simp only [BitVec.le_def, BitVec.toNat_and]
      exact Nat.and_le_left
    have hOneNat : (1#w).toNat = 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      exact Nat.one_lt_two_pow (by omega)
    simp only [BitVec.le_def, hOneNat] at hOne
    omega
  · rw [low3_one_and_ushiftRight_one hw, low3_and, low3_mul hw]
    bv_decide

theorem mul10 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    let t := x * s
    x ≠ 1#w ^^^ (x <<< (s ^^^ t).toNat) := by
  dsimp
  let t := x * s
  let k := s ^^^ t
  intro hEq
  change x = 1#w ^^^ (x <<< k.toNat) at hEq
  have hk : k ≠ 0#w := by
    intro hk
    have hkNat : k.toNat = 0 := by simp [hk]
    have hlow := congrArg low3 hEq
    have hbad : low3 x ≠ 1#3 ^^^ low3 x := by bv_decide
    apply hbad
    simpa [hkNat, low3_xor, low3_one hw] using hlow
  by_cases hkw : k.toNat ≤ w
  · have hShiftLow : (x <<< k.toNat).setWidth k.toNat = 0#k.toNat := by
      rw [BitVec.setWidth_shiftLeft_of_le (i := k.toNat)
        (y := k.toNat) hkw]
      exact BitVec.shiftLeft_eq_zero (Nat.le_refl _)
    have hXLow := congrArg (BitVec.setWidth k.toNat) hEq
    rw [BitVec.setWidth_xor, hShiftLow, BitVec.xor_zero,
      BitVec.setWidth_ofNat_of_le hkw] at hXLow
    have hTLow : t.setWidth k.toNat = s.setWidth k.toNat := by
      change (x * s).setWidth k.toNat = s.setWidth k.toNat
      rw [BitVec.setWidth_mul x s hkw, hXLow, BitVec.one_mul]
    have hKLow : k.setWidth k.toNat = 0#k.toNat := by
      change (s ^^^ t).setWidth k.toNat = 0#k.toNat
      rw [BitVec.setWidth_xor, hTLow, BitVec.xor_self]
    have hnat := congrArg BitVec.toNat hKLow
    simp [BitVec.toNat_setWidth, Nat.mod_two_pow_self] at hnat
    exact hk (BitVec.eq_of_toNat_eq (by simpa using hnat))
  · have hShift : x <<< k.toNat = 0#w :=
      BitVec.shiftLeft_eq_zero (by omega)
    have hxOne : x = 1#w := by simpa [hShift] using hEq
    have htEq : t = s := by simp [t, hxOne]
    apply hk
    simp [k, htEq]

theorem or_one_eq_self_of_lsb_true {w : Nat} (hw : 0 < w) (s : BitVec w)
    (hs : s.getLsbD 0 = true) : s ||| 1#w = s := by
  ext i hi
  by_cases hi0 : i = 0
  · subst i
    simp [hs, hw]
  · simp [hi0]

theorem shiftLeft_one_ne_zero_of_lsb_true {w : Nat} (hw : 1 < w)
    (t : BitVec w) (ht : t.getLsbD 0 = true) : t <<< 1 ≠ 0#w := by
  intro h
  have hbit : (t <<< 1).getLsbD 1 = true := by
    simp [BitVec.getLsbD_shiftLeft, hw, ht]
  rw [h] at hbit
  simp at hbit

theorem mul7 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    let t := x * s
    t ≠ (s ||| 1#w) <<< (t <<< x.toNat).toNat := by
  dsimp
  let t := x * s
  let u := s ||| 1#w
  let k := t <<< x.toNat
  intro hEq
  change t = u <<< k.toNat at hEq
  by_cases hk : k = 0#w
  · have hkNat : k.toNat = 0 := by simp [hk]
    have htU : t = u := by simpa [hkNat] using hEq
    have huOdd : u.getLsbD 0 = true := by simp [u, show 0 < w by omega]
    have htOdd : t.getLsbD 0 = true := by rw [htU]; exact huOdd
    have hprodOdd : (x.getLsbD 0 && s.getLsbD 0) = true := by
      rw [← mul_lsb x s]
      simpa [t] using htOdd
    have hxOdd := (Bool.and_eq_true_iff.mp hprodOdd).1
    have hsOdd := (Bool.and_eq_true_iff.mp hprodOdd).2
    have huS : u = s := or_one_eq_self_of_lsb_true (by omega) s hsOdd
    have htS : t = s := htU.trans huS
    have hzero : s * (x - 1#w) = 0#w := by
      rw [BitVec.mul_sub, BitVec.mul_one, BitVec.mul_comm s x]
      change t - s = 0#w
      rw [htS, BitVec.sub_self]
    have hxSub : x - 1#w = 0#w :=
      mul_eq_zero_of_lsb_true s (x - 1#w) hsOdd hzero
    have hxOne : x = 1#w := by
      rw [BitVec.sub_eq_iff_eq_add] at hxSub
      simpa using hxSub
    have hkDef : k = t <<< x.toNat := rfl
    have hShiftZero : t <<< 1 = 0#w := by
      rw [hkDef, hxOne] at hk
      simpa [show 0 < w by omega] using hk
    exact (shiftLeft_one_ne_zero_of_lsb_true (by omega) t htOdd) hShiftZero
  · apply self_amount_ne_shiftLeft k (u <<< x.toNat) hk
    calc
      k = t <<< x.toNat := rfl
      _ = (u <<< k.toNat) <<< x.toNat := by rw [hEq]
      _ = (u <<< x.toNat) <<< k.toNat := by
        rw [← BitVec.shiftLeft_add u k.toNat x.toNat,
          ← BitVec.shiftLeft_add u x.toNat k.toNat]
        rw [Nat.add_comm]

theorem testBit_pred_of_mod_two_eq_one {s i : Nat} (hs : s % 2 = 1) :
    (s - 1).testBit i = (if i = 0 then false else s.testBit i) := by
  cases i with
  | zero =>
      simp [Nat.testBit, hs]
      omega
  | succ i =>
      simp only [Nat.testBit_succ]
      have hsPos : 0 < s := by omega
      have hdiv : (s - 1) / 2 = s / 2 := by omega
      rw [hdiv]
      simp

theorem nat_odd_or_complement_mask {w s : Nat} (hw : 0 < w)
    (hsLt : s < 2 ^ w) (hsOdd : s % 2 = 1) :
    s ||| (2 ^ w - s) = 2 ^ w - 1 := by
  have hsPos : 0 < s := by omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsPos)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow_sub_succ (by omega),
    Nat.testBit_two_pow_sub_one]
  have hpred := testBit_pred_of_mod_two_eq_one (s := q + 1) (i := i) hsOdd
  by_cases hiw : i < w
  · by_cases hi : i = 0
    · subst i
      have hsBit : (q + 1).testBit 0 = true := by
        rwa [← Nat.mod_two_eq_one_iff_testBit_zero]
      simp [hiw, hsBit]
    · simp [hi] at hpred
      simp [hiw, hi, ← hpred]
  · have hsBit : (q + 1).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hsLt
        (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
    simp [hiw, hsBit]

theorem two_mul_or (a b : Nat) :
    2 * a ||| 2 * b = 2 * (a ||| b) := by
  simpa [Nat.shiftLeft_eq, Nat.mul_comm] using
    (Nat.shiftLeft_or_distrib (a := a) (b := b) (i := 1)).symm

theorem two_mul_and (a b : Nat) :
    2 * a &&& 2 * b = 2 * (a &&& b) := by
  simpa [Nat.shiftLeft_eq, Nat.mul_comm] using
    (Nat.shiftLeft_and_distrib (a := a) (b := b) (i := 1)).symm

theorem nat_or_neg_and_multiple : ∀ (w x s : Nat), s < 2 ^ w →
    let negs := if s = 0 then 0 else 2 ^ w - s
    ((s ||| negs) &&& ((x * s) % 2 ^ w)) = (x * s) % 2 ^ w := by
  intro w
  induction w with
  | zero =>
      intro x s hs
      have hs0 : s = 0 := by omega
      simp [hs0]
  | succ w ih =>
      intro x s hs
      by_cases hs0 : s = 0
      · simp [hs0]
      by_cases hsOdd : s % 2 = 1
      · have hmask := nat_odd_or_complement_mask (w := w + 1) (s := s)
          (by omega) hs hsOdd
        simp only [hs0, if_false]
        rw [hmask]
        rw [Nat.and_comm]
        exact Nat.and_two_pow_sub_one_of_lt_two_pow
          (Nat.mod_lt _ (Nat.two_pow_pos _))
      · have hsEven : s % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one s with h | h
          · exact h
          · exact False.elim (hsOdd h)
        let s' := s / 2
        have hsEq : s = 2 * s' := by
          dsimp [s']
          omega
        have hsLt' : s' < 2 ^ w := by
          rw [hsEq] at hs
          rw [Nat.pow_succ] at hs
          omega
        have hneg : 2 ^ (w + 1) - s = 2 * (2 ^ w - s') := by
          rw [Nat.pow_succ, hsEq]
          omega
        have hprod : (x * s) % 2 ^ (w + 1) =
            2 * ((x * s') % 2 ^ w) := by
          rw [hsEq, Nat.pow_succ]
          rw [show x * (2 * s') = 2 * (x * s') by ac_rfl,
            show 2 ^ w * 2 = 2 * 2 ^ w by ac_rfl,
            Nat.mul_mod_mul_left]
        have hs'0 : s' ≠ 0 := by
          intro hs'0
          apply hs0
          rw [hsEq, hs'0]
        have hrec := ih x s' hsLt'
        simp [hs'0] at hrec
        simp only [hs0, if_false]
        rw [hneg, hprod, hsEq, two_mul_or, two_mul_and, hrec]

theorem mul3 {w : Nat} (x s : BitVec w) :
    ((-s ||| s) &&& (x * s)) = x * s := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_mul]
  by_cases hs : s = 0#w
  · simp [hs]
  · have hsNat : s.toNat ≠ 0 := BitVec.toNat_ne_iff_ne.mpr hs
    have hneg : (-s).toNat = 2 ^ w - s.toNat := by
      exact BitVec.toNat_neg_of_pos (by
        simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod]
        exact Nat.pos_of_ne_zero hsNat)
    rw [hneg]
    rw [Nat.or_comm]
    simpa [hsNat] using nat_or_neg_and_multiple w x.toNat s.toNat s.isLt

theorem two_mul_add_one_or (a b : Nat) :
    (2 * a + 1) ||| (2 * b + 1) = 2 * (a ||| b) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp
  | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.or_div_two]
      have ha : (2 * a + 1) / 2 = a := by omega
      have hb : (2 * b + 1) / 2 = b := by omega
      have hab : (2 * (a ||| b) + 1) / 2 = a ||| b := by omega
      rw [ha, hb, hab]

theorem two_mul_add_one_and (a b : Nat) :
    (2 * a + 1) &&& (2 * b + 1) = 2 * (a &&& b) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp
  | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.and_div_two]
      have ha : (2 * a + 1) / 2 = a := by omega
      have hb : (2 * b + 1) / 2 = b := by omega
      have hab : (2 * (a &&& b) + 1) / 2 = a &&& b := by omega
      rw [ha, hb, hab]

theorem two_mul_or_two_mul_add_one (a b : Nat) :
    (2 * a) ||| (2 * b + 1) = 2 * (a ||| b) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp
  | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.or_div_two]
      have ha : (2 * a) / 2 = a := by omega
      have hb : (2 * b + 1) / 2 = b := by omega
      have hab : (2 * (a ||| b) + 1) / 2 = a ||| b := by omega
      rw [ha, hb, hab]

theorem nat_urem_mask : ∀ (w x s : Nat), x < 2 ^ w → s < 2 ^ w →
    let negs := if s = 0 then 0 else 2 ^ w - s
    x &&& (s ||| (x % s) ||| negs) = x := by
  intro w
  induction w with
  | zero =>
      intro x s hx hs
      have hx0 : x = 0 := by omega
      simp [hx0]
  | succ w ih =>
      intro x s hx hs
      by_cases hs0 : s = 0
      · simp [hs0]
      by_cases hsOdd : s % 2 = 1
      · have hmask := nat_odd_or_complement_mask (w := w + 1) (s := s)
          (by omega) hs hsOdd
        simp only [hs0, if_false]
        have hrLt : x % s < 2 ^ (w + 1) :=
          Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx
        have hor : (2 ^ (w + 1) - 1) ||| (x % s) = 2 ^ (w + 1) - 1 := by
          apply Nat.eq_of_testBit_eq
          intro i
          by_cases hi : i < w + 1
          · simp [Nat.testBit_two_pow_sub_one, hi]
          · have hrBit : (x % s).testBit i = false := by
              apply Nat.testBit_lt_two_pow
              exact Nat.lt_of_lt_of_le hrLt
                (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
            simp [Nat.testBit_two_pow_sub_one, hi, hrBit]
        rw [show s ||| x % s ||| (2 ^ (w + 1) - s) =
            (s ||| (2 ^ (w + 1) - s)) ||| (x % s) by ac_rfl,
          hmask, hor]
        exact Nat.and_two_pow_sub_one_of_lt_two_pow hx
      · have hsEven : s % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one s with h | h
          · exact h
          · exact False.elim (hsOdd h)
        let s' := s / 2
        let x' := x / 2
        let b := x % 2
        let r := x % s
        have hsEq : s = 2 * s' := by dsimp [s']; omega
        have hxEq : x = 2 * x' + b := by
          dsimp [x', b]
          omega
        have hb : b = 0 ∨ b = 1 := by
          dsimp [b]
          exact Nat.mod_two_eq_zero_or_one x
        have hsLt' : s' < 2 ^ w := by
          rw [hsEq] at hs
          rw [Nat.pow_succ] at hs
          omega
        have hxLt' : x' < 2 ^ w := by
          rw [hxEq] at hx
          rw [Nat.pow_succ] at hx
          omega
        have hs'0 : s' ≠ 0 := by
          intro hs'0
          apply hs0
          rw [hsEq, hs'0]
        have hneg : 2 ^ (w + 1) - s = 2 * (2 ^ w - s') := by
          rw [Nat.pow_succ, hsEq]
          omega
        have hrDiv : r / 2 = x' % s' := by
          dsimp [r, x', s']
          have h := Nat.mod_mul_left_div_self x 2 (s / 2)
          have htwoDvd : 2 ∣ s := by
            apply Nat.dvd_of_mod_eq_zero
            exact hsEven
          have hsDiv : (s / 2) * 2 = s := Nat.div_mul_cancel htwoDvd
          rw [hsDiv] at h
          exact h
        have hrMod : r % 2 = b := by
          dsimp [r, b]
          have htwoDvd : 2 ∣ s := by
            apply Nat.dvd_of_mod_eq_zero
            exact hsEven
          exact Nat.mod_mod_of_dvd x htwoDvd
        have hrEq : r = 2 * (x' % s') + b := by
          rw [← hrDiv, ← hrMod]
          omega
        have hrec := ih x' s' hxLt' hsLt'
        simp [hs'0] at hrec
        have hrec' : x' &&& (s' ||| (2 ^ w - s') ||| (x' % s')) = x' := by
          rw [show s' ||| (2 ^ w - s') ||| (x' % s') =
            s' ||| (x' % s') ||| (2 ^ w - s') by ac_rfl]
          exact hrec
        simp only [hs0, if_false]
        have hrem : (2 * x' + b) % (2 * s') = r := by
          rw [← hxEq, ← hsEq]
        rw [hneg, hxEq, hsEq]
        rw [hrem, hrEq]
        rcases hb with hb | hb
        · rw [hb]
          simp only [Nat.add_zero, two_mul_or, two_mul_and]
          rw [hrec]
        · rw [hb]
          rw [show 2 * s' ||| (2 * (x' % s') + 1) ||| 2 * (2 ^ w - s') =
              (2 * s' ||| 2 * (2 ^ w - s')) ||| (2 * (x' % s') + 1) by ac_rfl,
            two_mul_or, two_mul_or_two_mul_add_one, two_mul_add_one_and,
            hrec']

theorem mul6 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (x &&& (x * s)) ≠ (s ||| ~~~(x * s)) := by
  apply ne_of_low3_ne
  rw [low3_and, low3_mul hw, low3_or, low3_not hw, low3_mul hw]
  bv_decide

theorem mul11 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x * s ≠ (1#w ||| ~~~(x ^^^ s)) := by
  apply ne_of_low3_ne
  rw [low3_mul hw, low3_or, low3_one hw, low3_not hw, low3_xor]
  bv_decide

theorem mul12 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x * s ≠ (~~~(1#w) ||| (x ^^^ s)) := by
  apply ne_of_low3_ne
  rw [low3_mul hw, low3_or, low3_not hw, low3_one hw, low3_xor]
  bv_decide

theorem mul18 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x * s ≠ (1#w ||| (x + s)) := by
  apply ne_of_low3_ne
  rw [low3_mul hw, low3_or, low3_one hw, low3_add hw]
  bv_decide

theorem mul13 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ (x <<< (s + x * s).toNat) - 1#w := by
  intro hEq
  let k := s + x * s
  have hk : k ≠ 0#w := by
    intro hk
    have hlow := congrArg low3 hEq
    have hkNat : k.toNat = 0 := by simp [hk]
    have hbad : low3 x ≠ low3 x - 1#3 := by bv_decide
    apply hbad
    simpa [k, hkNat, low3_sub hw, low3_one hw] using hlow
  apply self_amount_ne_shiftLeft k (x * s) hk
  have hxShift : x + 1#w = x <<< k.toNat :=
    BitVec.eq_sub_iff_add_eq.mp (by simpa [k] using hEq)
  calc
    k = s + x * s := rfl
    _ = s * (x + 1#w) := by
      rw [BitVec.mul_add, BitVec.mul_one, BitVec.mul_comm s x,
        BitVec.add_comm]
    _ = s * (x <<< k.toNat) := by rw [hxShift]
    _ = (x * s) <<< k.toNat := by
      rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow]
      rw [← BitVec.mul_assoc, BitVec.mul_comm s x]

theorem mul14 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ 1#w - (x <<< (s - x * s).toNat) := by
  intro hEq
  let k := s - x * s
  change x = 1#w - (x <<< k.toNat) at hEq
  have hk : k ≠ 0#w := by
    intro hk
    have hlow := congrArg low3 hEq
    have hkNat : k.toNat = 0 := by simp [hk]
    have hbad : low3 x ≠ 1#3 - low3 x := by bv_decide
    apply hbad
    simpa [k, hkNat, low3_sub hw, low3_one hw] using hlow
  apply self_amount_ne_shiftLeft k (x * s) hk
  have hShift : 1#w - x = x <<< k.toNat := by
    rw [BitVec.sub_eq_iff_eq_add]
    have hx := BitVec.eq_sub_iff_add_eq.mp hEq
    simpa [BitVec.add_comm] using hx.symm
  calc
    k = s - x * s := rfl
    _ = (1#w - x) * s := by
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_mul,
        BitVec.one_mul, BitVec.neg_mul, BitVec.mul_comm x s]
    _ = (x <<< k.toNat) * s := by rw [hShift]
    _ = (x * s) <<< k.toNat := by
      rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow,
        BitVec.mul_assoc, BitVec.mul_comm (BitVec.twoPow w k.toNat) s,
        ← BitVec.mul_assoc]

theorem mul15 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    s ≠ 1#w + (s <<< (x * s - x).toNat) := by
  intro hEq
  let k := x * s - x
  change s = 1#w + (s <<< k.toNat) at hEq
  have hk : k ≠ 0#w := by
    intro hk
    have hlow := congrArg low3 hEq
    have hkNat : k.toNat = 0 := by simp [hk]
    have hbad : low3 s ≠ 1#3 + low3 s := by bv_decide
    apply hbad
    simpa [k, hkNat, low3_add hw, low3_one hw] using hlow
  apply self_amount_ne_shiftLeft k (x * s) hk
  have hShift : s - 1#w = s <<< k.toNat := by
    rw [BitVec.sub_eq_iff_eq_add, BitVec.add_comm]
    exact hEq
  calc
    k = x * s - x := rfl
    _ = x * (s - 1#w) := by
      rw [BitVec.mul_sub, BitVec.mul_one]
    _ = x * (s <<< k.toNat) := by rw [hShift]
    _ = (x * s) <<< k.toNat := by
      rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow,
        BitVec.mul_assoc]

theorem mul16 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    s ≠ 1#w - (s <<< (x * s - x).toNat) := by
  intro hEq
  let k := x * s - x
  change s = 1#w - (s <<< k.toNat) at hEq
  have hk : k ≠ 0#w := by
    intro hk
    have hlow := congrArg low3 hEq
    have hkNat : k.toNat = 0 := by simp [hk]
    have hbad : low3 s ≠ 1#3 - low3 s := by bv_decide
    apply hbad
    simpa [k, hkNat, low3_sub hw, low3_one hw] using hlow
  apply neg_self_amount_ne_shiftLeft k (x * s) hk
  have hShift : 1#w - s = s <<< k.toNat := by
    rw [BitVec.sub_eq_iff_eq_add]
    have hs := BitVec.eq_sub_iff_add_eq.mp hEq
    simpa [BitVec.add_comm] using hs.symm
  calc
    -k = -(x * s - x) := rfl
    _ = x * (1#w - s) := by
      rw [BitVec.neg_sub, BitVec.sub_eq_add_neg, BitVec.mul_add,
        BitVec.mul_one, BitVec.mul_neg, BitVec.mul_comm x s]
      rw [BitVec.add_comm]
    _ = x * (s <<< k.toNat) := by rw [hShift]
    _ = (x * s) <<< k.toNat := by
      rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow,
        BitVec.mul_assoc]

theorem mul17 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    s ≠ 1#w + (s <<< (x - x * s).toNat) := by
  intro hEq
  let k := x - x * s
  change s = 1#w + (s <<< k.toNat) at hEq
  have hk : k ≠ 0#w := by
    intro hk
    have hlow := congrArg low3 hEq
    have hkNat : k.toNat = 0 := by simp [hk]
    have hbad : low3 s ≠ 1#3 + low3 s := by bv_decide
    apply hbad
    simpa [k, hkNat, low3_add hw, low3_one hw] using hlow
  apply neg_self_amount_ne_shiftLeft k (x * s) hk
  have hShift : s - 1#w = s <<< k.toNat := by
    rw [BitVec.sub_eq_iff_eq_add, BitVec.add_comm]
    exact hEq
  calc
    -k = -(x - x * s) := rfl
    _ = x * (s - 1#w) := by
      rw [BitVec.neg_sub, BitVec.sub_eq_add_neg, BitVec.mul_add,
        BitVec.mul_neg, BitVec.mul_one]
      rw [BitVec.add_comm]
    _ = x * (s <<< k.toNat) := by rw [hShift]
    _ = (x * s) <<< k.toNat := by
      rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow,
        BitVec.mul_assoc]

theorem mul19 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ ~~~(x <<< (s + x * s).toNat) := by
  intro hEq
  let k := s + x * s
  change x = ~~~(x <<< k.toNat) at hEq
  have hk : k ≠ 0#w := by
    intro hk
    have hlow := congrArg low3 hEq
    have hkNat : k.toNat = 0 := by simp [hk]
    have hbad : low3 x ≠ ~~~low3 x := by bv_decide
    apply hbad
    simpa [k, hkNat, low3_not hw] using hlow
  apply neg_self_amount_ne_shiftLeft k (x * s) hk
  have hNegShift : x + 1#w = -(x <<< k.toNat) := by
    calc
      x + 1#w = ~~~(x <<< k.toNat) + 1#w :=
        congrArg (fun z => z + 1#w) hEq
      _ = -(x <<< k.toNat) := (BitVec.neg_eq_not_add _).symm
  have hkNeg : k = -((x * s) <<< k.toNat) := by
    calc
      k = s + x * s := rfl
      _ = s * (x + 1#w) := by
        rw [BitVec.mul_add, BitVec.mul_one, BitVec.mul_comm s x,
          BitVec.add_comm]
      _ = s * (-(x <<< k.toNat)) := by rw [hNegShift]
      _ = -((x * s) <<< k.toNat) := by
        rw [BitVec.mul_neg, BitVec.shiftLeft_eq_mul_twoPow,
          BitVec.shiftLeft_eq_mul_twoPow, ← BitVec.mul_assoc,
          BitVec.mul_comm s x]
  have := congrArg Neg.neg hkNeg
  simpa using this

theorem urem_decomp {w : Nat} (x s : BitVec w) :
    x = (x / s) * s + x % s := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv,
    BitVec.toNat_umod]
  have hEq : x.toNat % s.toNat + x.toNat / s.toNat * s.toNat = x.toNat :=
    Nat.mod_add_div' x.toNat s.toNat
  have hProd : x.toNat / s.toNat * s.toNat < 2 ^ w := by
    omega
  rw [Nat.mod_eq_of_lt hProd]
  have hSum : x.toNat / s.toNat * s.toNat + x.toNat % s.toNat < 2 ^ w := by
    omega
  rw [Nat.mod_eq_of_lt hSum]
  omega

theorem urem_low3_relation {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    low3 x = low3 (x / s) * low3 s + low3 (x % s) := by
  have h := congrArg low3 (urem_decomp x s)
  simpa [low3_add hw, low3_mul hw] using h

theorem urem8 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x = x &&& (s ||| (x % s) ||| -s) := by
  symm
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_umod]
  by_cases hs : s = 0#w
  · simp [hs]
  · have hsNat : s.toNat ≠ 0 := BitVec.toNat_ne_iff_ne.mpr hs
    have hneg : (-s).toNat = 2 ^ w - s.toNat := by
      exact BitVec.toNat_neg_of_pos (by
        simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod]
        exact Nat.pos_of_ne_zero hsNat)
    rw [hneg]
    simpa [hsNat] using nat_urem_mask w x.toNat s.toNat x.isLt s.isLt

theorem urem10 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    1#w ≠ (x % s) &&& ~~~(x ||| s) := by
  apply ne_of_low3_ne
  rw [low3_one hw, low3_and, low3_not hw, low3_or]
  have h := urem_low3_relation hw x s
  bv_decide

theorem urem12 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (1#w &&& (x % s)) ≤ ((x % s) &&& (x ||| s)) := by
  apply le_of_low3_le_of_lt_eight
  · have hOne : (1#w &&& (x % s)) ≤ 1#w := by
      simp only [BitVec.le_def, BitVec.toNat_and]
      exact Nat.and_le_left
    have hOneNat : (1#w).toNat = 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      exact Nat.one_lt_two_pow (by omega)
    simp only [BitVec.le_def, hOneNat] at hOne
    omega
  · rw [low3_and, low3_one hw, low3_and, low3_or]
    have h := urem_low3_relation hw x s
    bv_decide

theorem urem3 {w : Nat} (x s : BitVec w) (hx : x = 0#w) : x % s = 0#w := by
  subst x
  exact BitVec.zero_umod

theorem urem4 {w : Nat} (x s : BitVec w) (hs : s = 0#w) : x % s = x := by
  subst s
  exact BitVec.umod_zero

theorem urem5 {w : Nat} (x s : BitVec w) (hs : s = x) : x % s = 0#w := by
  subst s
  exact BitVec.umod_self

theorem urem6 {w : Nat} (x s : BitVec w) (h : x < s) : x % s = x := by
  exact BitVec.umod_eq_of_lt h

theorem urem7 {w : Nat} (x s : BitVec w) : x % s ≤ ~~~(-s) := by
  cases w with
  | zero => simp [BitVec.eq_nil x, BitVec.eq_nil s]
  | succ w =>
    rw [BitVec.not_eq_neg_add]
    simp only [BitVec.neg_neg]
    have hone : (1#(w + 1)).toNat = 1 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    by_cases hs : s = 0#(w + 1)
    · subst s
      simp only [BitVec.umod_zero, BitVec.zero_sub]
      simp only [BitVec.le_def, BitVec.toNat_neg, BitVec.toNat_ofNat]
      have hx := x.isLt
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      have hpred : 2 ^ (w + 1) - 1 < 2 ^ (w + 1) := by
        have := Nat.two_pow_pos (w + 1)
        omega
      rw [Nat.mod_eq_of_lt hpred]
      omega
    · simp only [BitVec.le_def, BitVec.toNat_umod, BitVec.toNat_sub,
        hone]
      have hsPos : 0 < s.toNat :=
        Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
      have hr := Nat.mod_lt x.toNat hsPos
      have hsLt := s.isLt
      have hp : 0 < 2 ^ (w + 1) := Nat.two_pow_pos (w + 1)
      have hsub : (2 ^ (w + 1) - 1 + s.toNat) % 2 ^ (w + 1) =
          s.toNat - 1 := by
        have : 2 ^ (w + 1) - 1 + s.toNat =
            2 ^ (w + 1) + (s.toNat - 1) := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt]
        omega
      rw [hsub]
      omega

theorem urem14 {w : Nat} (x s : BitVec w) : x % s ≤ x + -s := by
  rw [← BitVec.sub_eq_add_neg]
  simp only [BitVec.le_def, BitVec.toNat_umod, BitVec.toNat_sub]
  by_cases hs0 : s.toNat = 0
  · simp [hs0]
  · have hsPos : 0 < s.toNat := Nat.pos_of_ne_zero hs0
    have hr : x.toNat % s.toNat < s.toNat := Nat.mod_lt _ hsPos
    have hdecomp := Nat.mod_add_div x.toNat s.toNat
    have hp := Nat.two_pow_pos w
    by_cases hxs : x.toNat < s.toNat
    · rw [Nat.mod_eq_of_lt hxs]
      have hraw : 2 ^ w - s.toNat + x.toNat < 2 ^ w := by omega
      rw [Nat.mod_eq_of_lt hraw]
      omega
    · have hsx : s.toNat ≤ x.toNat := by omega
      have hraw : 2 ^ w - s.toNat + x.toNat = 2 ^ w + (x.toNat - s.toNat) := by omega
      rw [hraw, Nat.add_mod_left]
      have hsubLt : x.toNat - s.toNat < 2 ^ w :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt
      rw [Nat.mod_eq_of_lt hsubLt]
      have hq : 0 < x.toNat / s.toNat := Nat.div_pos hsx hsPos
      have hsq : s.toNat ≤ s.toNat * (x.toNat / s.toNat) := by
        have := Nat.mul_le_mul_left s.toNat hq
        simpa using this
      have hrs : x.toNat % s.toNat + s.toNat ≤ x.toNat := by
        calc
          x.toNat % s.toNat + s.toNat ≤
              x.toNat % s.toNat + s.toNat * (x.toNat / s.toNat) :=
            Nat.add_le_add_left hsq _
          _ = x.toNat := hdecomp
      omega

theorem nat_or_le_add (a b : Nat) : a ||| b ≤ a + b := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hb0 : b = 0
  · simp [hb0]
  let a' := a / 2
  let b' := b / 2
  have haeq : a = 2 * a' + a % 2 := by
    dsimp [a']
    omega
  have hbeq : b = 2 * b' + b % 2 := by
    dsimp [b']
    omega
  have hsum : a' + b' < a + b := by
    have ha' : a' < a := by dsimp [a']; omega
    have hb' : b' < b := by dsimp [b']; omega
    omega
  have ih := nat_or_le_add a' b'
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · rw [ha] at haeq
    rw [hb] at hbeq
    simp only [Nat.add_zero] at haeq hbeq
    rw [haeq, hbeq, two_mul_or]
    omega
  · rw [ha] at haeq
    rw [hb] at hbeq
    simp only [Nat.add_zero] at haeq
    rw [haeq, hbeq, two_mul_or_two_mul_add_one]
    omega
  · rw [ha] at haeq
    rw [hb] at hbeq
    simp only [Nat.add_zero] at hbeq
    rw [haeq, hbeq, Nat.or_comm, two_mul_or_two_mul_add_one]
    have ih' : b' ||| a' ≤ a' + b' := by simpa [Nat.or_comm] using ih
    omega
  · rw [ha] at haeq
    rw [hb] at hbeq
    rw [haeq, hbeq, two_mul_add_one_or]
    omega
termination_by a + b

theorem urem9 {w : Nat} (x s : BitVec w) :
    (x % s ||| (x &&& s)) ≤ x := by
  simp only [BitVec.le_def, BitVec.toNat_or, BitVec.toNat_umod,
    BitVec.toNat_and]
  by_cases hs0 : s.toNat = 0
  · simp [hs0]
  · have hsPos : 0 < s.toNat := Nat.pos_of_ne_zero hs0
    by_cases hxs : x.toNat < s.toNat
    · rw [Nat.mod_eq_of_lt hxs]
      have habs : x.toNat ||| (x.toNat &&& s.toNat) = x.toNat := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_or, Nat.testBit_and, Bool.or_eq_left_iff_imp]
        cases hxi : x.toNat.testBit i <;>
          cases hsi : s.toNat.testBit i <;> simp_all
      rw [habs]
      exact Nat.le_refl _
    · have hsx : s.toNat ≤ x.toNat := by omega
      have hq : 0 < x.toNat / s.toNat := Nat.div_pos hsx hsPos
      have hsq : s.toNat ≤ s.toNat * (x.toNat / s.toNat) := by
        have := Nat.mul_le_mul_left s.toNat hq
        simpa using this
      have hdecomp := Nat.mod_add_div x.toNat s.toNat
      have hrs : x.toNat % s.toNat + s.toNat ≤ x.toNat := by
        calc
          x.toNat % s.toNat + s.toNat ≤
              x.toNat % s.toNat + s.toNat * (x.toNat / s.toNat) :=
            Nat.add_le_add_left hsq _
          _ = x.toNat := hdecomp
      have hor := nat_or_le_add (x.toNat % s.toNat) (x.toNat &&& s.toNat)
      have hand : x.toNat &&& s.toNat ≤ s.toNat := Nat.and_le_right
      omega

theorem nat_le_or_left (a b : Nat) : a ≤ a ||| b := by
  have h : a &&& (a ||| b) = a := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  calc
    a = a &&& (a ||| b) := h.symm
    _ ≤ a ||| b := Nat.and_le_right

theorem nat_le_or_right (a b : Nat) : b ≤ a ||| b := by
  rw [Nat.or_comm]
  exact nat_le_or_left b a

theorem urem11 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x % s ≠ ~~~x ||| -s := by
  intro h
  let r := x % s
  by_cases hs : s = 0#w
  · subst s
    have hlow := congrArg low3 h
    simp [r, low3_or, low3_not hw, low3_neg hw] at hlow
  · have hsPos : 0 < s.toNat :=
      Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
    have hrlt : r.toNat < s.toNat := by
      dsimp [r]
      exact Nat.mod_lt _ hsPos
    have hneg : (-s).toNat = 2 ^ w - s.toNat := by
      exact BitVec.toNat_neg_of_pos (by simpa [BitVec.lt_def] using hsPos)
    have hge : 2 ^ w - s.toNat ≤ r.toNat := by
      have hor : (-s).toNat ≤ (~~~x ||| -s).toNat := by
        simp only [BitVec.toNat_or]
        exact nat_le_or_right _ _
      calc
        2 ^ w - s.toNat = (-s).toNat := hneg.symm
        _ ≤ (~~~x ||| -s).toNat := hor
        _ = r.toNat := by rw [← h]
    have hq0 : x.toNat / s.toNat = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hqpos
      have hsq : s.toNat ≤ s.toNat * (x.toNat / s.toNat) := by
        have := Nat.mul_le_mul_left s.toNat hqpos
        simpa using this
      have hdecomp := Nat.mod_add_div x.toNat s.toNat
      have hxlt := x.isLt
      dsimp [r] at hge
      omega
    have hxrn : x.toNat = r.toNat := by
      have hdecomp := Nat.mod_add_div x.toNat s.toNat
      rw [hq0] at hdecomp
      simp only [Nat.mul_zero, Nat.add_zero] at hdecomp
      have hxmod : x.toNat = x.toNat % s.toNat := hdecomp.symm
      calc
        x.toNat = x.toNat % s.toNat := hxmod
        _ = r.toNat := by rfl
    have hxr : x = r := BitVec.eq_of_toNat_eq hxrn
    change r = ~~~x ||| -s at h
    rw [hxr] at h
    have hnot0 : ~~~r = 0#w := by
      have hh := congrArg (fun z : BitVec w => ~~~r &&& z) h
      have hleft : ~~~r &&& r = 0#w := by
        ext i hi
        simp
      have hright : ~~~r &&& (~~~r ||| -s) = ~~~r := by
        ext i hi
        rw [BitVec.getElem_and hi, BitVec.getElem_or hi,
          BitVec.getElem_not hi]
        cases r[i] <;> simp
      try dsimp only at hh
      rw [hleft, hright] at hh
      exact hh.symm
    have hrAll : r = BitVec.allOnes w := by
      have hh := congrArg (fun z : BitVec w => ~~~z) hnot0
      simpa using hh
    have hrNat : r.toNat = 2 ^ w - 1 := by
      rw [hrAll, BitVec.toNat_allOnes]
    have hsLt := s.isLt
    omega

theorem udiv2 {w : Nat} (x s : BitVec w) (hsx : s = x)
    (hs0 : s ≠ 0#w) : x.smtUDiv s = 1#w := by
  subst x
  rw [BitVec.smtUDiv_eq, if_neg hs0, BitVec.udiv_self]
  simp [hs0]

theorem udiv3 {w : Nat} (x s : BitVec w) (hs : s = 0#w) :
    x.smtUDiv s = BitVec.allOnes w := by
  subst s
  simp [BitVec.smtUDiv]

theorem udiv4 {w : Nat} (x s : BitVec w) (hx : x = 0#w)
    (hs : s ≠ 0#w) : x.smtUDiv s = 0#w := by
  subst x
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.zero_udiv]

theorem udiv5 {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    x.smtUDiv s ≤ x := by
  rw [BitVec.smtUDiv_eq, if_neg hs]
  simp only [BitVec.le_def, BitVec.toNat_udiv]
  exact Nat.div_le_self _ _

theorem udiv6 {w : Nat} (x s : BitVec w)
    (hs : s = BitVec.allOnes w) (hx : x ≠ BitVec.allOnes w) :
    x.smtUDiv s = 0#w := by
  subst s
  cases w with
  | zero => exact False.elim (hx (BitVec.eq_nil x))
  | succ w =>
    have hs0 : BitVec.allOnes (w + 1) ≠ 0#(w + 1) := by
      intro h
      have hh := congrArg BitVec.toNat h
      have hz : (0#(w + 1)).toNat = 0 := by simp
      rw [BitVec.toNat_allOnes, hz] at hh
      have hp := Nat.one_lt_two_pow (by omega : w + 1 ≠ 0)
      omega
    rw [BitVec.smtUDiv_eq, if_neg hs0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_udiv, BitVec.toNat_allOnes]
    have hxlt := x.isLt
    have hxltMax : x.toNat < 2 ^ (w + 1) - 1 := by
      have hxle : x.toNat ≤ 2 ^ (w + 1) - 1 := by omega
      have hxne : x.toNat ≠ 2 ^ (w + 1) - 1 := by
        intro h
        apply hx
        apply BitVec.eq_of_toNat_eq
        simpa using h
      omega
    rw [Nat.div_eq_of_lt hxltMax]
    simp

theorem nat_or_one (a : Nat) :
    a ||| 1 = if a % 2 = 0 then a + 1 else a := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · have heq : a = 2 * (a / 2) := by omega
    rw [ha, if_pos rfl, heq]
    calc
      2 * (a / 2) ||| 1 =
          2 * (a / 2) ||| (2 * 0 + 1) := by rfl
      _ = 2 * ((a / 2) ||| 0) + 1 := two_mul_or_two_mul_add_one _ _
      _ = 2 * (a / 2) + 1 := by simp
  · have heq : a = 2 * (a / 2) + 1 := by omega
    rw [ha, if_neg (by omega), heq]
    calc
      2 * (a / 2) + 1 ||| 1 =
          (2 * (a / 2) + 1) ||| (2 * 0 + 1) := by rfl
      _ = 2 * ((a / 2) ||| 0) + 1 := two_mul_add_one_or _ _
      _ = 2 * (a / 2) + 1 := by simp

theorem udiv8 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x.smtUDiv s ≤ -(s ||| 1#w) := by
  by_cases hs : s = 0#w
  · subst s
    have hnegOne : -(1#w) = BitVec.allOnes w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_neg, BitVec.toNat_allOnes]
      have hone : (1#w).toNat = 1 := by
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      rw [hone]
      have hpred : 2 ^ w - 1 < 2 ^ w := by
        have := Nat.two_pow_pos w
        omega
      rw [Nat.mod_eq_of_lt hpred]
    simp [BitVec.smtUDiv, hnegOne]
  · rw [BitVec.smtUDiv_eq, if_neg hs]
    simp only [BitVec.le_def, BitVec.toNat_udiv, BitVec.toNat_neg,
      BitVec.toNat_or]
    have hsPos : 0 < s.toNat :=
      Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
    have hone : (1#w).toNat = 1 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    rw [hone, nat_or_one]
    let q := x.toNat / s.toNat
    have hprod : s.toNat * q ≤ x.toNat := Nat.mul_div_le x.toNat s.toNat
    have hxlt := x.isLt
    have hslt := s.isLt
    have hp := Nat.two_pow_pos w
    split
    · next heven =>
      have hnEven : (2 ^ w) % 2 = 0 := by
        rw [Nat.pow_mod]
        simp [show 0 < w by omega]
      have hsTwo : 2 ≤ s.toNat := by
        by_cases hsOne : s.toNat = 1
        · rw [hsOne] at heven
          simp at heven
        · omega
      have hsum : q + (s.toNat + 1) ≤ 2 ^ w := by
        by_cases hq0 : q = 0
        · omega
        have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
        by_cases hqOne : q = 1
        · have hsEvenLt : s.toNat + 1 < 2 ^ w := by
            omega
          omega
        · have hqTwo : 2 ≤ q := by omega
          have hmul : q + s.toNat ≤ s.toNat * q := by
            by_cases haq : s.toNat ≤ q
            · have hh := Nat.mul_le_mul_right q hsTwo
              omega
            · have hqa : q ≤ s.toNat := by omega
              have hh := Nat.mul_le_mul_right s.toNat hqTwo
              have hcomm : q * s.toNat = s.toNat * q := Nat.mul_comm _ _
              omega
          omega
      have hpos : 0 < s.toNat + 1 := by omega
      have hlt : s.toNat + 1 < 2 ^ w := by omega
      change q ≤ (2 ^ w - (s.toNat + 1)) % 2 ^ w
      have hneg : (2 ^ w - (s.toNat + 1)) % 2 ^ w =
          2 ^ w - (s.toNat + 1) := Nat.mod_eq_of_lt (by omega)
      rw [hneg]
      omega
    · next hodd =>
      have hsum : q + s.toNat ≤ 2 ^ w := by
        by_cases hq0 : q = 0
        · omega
        have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
        have hmul : q + s.toNat ≤ s.toNat * q + 1 := by
          by_cases hqOne : q = 1
          · rw [hqOne]
            simp
            omega
          by_cases hsOne : s.toNat = 1
          · rw [hsOne]
            simp
          have hqTwo : 2 ≤ q := by omega
          have hsTwo : 2 ≤ s.toNat := by omega
          by_cases haq : s.toNat ≤ q
          · have hh := Nat.mul_le_mul_right q hsTwo
            omega
          · have hqa : q ≤ s.toNat := by omega
            have hh := Nat.mul_le_mul_right s.toNat hqTwo
            have hcomm : q * s.toNat = s.toNat * q := Nat.mul_comm _ _
            omega
        omega
      change q ≤ (2 ^ w - s.toNat) % 2 ^ w
      have hneg : (2 ^ w - s.toNat) % 2 ^ w = 2 ^ w - s.toNat :=
        Nat.mod_eq_of_lt (by omega)
      rw [hneg]
      omega

theorem toNat_sub_one_of_ne_zero {w : Nat} (x : BitVec w)
    (hx : x ≠ 0#w) : (x - 1#w).toNat = x.toNat - 1 := by
  have hxPos : 0 < x.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hx)
  have hwPos : 0 < w := by
    by_cases hw : w = 0
    · subst w
      exact False.elim (hx (BitVec.eq_nil x))
    · omega
  have hone : (1#w).toNat = 1 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hwPos))]
  rw [BitVec.toNat_sub, hone]
  have hraw : 2 ^ w - 1 + x.toNat = 2 ^ w + (x.toNat - 1) := by
    omega
  rw [hraw, Nat.add_mod_left, Nat.mod_eq_of_lt]
  omega

theorem nat_add_sub_one_le_mul (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    a + b - 1 ≤ a * b := by
  by_cases ha1 : a = 1
  · subst a
    simp
  by_cases hb1 : b = 1
  · subst b
    simp
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  by_cases hab : a ≤ b
  · have hh := Nat.mul_le_mul_right b ha2
    omega
  · have hba : b ≤ a := by omega
    have hh := Nat.mul_le_mul_right a hb2
    have hcomm : b * a = a * b := Nat.mul_comm _ _
    omega

theorem udiv7 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    -((-s) &&& (-(x.smtUDiv s))) ≤ x := by
  let t := x.smtUDiv s
  change -((-s) &&& (-t)) ≤ x
  by_cases hs : s = 0#w
  · subst s
    simp [t, BitVec.le_def]
  · have htEq : t = x / s := by simp [t, BitVec.smtUDiv, hs]
    by_cases ht : t = 0#w
    · rw [ht]
      simp [BitVec.le_def]
    · rw [show -((-s) &&& (-t)) =
          ((s - 1#w) ||| (t - 1#w)) + 1#w by
        rw [BitVec.neg_eq_not_add, BitVec.not_and, BitVec.not_neg,
          BitVec.not_neg]]
      simp only [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_or]
      rw [toNat_sub_one_of_ne_zero s hs,
        toNat_sub_one_of_ne_zero t ht]
      have hone : (1#w).toNat = 1 := by
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      rw [hone]
      have hsPos : 0 < s.toNat :=
        Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
      have htPos : 0 < t.toNat :=
        Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr ht)
      have hor := nat_or_le_add (s.toNat - 1) (t.toNat - 1)
      have hmulBound := nat_add_sub_one_le_mul s.toNat t.toNat hsPos htPos
      have htNat : t.toNat = x.toNat / s.toNat := by
        rw [htEq, BitVec.toNat_udiv]
      have hprod : s.toNat * t.toNat ≤ x.toNat := by
        rw [htNat]
        exact Nat.mul_div_le _ _
      have hxlt := x.isLt
      have hraw : (s.toNat - 1 ||| t.toNat - 1) + 1 < 2 ^ w := by
        omega
      rw [Nat.mod_eq_of_lt hraw]
      omega

theorem le_of_and_not_eq_zero {w : Nat} (s x : BitVec w)
    (h : s &&& ~~~x = 0#w) : s ≤ x := by
  have hsx : s &&& x = s := by
    ext i hi
    have hb := congrArg (fun z : BitVec w => z[i]) h
    try dsimp only at hb
    rw [BitVec.getElem_and hi, BitVec.getElem_not hi] at hb
    have hsbit := s[i]
    have hxbit := x[i]
    cases hsbit <;> cases hxbit <;> simp_all
  simp only [BitVec.le_def]
  have hn := congrArg BitVec.toNat hsx
  simp only [BitVec.toNat_and] at hn
  rw [← hn]
  exact Nat.and_le_right

theorem udiv9 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x.smtUDiv s ≠ -(s &&& ~~~x) := by
  intro h
  let t := x.smtUDiv s
  let a := s &&& ~~~x
  change t = -a at h
  by_cases hs : s = 0#w
  · subst s
    have ht : t = BitVec.allOnes w := by simp [t, BitVec.smtUDiv]
    have ha : a = 0#w := by simp [a]
    rw [ht, ha] at h
    have hh := congrArg BitVec.toNat h
    have hz : (0#w).toNat = 0 := by simp
    rw [BitVec.toNat_allOnes, BitVec.neg_zero, hz] at hh
    have hp := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega
  · have htEq : t = x / s := by simp [t, BitVec.smtUDiv, hs]
    by_cases ha0 : a = 0#w
    · rw [ha0, BitVec.neg_zero] at h
      have ht0 : t = 0#w := h
      have hxlt : x < s := by
        rw [BitVec.lt_def]
        have htNat : t.toNat = x.toNat / s.toNat := by
          rw [htEq, BitVec.toNat_udiv]
        have hsPos : 0 < s.toNat :=
          Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
        have htZero := congrArg BitVec.toNat ht0
        have hz : (0#w).toNat = 0 := by simp
        rw [hz] at htZero
        have hdiv0 : x.toNat / s.toNat = 0 := by simpa [htNat] using htZero
        by_cases hxs : x.toNat < s.toNat
        · exact hxs
        · have hsx : s.toNat ≤ x.toNat := by omega
          have hone : 1 ≤ x.toNat / s.toNat :=
            (Nat.le_div_iff_mul_le hsPos).mpr (by simpa using hsx)
          omega
      have hsle := le_of_and_not_eq_zero s x (by simpa [a] using ha0)
      rw [BitVec.lt_def] at hxlt
      rw [BitVec.le_def] at hsle
      omega
    · have haPos : 0 < a.toNat :=
        Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr ha0)
      have hneg : (-a).toNat = 2 ^ w - a.toNat :=
        BitVec.toNat_neg_of_pos (by simpa [BitVec.lt_def] using haPos)
      have hta : t.toNat + a.toNat = 2 ^ w := by
        have hh := congrArg BitVec.toNat h
        rw [hneg] at hh
        have halt := a.isLt
        omega
      have hsPos : 0 < s.toNat :=
        Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
      have htPos : 0 < t.toNat := by omega
      have haLeS : a.toNat ≤ s.toNat := by
        dsimp [a]
        exact Nat.and_le_left
      have htNat : t.toNat = x.toNat / s.toNat := by
        rw [htEq, BitVec.toNat_udiv]
      have hprod : s.toNat * t.toNat ≤ x.toNat := by
        rw [htNat]
        exact Nat.mul_div_le _ _
      have hxlt := x.isLt
      by_cases hsOne : s.toNat = 1
      · have haOne : a.toNat = 1 := by omega
        have htMax : t.toNat = 2 ^ w - 1 := by omega
        rw [hsOne] at hprod
        simp only [Nat.one_mul] at hprod
        have hxMax : x.toNat = 2 ^ w - 1 := by omega
        have hnotX : (~~~x).toNat = 0 := by
          rw [BitVec.toNat_not, hxMax]
          omega
        have haZero : a.toNat = 0 := by
          dsimp [a]
          simp [BitVec.toNat_and, hnotX]
        omega
      · by_cases htOne : t.toNat = 1
        · have haMax : a.toNat = 2 ^ w - 1 := by omega
          have hslt := s.isLt
          have hsMax : s.toNat = 2 ^ w - 1 := by omega
          have hnotLe : 2 ^ w - 1 ≤ (~~~x).toNat := by
            have haLeNot : a.toNat ≤ (~~~x).toNat := by
              dsimp [a]
              exact Nat.and_le_right
            omega
          have hnotLt := (~~~x).isLt
          have hnotEq : (~~~x).toNat = 2 ^ w - 1 := by omega
          have hxZero : x.toNat = 0 := by
            rw [BitVec.toNat_not] at hnotEq
            omega
          have htZero : t.toNat = 0 := by
            rw [htNat, hxZero]
            simp
          omega
        · have hsTwo : 2 ≤ s.toNat := by omega
          have htTwo : 2 ≤ t.toNat := by omega
          have hsum : s.toNat + t.toNat ≤ s.toNat * t.toNat := by
            by_cases hst : s.toNat ≤ t.toNat
            · have hh := Nat.mul_le_mul_right t.toNat hsTwo
              omega
            · have hts : t.toNat ≤ s.toNat := by omega
              have hh := Nat.mul_le_mul_right s.toNat htTwo
              have hcomm : t.toNat * s.toNat = s.toNat * t.toNat :=
                Nat.mul_comm _ _
              omega
          omega

theorem toNat_le_and_not_add {w : Nat} (x y : BitVec w) :
    x.toNat ≤ (x &&& ~~~y).toNat + y.toNat := by
  have hpart : (x &&& ~~~y) ||| (x &&& y) = x := by
    ext i hi
    rw [BitVec.getElem_or hi, BitVec.getElem_and hi,
      BitVec.getElem_not hi, BitVec.getElem_and hi]
    cases x[i] <;> cases y[i] <;> decide
  have hn := congrArg BitVec.toNat hpart
  simp only [BitVec.toNat_or] at hn
  have hor := nat_or_le_add (x &&& ~~~y).toNat (x &&& y).toNat
  have hand : (x &&& y).toNat ≤ y.toNat := by
    simp only [BitVec.toNat_and]
    exact Nat.and_le_right
  omega

theorem mod_two_zero_of_lsb_false {w : Nat} (x : BitVec w)
    (h : x.getLsbD 0 = false) : x.toNat % 2 = 0 := by
  rw [Nat.mod_two_eq_zero_iff_testBit_zero]
  simpa [BitVec.getLsbD] using h

theorem udiv10 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (s ||| x.smtUDiv s) ≠ (x &&& ~~~(1#w)) := by
  intro h
  let t := x.smtUDiv s
  change s ||| t = x &&& ~~~(1#w) at h
  have hwPos : 0 < w := by omega
  have hb := congrArg (fun z : BitVec w => z.getLsbD 0) h
  try dsimp only at hb
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not] at hb
  have honeBit : (1#w).getLsbD 0 = true := by
    simp [BitVec.getLsbD, hwPos]
  rw [honeBit] at hb
  simp [hwPos] at hb
  have hsBit : s.getLsbD 0 = false := by
    change s.toNat.testBit 0 = false
    exact hb.1
  have htBit : t.getLsbD 0 = false := by
    change t.toNat.testBit 0 = false
    exact hb.2
  have hsEven := mod_two_zero_of_lsb_false s hsBit
  have htEven := mod_two_zero_of_lsb_false t htBit
  by_cases hs : s = 0#w
  · subst s
    have htAll : t = BitVec.allOnes w := by simp [t, BitVec.smtUDiv]
    rw [htAll] at htBit
    have hallBit : (BitVec.allOnes w).getLsbD 0 = true := by
      simp [BitVec.getLsbD, hwPos]
    exact Bool.noConfusion (htBit.symm.trans hallBit)
  · have hsPos : 0 < s.toNat :=
      Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
    have htEq : t = x / s := by simp [t, BitVec.smtUDiv, hs]
    have horLeX : (s ||| t).toNat ≤ x.toNat := by
      rw [h]
      simp only [BitVec.toNat_and]
      exact Nat.and_le_left
    have hsLeX : s.toNat ≤ x.toNat := by
      have hle : s.toNat ≤ (s ||| t).toNat := by
        simp only [BitVec.toNat_or]
        exact nat_le_or_left _ _
      omega
    have htPos : 0 < t.toNat := by
      have htNat : t.toNat = x.toNat / s.toNat := by
        rw [htEq, BitVec.toNat_udiv]
      rw [htNat]
      exact Nat.div_pos hsLeX hsPos
    have hsTwo : 2 ≤ s.toNat := by omega
    have htTwo : 2 ≤ t.toNat := by omega
    have hxNear : x.toNat ≤ (s ||| t).toNat + 1 := by
      have hnear := toNat_le_and_not_add x (1#w)
      have hone : (1#w).toNat = 1 := by
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      rw [hone, ← h] at hnear
      exact hnear
    have horAdd := nat_or_le_add s.toNat t.toNat
    have htNat : t.toNat = x.toNat / s.toNat := by
      rw [htEq, BitVec.toNat_udiv]
    have hprod : s.toNat * t.toNat ≤ x.toNat := by
      rw [htNat]
      exact Nat.mul_div_le _ _
    simp only [BitVec.toNat_or] at hxNear
    have hsmall : s.toNat * t.toNat ≤ s.toNat + t.toNat + 1 := by
      omega
    have hsEq : s.toNat = 2 := by
      by_cases hs2 : s.toNat = 2
      · exact hs2
      have hsFour : 4 ≤ s.toNat := by omega
      by_cases hstLe : s.toNat ≤ t.toNat
      · have hfour := Nat.mul_le_mul_right t.toNat hsFour
        omega
      · have hts : t.toNat ≤ s.toNat := by omega
        by_cases ht2 : t.toNat = 2
        · rw [ht2] at hsmall
          omega
        · have htFour : 4 ≤ t.toNat := by omega
          have hfour := Nat.mul_le_mul_right s.toNat htFour
          have hcomm : t.toNat * s.toNat = s.toNat * t.toNat :=
            Nat.mul_comm _ _
          omega
    have htEqTwo : t.toNat = 2 := by
      rw [hsEq] at hsmall
      omega
    rw [hsEq, htEqTwo] at hprod horAdd hxNear
    have horEq : s.toNat ||| t.toNat = 2 := by
      rw [hsEq, htEqTwo]
      decide
    have hor22 : 2 ||| 2 = 2 := by decide
    rw [hor22] at hxNear
    simp at hprod
    omega

theorem udiv11 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (s ||| 1#w) ≠ (x &&& ~~~(x.smtUDiv s)) := by
  intro h
  let t := x.smtUDiv s
  change s ||| 1#w = x &&& ~~~t at h
  have hwPos : 0 < w := by omega
  have hb := congrArg (fun z : BitVec w => z.getLsbD 0) h
  try dsimp only at hb
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not] at hb
  have honeBit : (1#w).getLsbD 0 = true := by
    simp [BitVec.getLsbD, hwPos]
  rw [honeBit] at hb
  simp [hwPos] at hb
  have hxBit : x.getLsbD 0 = true := by
    change x.toNat.testBit 0 = true
    exact hb.1
  have htBit : t.getLsbD 0 = false := by
    change t.toNat.testBit 0 = false
    exact hb.2
  have hxOdd : x.toNat % 2 = 1 := by
    rw [Nat.mod_two_eq_one_iff_testBit_zero]
    simpa [BitVec.getLsbD] using hxBit
  have htEven := mod_two_zero_of_lsb_false t htBit
  by_cases hs : s = 0#w
  · subst s
    have htAll : t = BitVec.allOnes w := by simp [t, BitVec.smtUDiv]
    rw [htAll] at htBit
    have hallBit : (BitVec.allOnes w).getLsbD 0 = true := by
      simp [BitVec.getLsbD, hwPos]
    exact Bool.noConfusion (htBit.symm.trans hallBit)
  · have hsPos : 0 < s.toNat :=
      Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
    have htEq : t = x / s := by simp [t, BitVec.smtUDiv, hs]
    have hleftLeX : (s ||| 1#w).toNat ≤ x.toNat := by
      rw [h]
      simp only [BitVec.toNat_and]
      exact Nat.and_le_left
    have hsLeX : s.toNat ≤ x.toNat := by
      have hle : s.toNat ≤ (s ||| 1#w).toNat := by
        simp only [BitVec.toNat_or]
        exact nat_le_or_left _ _
      omega
    have htPos : 0 < t.toNat := by
      rw [htEq, BitVec.toNat_udiv]
      exact Nat.div_pos hsLeX hsPos
    have htTwo : 2 ≤ t.toNat := by omega
    have htNat : t.toNat = x.toNat / s.toNat := by
      rw [htEq, BitVec.toNat_udiv]
    have hprod : s.toNat * t.toNat ≤ x.toNat := by
      rw [htNat]
      exact Nat.mul_div_le _ _
    have hxNear : x.toNat ≤ (s ||| 1#w).toNat + t.toNat := by
      have hnear := toNat_le_and_not_add x t
      rw [← h] at hnear
      exact hnear
    have hone : (1#w).toNat = 1 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    have horOne := nat_or_le_add s.toNat 1
    simp only [BitVec.toNat_or, hone] at hxNear
    have hsmall : s.toNat * t.toNat ≤ s.toNat + t.toNat + 1 := by
      omega
    by_cases hsOne : s.toNat = 1
    · have htX : t.toNat = x.toNat := by
        rw [htNat, hsOne]
        simp
      omega
    · have hsTwo : 2 ≤ s.toNat := by omega
      have htEqTwo : t.toNat = 2 := by
        by_cases ht2 : t.toNat = 2
        · exact ht2
        have htFour : 4 ≤ t.toNat := by omega
        by_cases hs2 : s.toNat = 2
        · rw [hs2] at hsmall
          omega
        have hsThree : 3 ≤ s.toNat := by omega
        by_cases hst : s.toNat ≤ t.toNat
        · have hh := Nat.mul_le_mul_right t.toNat hsThree
          omega
        · have hts : t.toNat ≤ s.toNat := by omega
          have hh := Nat.mul_le_mul_right s.toNat htFour
          have hcomm : t.toNat * s.toNat = s.toNat * t.toNat :=
            Nat.mul_comm _ _
          omega
      have hsLeThree : s.toNat ≤ 3 := by
        rw [htEqTwo] at hsmall
        omega
      have hrlt : x.toNat % s.toNat < s.toNat := Nat.mod_lt _ hsPos
      have hdecomp := Nat.mod_add_div x.toNat s.toNat
      rw [← htNat, htEqTwo] at hdecomp
      by_cases hsEqTwo : s.toNat = 2
      · have hxEq : x.toNat = 5 := by omega
        have hlow := congrArg low3 h
        rw [low3_or, low3_one hw, low3_and, low3_not hw] at hlow
        have hsLow : low3 s = 2#3 := by
          apply BitVec.eq_of_toNat_eq
          simp [low3, BitVec.toNat_setWidth, hsEqTwo]
        have htLow : low3 t = 2#3 := by
          apply BitVec.eq_of_toNat_eq
          simp [low3, BitVec.toNat_setWidth, htEqTwo]
        have hxLow : low3 x = 5#3 := by
          apply BitVec.eq_of_toNat_eq
          simp [low3, BitVec.toNat_setWidth, hxEq]
        rw [hsLow, htLow, hxLow] at hlow
        bv_decide
      · have hsEqThree : s.toNat = 3 := by omega
        have hxEq : x.toNat = 7 := by omega
        have hlow := congrArg low3 h
        rw [low3_or, low3_one hw, low3_and, low3_not hw] at hlow
        have hsLow : low3 s = 3#3 := by
          apply BitVec.eq_of_toNat_eq
          simp [low3, BitVec.toNat_setWidth, hsEqThree]
        have htLow : low3 t = 2#3 := by
          apply BitVec.eq_of_toNat_eq
          simp [low3, BitVec.toNat_setWidth, htEqTwo]
        have hxLow : low3 x = 7#3 := by
          apply BitVec.eq_of_toNat_eq
          simp [low3, BitVec.toNat_setWidth, hxEq]
        rw [hsLow, htLow, hxLow] at hlow
        bv_decide

end BvAbstraction
