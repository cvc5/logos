module

public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

private theorem bv_smulo_elim_shape_of_ne_stuck (A : Term) :
    __eo_prog_bv_smulo_elim A ≠ Term.Stuck ->
    ∃ a b c,
      A =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) c := by
  intro h
  by_cases hShape :
      ∃ a b c,
        A =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) c
  · exact hShape
  · have hStuck : __eo_prog_bv_smulo_elim A = Term.Stuck := by
      rw [__eo_prog_bv_smulo_elim.eq_2]
      intro a b c hEq
      exact hShape ⟨a, b, c, hEq⟩
    exact False.elim (h hStuck)

private def bvSmuloExpanded (a b : Term) : Term :=
  let wTerm := __bv_bitwidth (__eo_typeof a)
  let nm2 := __eo_add wTerm (Term.Numeral (-2 : native_Int))
  let len :=
    __eo_add
      (__eo_add (Term.Numeral 1)
        (__eo_add (Term.Numeral (-1 : native_Int)) nm2))
      (Term.Numeral (-1 : native_Int))
  let topIdx := __eo_add wTerm (Term.Numeral (-1 : native_Int))
  let topExtract := Term.UOp2 UserOp2.extract topIdx topIdx
  let signExtendTop := Term.UOp1 UserOp1.sign_extend topIdx
  let xb :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) b)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvxor)
          (__eo_mk_apply signExtendTop (__eo_mk_apply topExtract b)))
        (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof b)))
  let xbBit1 := __eo_mk_apply
    (Term.UOp2 UserOp2.extract (Term.Numeral 1) (Term.Numeral 1)) xb
  let xa :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) a)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvxor)
          (__eo_mk_apply signExtendTop (__eo_mk_apply topExtract a)))
        (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof a)))
  let xaTop := __eo_mk_apply (Term.UOp2 UserOp2.extract nm2 nm2) xa
  let scan :=
    __bv_smulo_elim_rec xa xb xaTop
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvand) xbBit1)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.bvand) xaTop)
          (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof xbBit1))))
      (__eo_requires (__eo_is_neg len) (Term.Boolean false)
        (__iota_rec
          (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) len)
          (Term.Numeral 1)))
      nm2
  let signExtendOne := Term.UOp1 UserOp1.sign_extend (Term.Numeral 1)
  let aExt := Term.Apply signExtendOne a
  let product :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt)
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.bvmul)
          (Term.Apply signExtendOne b))
        (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)))
  let prodBitW := __eo_mk_apply (Term.UOp2 UserOp2.extract wTerm wTerm) product
  let prodTopDiff :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.bvxor) prodBitW)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvxor)
          (__eo_mk_apply topExtract product))
        (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof prodBitW)))
  __eo_ite (__eo_eq wTerm (Term.Numeral 1))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) a)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) b)
            (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof a)))))
      (Term.Binary 1 1))
    (__eo_ite (__eo_eq wTerm (Term.Numeral 2))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq) prodTopDiff)
        (Term.Binary 1 1))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.bvor) scan)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.bvor) prodTopDiff)
              (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof scan)))))
        (Term.Binary 1 1)))

private def inc (b : Bool) : Nat :=
  if b then 1 else 0

private def signedOverflowMag (W X Y : Nat) (sx sy : Bool) : Bool :=
  let P := (X + inc sx) * (Y + inc sy)
  if sx = sy then decide (2 ^ W ≤ P) else decide (2 ^ W < P)

private def topDiffMag (W X Y : Nat) (sx sy : Bool) : Bool :=
  let P := (X + inc sx) * (Y + inc sy)
  if sx = sy then
    P.testBit (W + 1) ^^ P.testBit W
  else
    let R := if P = 0 then 0 else 2 ^ (W + 2) - P
    R.testBit (W + 1) ^^ R.testBit W

private theorem testBit_false_of_lt_two_pow {n k : Nat} (h : n < 2 ^ k) :
    n.testBit k = false := by
  by_cases hb : n.testBit k = true
  · have hle := Nat.ge_two_pow_of_testBit hb
    exact False.elim (Nat.not_le_of_gt h hle)
  · exact Bool.eq_false_iff.2 hb

private theorem pos_topDiff_eq (W P : Nat) (hP : P ≤ 2 ^ (W + 1)) :
    (P.testBit (W + 1) ^^ P.testBit W) = decide (2 ^ W ≤ P) := by
  by_cases hlt : P < 2 ^ W
  · have hWfalse : P.testBit W = false := testBit_false_of_lt_two_pow hlt
    have hW1false : P.testBit (W + 1) = false := by
      apply testBit_false_of_lt_two_pow
      exact Nat.lt_trans hlt
        (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : W < W + 1))
    have hnot : ¬ 2 ^ W ≤ P := Nat.not_le_of_gt hlt
    simp [hWfalse, hW1false, hnot]
  · have hge : 2 ^ W ≤ P := Nat.le_of_not_gt hlt
    by_cases heq : P = 2 ^ (W + 1)
    · subst P
      have hge' : 2 ^ W ≤ 2 ^ (W + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      have hb1 : (2 ^ (W + 1)).testBit (W + 1) = true := by
        rw [Nat.testBit_two_pow]
        simp
      have hb0 : (2 ^ (W + 1)).testBit W = false := by
        rw [Nat.testBit_two_pow]
        simp
      simp [hb1, hb0, hge']
    · have hltTop : P < 2 ^ (W + 1) := Nat.lt_of_le_of_ne hP heq
      have hbW : P.testBit W = true := bit_w_of_range hge hltTop
      have hbW1 : P.testBit (W + 1) = false :=
        testBit_false_of_lt_two_pow hltTop
      simp [hbW, hbW1, hge]

private theorem neg_topDiff_eq (W P : Nat) (hP : P ≤ 2 ^ (W + 1)) :
    (let R := if P = 0 then 0 else 2 ^ (W + 2) - P
     R.testBit (W + 1) ^^ R.testBit W) = decide (2 ^ W < P) := by
  by_cases hP0 : P = 0
  · subst P
    simp
  · have hPpos : 0 < P := Nat.pos_of_ne_zero hP0
    let R := 2 ^ (W + 2) - P
    let low := 2 ^ (W + 1) - P
    have hIf : (if P = 0 then 0 else 2 ^ (W + 2) - P) = R := by
      simp [hP0, R]
    rw [hIf]
    have hPow : 2 ^ (W + 2) = 2 ^ (W + 1) + 2 ^ (W + 1) := by
      have h : 2 ^ (W + 2) = 2 ^ (W + 1) * 2 :=
        (pow_two_mul (W + 1) 1).symm
      rw [h]
      omega
    have hR_eq : R = 2 ^ (W + 1) + low := by
      dsimp [R, low]
      rw [hPow]
      omega
    have hRlt : R < 2 ^ (W + 2) := by
      dsimp [R]
      exact Nat.sub_lt (Nat.two_pow_pos _) hPpos
    have hRge : 2 ^ (W + 1) ≤ R := by
      dsimp [R]
      omega
    have hbHigh : R.testBit (W + 1) = true := bit_w_of_range hRge hRlt
    have hLowLt : low < 2 ^ (W + 1) := by
      dsimp [low]
      exact Nat.sub_lt (Nat.two_pow_pos _) hPpos
    have hRmod : R % 2 ^ (W + 1) = low := by
      rw [hR_eq]
      have hmod :
          (2 ^ (W + 1) + low) % 2 ^ (W + 1) =
            low % 2 ^ (W + 1) := by
        simpa [Nat.add_comm, Nat.mul_comm] using
          (Nat.add_mul_mod_self_left low (2 ^ (W + 1)) 1)
      rw [hmod, Nat.mod_eq_of_lt hLowLt]
    have hbLowEq : R.testBit W = low.testBit W := by
      have htb := Nat.testBit_mod_two_pow R (W + 1) W
      rw [hRmod] at htb
      have hdec : decide (W < W + 1) = true := by simp
      rw [hdec] at htb
      simpa using htb.symm
    by_cases hle : P ≤ 2 ^ W
    · have hnot : ¬ 2 ^ W < P := Nat.not_lt_of_ge hle
      have hLowGe : 2 ^ W ≤ low := by
        dsimp [low]
        omega
      have hbLow : low.testBit W = true := bit_w_of_range hLowGe hLowLt
      change (R.testBit (W + 1) ^^ R.testBit W) = decide (2 ^ W < P)
      rw [hbHigh, hbLowEq, hbLow]
      simp [hnot]
    · have hgt : 2 ^ W < P := Nat.lt_of_not_ge hle
      have hLowLtW : low < 2 ^ W := by
        dsimp [low]
        omega
      have hbLow : low.testBit W = false :=
        testBit_false_of_lt_two_pow hLowLtW
      change (R.testBit (W + 1) ^^ R.testBit W) = decide (2 ^ W < P)
      rw [hbHigh, hbLowEq, hbLow]
      simp [hgt]

private theorem no_highPair_succ_product_bound {W X Y : Nat}
    (hX : X < 2 ^ W) (hY : Y < 2 ^ W)
    (hNo : ¬ highPair W X Y) :
    (X + 1) * (Y + 1) ≤ 2 ^ (W + 1) := by
  by_cases hY0 : Y = 0
  · subst Y
    have hx1 : X + 1 ≤ 2 ^ W := Nat.succ_le_of_lt hX
    exact Nat.le_trans (by simpa using hx1)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : W ≤ W + 1))
  · let i := Y.log2
    have hlog := (Nat.log2_eq_iff (n := Y) (k := i) hY0).mp rfl
    have hiW : i < W := by
      have hlogLt : Y.log2 < W := (Nat.log2_lt hY0).mpr hY
      simpa [i] using hlogLt
    by_cases hi0 : i = 0
    · have hYlt2 : Y < 2 := by
        simpa [i, hi0] using hlog.2
      have hYeq1 : Y = 1 := by
        have hpos : 0 < Y := Nat.pos_of_ne_zero hY0
        omega
      subst Y
      have hx1 : X + 1 ≤ 2 ^ W := Nat.succ_le_of_lt hX
      calc
        (X + 1) * (1 + 1) = (X + 1) * 2 := by omega
        _ ≤ 2 ^ W * 2 := Nat.mul_le_mul_right 2 hx1
        _ = 2 ^ (W + 1) := by simpa using (pow_two_mul W 1)
    · have hi1 : 1 ≤ i := by omega
      have hbit : Y.testBit i = true := Nat.testBit_log2 hY0
      have hXlt : X < 2 ^ (W - i) := by
        apply Nat.lt_of_not_le
        intro hle
        exact hNo ⟨i, hi1, hiW, hbit, hle⟩
      have hx1 : X + 1 ≤ 2 ^ (W - i) := Nat.succ_le_of_lt hXlt
      have hy1 : Y + 1 ≤ 2 ^ (i + 1) := Nat.succ_le_of_lt hlog.2
      have hmul := Nat.mul_le_mul hx1 hy1
      have hsum : W - i + (i + 1) = W + 1 := by omega
      calc
        (X + 1) * (Y + 1) ≤ 2 ^ (W - i) * 2 ^ (i + 1) := hmul
        _ = 2 ^ (W + 1) := by rw [pow_two_mul, hsum]

private theorem signed_formula_value {W X Y : Nat} {sx sy scan : Bool}
    (hX : X < 2 ^ W) (hY : Y < 2 ^ W)
    (hscan : scan = true ↔ highPair W X Y) :
    (scan || topDiffMag W X Y sx sy) =
      signedOverflowMag W X Y sx sy := by
  let P := (X + inc sx) * (Y + inc sy)
  have hPleMax : P ≤ (X + 1) * (Y + 1) := by
    dsimp [P, inc]
    cases sx <;> cases sy <;> simp
    · exact Nat.mul_le_mul (Nat.le_succ X) (Nat.le_succ Y)
    · exact Nat.mul_le_mul_right (Y + 1) (Nat.le_succ X)
    · exact Nat.mul_le_mul_left (X + 1) (Nat.le_succ Y)
  by_cases hp : highPair W X Y
  · have hscanTrue : scan = true := hscan.2 hp
    have hXYov : 2 ^ W ≤ X * Y := highPair_overflow hp
    have hOverflow : signedOverflowMag W X Y sx sy = true := by
      change
        (if sx = sy then decide (2 ^ W ≤ P) else decide (2 ^ W < P)) =
          true
      by_cases hsame : sx = sy
      · rw [if_pos hsame]
        have hPge : 2 ^ W ≤ P := by
          dsimp [P, inc]
          cases sx <;> cases sy <;> simp [inc] at hsame ⊢
          · exact hXYov
          · exact Nat.le_trans hXYov
              (Nat.mul_le_mul (Nat.le_succ X) (Nat.le_succ Y))
        simp [hPge]
      · rw [if_neg hsame]
        have hYpos : 0 < Y := by
          rcases hp with ⟨_i, _hi1, _hiW, hbit, _⟩
          exact Nat.pos_of_ne_zero (by intro hy0; subst Y; simp at hbit)
        have hXpos : 0 < X := by
          rcases hp with ⟨_i, _hi1, _hiW, _hbit, hle⟩
          exact Nat.pos_of_ne_zero (by intro hx0; subst X; simp at hle)
        have hPgt : 2 ^ W < P := by
          dsimp [P, inc]
          cases sx <;> cases sy <;> simp [inc] at hsame ⊢
          · rw [Nat.mul_add, Nat.mul_one]
            exact Nat.lt_of_le_of_lt hXYov
              (Nat.lt_add_of_pos_right hXpos)
          · rw [Nat.add_mul, Nat.one_mul]
            exact Nat.lt_of_le_of_lt hXYov
              (Nat.lt_add_of_pos_right hYpos)
        simp [hPgt]
    rw [hscanTrue, hOverflow]
    simp
  · have hscanFalse : scan = false :=
      Bool.eq_false_iff.2 (fun hs => hp (hscan.1 hs))
    have hBound : P ≤ 2 ^ (W + 1) :=
      Nat.le_trans hPleMax (no_highPair_succ_product_bound hX hY hp)
    have hTop :
        topDiffMag W X Y sx sy = signedOverflowMag W X Y sx sy := by
      change
        (if sx = sy then P.testBit (W + 1) ^^ P.testBit W
          else
            (let R := if P = 0 then 0 else 2 ^ (W + 2) - P
             R.testBit (W + 1) ^^ R.testBit W)) =
        (if sx = sy then decide (2 ^ W ≤ P) else decide (2 ^ W < P))
      by_cases hsame : sx = sy
      · rw [if_pos hsame, if_pos hsame]
        exact pos_topDiff_eq W P hBound
      · rw [if_neg hsame, if_neg hsame]
        exact neg_topDiff_eq W P hBound
    rw [hscanFalse, hTop]
    simp

private theorem nil_bvxor_bit :
    __eo_nil (Term.UOp UserOp.bvxor)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) =
      Term.Binary 1 0 := by
  native_decide

private theorem nil_bvxor_bitvec_succ_of_ne_stuck
    (w : Nat)
    (hNe :
      __eo_nil (Term.UOp UserOp.bvxor)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int (w + 1)))) ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvxor)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1)))) =
      Term.Binary (native_nat_to_int (w + 1)) 0 := by
  change __eo_to_bin (Term.Numeral (native_nat_to_int (w + 1))) (Term.Numeral 0) =
      Term.Binary (native_nat_to_int (w + 1)) 0
  change
    (native_ite (native_zleq (native_nat_to_int (w + 1)) 4294967296)
        (__eo_mk_binary (native_nat_to_int (w + 1)) 0) Term.Stuck) =
      Term.Binary (native_nat_to_int (w + 1)) 0
  cases hBound : native_zleq (native_nat_to_int (w + 1)) 4294967296
  · exfalso
    apply hNe
    change
      native_ite (native_zleq (native_nat_to_int (w + 1)) 4294967296)
          (__eo_mk_binary (native_nat_to_int (w + 1)) 0) Term.Stuck =
        Term.Stuck
    rw [hBound]
    rfl
  · simp [native_ite, hBound]
    have hNonneg : native_zleq 0 (native_nat_to_int (w + 1)) = true := by
      exact decide_eq_true (Int.natCast_nonneg (w + 1))
    simp [__eo_mk_binary, native_ite, hNonneg]
    unfold native_mod_total
    rw [native_int_pow2_nat (w + 1)]
    exact Int.zero_emod _

private theorem bv1_xor (x y : Bool) :
    __smtx_model_eval_bvxor (bv1 x) (bv1 y) = bv1 (x ^^ y) := by
  cases x <;> cases y <;> native_decide

private theorem smulo_bv_toInt_emod (w : Nat) (x : BitVec w) :
    x.toInt % (2 ^ w : Int) = (x.toNat : Int) := by
  have hc : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by norm_cast
  rw [hc, BitVec.toInt_eq_toNat_bmod, Int.bmod_emod]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast x.isLt)

private theorem smulo_ofInt_toNat_canonical
    (w : Nat) (c : Int) (h0 : 0 ≤ c) (h1 : c < 2 ^ w) :
    (BitVec.ofInt w c).toNat = c.toNat := by
  rw [BitVec.toNat_ofInt]
  congr 1
  exact Int.emod_eq_of_lt h0 (by exact_mod_cast h1)

private theorem smulo_natpow2_eq (w : Nat) :
    native_int_pow2 ((w : Nat) : Int) = (2 : Int) ^ w := by
  have hwnn : ¬ (((w : Nat) : Int) < 0) := by omega
  unfold native_int_pow2 native_zexp_total
  rw [if_neg hwnn, Int.toNat_natCast]

private theorem bvxor_payload_nat
    (w : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2 ^ w)
    (ha0 : 0 ≤ an) (ha1 : an < 2 ^ w) :
    native_mod_total (native_binary_xor ((w : Nat) : Int) cn an)
        (native_int_pow2 ((w : Nat) : Int)) =
      ((cn.toNat ^^^ an.toNat : Nat) : Int) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst w
    rw [show ((2 : Int) ^ 0) = 1 from rfl] at hc1 ha1
    have hcn : cn = 0 := by omega
    have han : an = 0 := by omega
    subst cn
    subst an
    native_decide
  · have hne : native_zeq (((w : Nat) : Int)) 0 = false := by
      simp [native_zeq]
      omega
    have hx :
        native_binary_xor ((w : Nat) : Int) cn an =
          (BitVec.ofInt w cn ^^^ BitVec.ofInt w an).toInt := by
      simp only [native_binary_xor, impl_native_pixor]
      rw [hne, Int.toNat_natCast]
      rfl
    have e1 :
        native_mod_total
            (native_binary_xor ((w : Nat) : Int) cn an)
            (native_int_pow2 ((w : Nat) : Int)) =
          (BitVec.ofInt w cn ^^^ BitVec.ofInt w an).toInt %
            (2 : Int) ^ w := by
      rw [hx]
      simp only [native_mod_total]
      rw [smulo_natpow2_eq]
    rw [e1, smulo_bv_toInt_emod, BitVec.toNat_xor,
      smulo_ofInt_toNat_canonical w cn hc0 hc1,
      smulo_ofInt_toNat_canonical w an ha0 ha1]

private theorem bvxor_value_nat
    (W A B : Nat) (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int W) (A : Int))
        (SmtValue.Binary (native_nat_to_int W) (B : Int)) =
      SmtValue.Binary (native_nat_to_int W) ((A ^^^ B : Nat) : Int) := by
  simp only [__smtx_model_eval_bvxor]
  have hPayload :=
    bvxor_payload_nat W (A : Int) (B : Int)
      (Int.natCast_nonneg A) (by exact_mod_cast hA)
      (Int.natCast_nonneg B) (by exact_mod_cast hB)
  simpa [native_nat_to_int] using
    congrArg (fun p => SmtValue.Binary (native_nat_to_int W) p) hPayload

private theorem xor_zero_nat (A : Nat) : A ^^^ 0 = A := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  simp

private theorem xor_all_ones_nat {w A : Nat} (hA : A < 2 ^ w) :
    A ^^^ (2 ^ w - 1) = 2 ^ w - 1 - A := by
  have hEq :
      (BitVec.ofNat w A ^^^ BitVec.allOnes w).toNat =
        (~~~(BitVec.ofNat w A)).toNat := by
    rw [BitVec.xor_allOnes]
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_allOnes,
    BitVec.toNat_not, BitVec.toNat_ofNat] at hEq
  rw [Nat.mod_eq_of_lt hA] at hEq
  exact hEq

private theorem native_mod_neg_one_pow2_nat (k : Nat) :
    native_mod_total (-1 : Int) (native_int_pow2 (native_nat_to_int k)) =
      ((2 ^ k - 1 : Nat) : Int) := by
  have hposNat : 0 < 2 ^ k := Nat.two_pow_pos k
  unfold native_mod_total
  rw [native_int_pow2_nat k]
  change ((-1 : Int) % ((2 ^ k : Nat) : Int)) =
    ((2 ^ k - 1 : Nat) : Int)
  have hEqMod :
      ((-1 : Int) % ((2 ^ k : Nat) : Int)) =
        (((2 ^ k - 1 : Nat) : Int) % ((2 ^ k : Nat) : Int)) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hsub :
        (-1 : Int) - ((2 ^ k - 1 : Nat) : Int) =
          -((2 ^ k : Nat) : Int) := by
      omega
    rw [hsub]
    exact Int.emod_eq_zero_of_dvd ⟨(-1 : Int), by simp⟩
  rw [hEqMod]
  exact Int.emod_eq_of_lt (by omega) (by omega)

private theorem native_binary_uts_zero_bit : native_binary_uts 1 0 = 0 := by
  native_decide

private theorem native_binary_uts_one_bit : native_binary_uts 1 1 = -1 := by
  native_decide

private theorem eval_numeral_term (M : SmtModel) (n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) =
      SmtValue.Numeral n := by
  show __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
  simp only [__smtx_model_eval]

private theorem sign_extend_bit_value (W : Nat) (bit : Bool) :
    __smtx_model_eval_sign_extend
        (SmtValue.Numeral (native_nat_to_int W)) (bv1 bit) =
      SmtValue.Binary (native_nat_to_int (W + 1))
        (if bit then ((2 ^ (W + 1) - 1 : Nat) : Int) else 0) := by
  have hWidth : ((W : Nat) : Int) + 1 = native_nat_to_int (W + 1) := by
    simp [native_nat_to_int]
  cases bit
  · simp [bv1, __smtx_model_eval_sign_extend, native_binary_uts_zero_bit,
      native_zplus, native_nat_to_int]
    rw [hWidth]
    unfold native_mod_total
    exact Int.zero_emod _
  · simp [bv1, __smtx_model_eval_sign_extend, native_binary_uts_one_bit,
      native_zplus, native_nat_to_int]
    rw [hWidth]
    rw [native_mod_neg_one_pow2_nat (W + 1)]

private theorem smtx_eval_bvxor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvxor x y) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvsmulo_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvsmulo x y) =
      __smtx_model_eval_bvsmulo
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_sign_extend_term_eq
    (M : SmtModel) (n x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.sign_extend n x) =
      __smtx_model_eval_sign_extend
        (__smtx_model_eval M n) (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bvxor_term
    (M : SmtModel) (x y : Term) (bx byv : Bool)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bv1 bx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = bv1 byv) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) =
      bv1 (bx ^^ byv) := by
  show __smtx_model_eval M (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt y)) =
      bv1 (bx ^^ byv)
  rw [smtx_eval_bvxor_term_eq]
  rw [hx, hy]
  exact bv1_xor bx byv

private theorem eval_bvxor_binary_term
    (M : SmtModel) (x y : Term) (W A B : Nat)
    (hA : A < 2 ^ W) (hB : B < 2 ^ W)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int W) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int W) (B : Int)) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) =
      SmtValue.Binary (native_nat_to_int W) ((A ^^^ B : Nat) : Int) := by
  show __smtx_model_eval M (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.Binary (native_nat_to_int W) ((A ^^^ B : Nat) : Int)
  rw [smtx_eval_bvxor_term_eq]
  rw [hx, hy]
  exact bvxor_value_nat W A B hA hB

private theorem eval_bvsmulo_term
    (M : SmtModel) (x y : Term) (vx vy : SmtValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = vx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = vy) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) x) y)) =
      __smtx_model_eval_bvsmulo vx vy := by
  show __smtx_model_eval M (SmtTerm.bvsmulo (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_bvsmulo vx vy
  rw [smtx_eval_bvsmulo_term_eq]
  rw [hx, hy]

private theorem eval_sign_extend_term
    (M : SmtModel) (n x : Term) (vn vx : SmtValue)
    (hn : __smtx_model_eval M (__eo_to_smt n) = vn)
    (hx : __smtx_model_eval M (__eo_to_smt x) = vx) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend n) x)) =
      __smtx_model_eval_sign_extend vn vx := by
  show __smtx_model_eval M (SmtTerm.sign_extend (__eo_to_smt n) (__eo_to_smt x)) =
      __smtx_model_eval_sign_extend vn vx
  rw [smtx_eval_sign_extend_term_eq]
  rw [hn, hx]

private def smuloSignedMagTerm (t : Term) (W : Nat) : Term :=
  let topIdx := Term.Numeral (native_nat_to_int W)
  let topExtract := Term.UOp2 UserOp2.extract topIdx topIdx
  let signExtendTop := Term.UOp1 UserOp1.sign_extend topIdx
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) t)
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.bvxor)
        (__eo_mk_apply signExtendTop (__eo_mk_apply topExtract t)))
      (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof t)))

private theorem term_uop1_ne_stuck (op : UserOp1) (i : Term) :
    Term.UOp1 op i ≠ Term.Stuck := by
  intro h
  cases h

private theorem term_uop2_ne_stuck (op : UserOp2) (i j : Term) :
    Term.UOp2 op i j ≠ Term.Stuck := by
  intro h
  cases h

private theorem term_ne_stuck_of_typeof_bitvec
    {t : Term} {w : Nat}
    (hTy : __eo_typeof t =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    t ≠ Term.Stuck := by
  intro ht
  subst t
  change Term.Stuck =
    Term.Apply (Term.UOp UserOp.BitVec)
      (Term.Numeral (native_nat_to_int w)) at hTy
  cases hTy

private theorem typeof_bvxor_same_bitvec
    (x y : Term) (w : Nat)
    (hxTy : __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hyTy : __eo_typeof y =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  change __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  rw [hxTy, hyTy]
  change
    __eo_requires
      (__eo_eq (Term.Numeral (native_nat_to_int w))
        (Term.Numeral (native_nat_to_int w)))
      (Term.Boolean true)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  simp [__eo_eq, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem typeof_bvor_same_bitvec
    (x y : Term) (w : Nat)
    (hxTy : __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hyTy : __eo_typeof y =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x) y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  change __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  rw [hxTy, hyTy]
  change
    __eo_requires
      (__eo_eq (Term.Numeral (native_nat_to_int w))
        (Term.Numeral (native_nat_to_int w)))
      (Term.Boolean true)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  simp [__eo_eq, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem typeof_bvand_same_bitvec
    (x y : Term) (w : Nat)
    (hxTy : __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hyTy : __eo_typeof y =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  change __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  rw [hxTy, hyTy]
  change
    __eo_requires
      (__eo_eq (Term.Numeral (native_nat_to_int w))
        (Term.Numeral (native_nat_to_int w)))
      (Term.Boolean true)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  simp [__eo_eq, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem typeof_sign_extend_bit_to_succ
    (x : Term) (W : Nat)
    (hxTy : __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) :
    __eo_typeof
        (Term.Apply
          (Term.UOp1 UserOp1.sign_extend
            (Term.Numeral (native_nat_to_int W))) x) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))) := by
  change
    __eo_typeof_zero_extend (Term.UOp UserOp.Int)
      (Term.Numeral (native_nat_to_int W)) (__eo_typeof x) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1)))
  rw [hxTy]
  change
    __eo_requires
      (__eo_gt (Term.Numeral (native_nat_to_int W))
        (Term.Numeral (-1 : native_Int)))
      (Term.Boolean true)
      (__eo_mk_apply (Term.UOp UserOp.BitVec)
        (__eo_add (Term.Numeral 1)
          (Term.Numeral (native_nat_to_int W)))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1)))
  have hGt :
      __eo_gt (Term.Numeral (native_nat_to_int W))
        (Term.Numeral (-1 : native_Int)) =
        Term.Boolean true := by
    have hlt : (-1 : Int) < (W : Int) := by omega
    simp [__eo_gt, native_zlt, native_nat_to_int, hlt]
  have hAdd :
      __eo_add (Term.Numeral 1) (Term.Numeral (native_nat_to_int W)) =
        Term.Numeral (native_nat_to_int (W + 1)) := by
    have hEq : (1 : Int) + (W : Int) = ((W + 1 : Nat) : Int) := by omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  rw [hGt, hAdd]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.BitVec)
    (term_numeral_ne_stuck _)

private def smScanRec (W X Y : Nat) : Nat -> Nat -> Bool -> Bool -> Bool
  | _start, 0, _ppc, res => res
  | start, len + 1, ppc, res =>
      let next := X.testBit (W - 1 - start) || ppc
      smScanRec W X Y (start + 1) len next
        (res || (Y.testBit (start + 1) && next))

private theorem smScanRec_eq_or_scanPair
    (W X Y start len : Nat) (ppc res : Bool) :
    smScanRec W X Y start len ppc res =
      (res ||
        scanPair W X Y (start + 1) len
          (X.testBit (W - 1 - start) || ppc)) := by
  induction len generalizing start ppc res with
  | zero =>
      simp [smScanRec, scanPair]
  | succ len ih =>
      simp [smScanRec, scanPair, ih]
      let next := X.testBit (W - 1 - start) || ppc
      let tail :=
        scanPair W X Y (start + 2) len
          (X.testBit (W - 1 - (start + 1)) || next)
      cases res <;> cases Y.testBit (start + 1) <;>
        cases next <;> cases tail <;> rfl

private theorem smScanRec_iff_highPair {W X Y : Nat}
    (hW : 2 ≤ W) (hX : X < 2 ^ W) :
    smScanRec W X Y 1 (W - 2) (X.testBit (W - 1))
        (Y.testBit 1 && X.testBit (W - 1)) = true ↔
      highPair W X Y := by
  rw [smScanRec_eq_or_scanPair]
  have hScan :=
    scanPair_iff_highPair (w := W) (a := X) (b := Y) (by omega) hX
  have hSplit :
      scanPair W X Y 1 (W - 1) (X.testBit (W - 1)) =
        ((Y.testBit 1 && X.testBit (W - 1)) ||
          scanPair W X Y 2 (W - 2)
            (X.testBit (W - 1 - 1) || X.testBit (W - 1))) := by
    rcases W with _ | W
    · omega
    rcases W with _ | W
    · omega
    simp [scanPair]
  rw [← hScan, hSplit]

private def signedMag (W A : Nat) : Nat :=
  if A.testBit W then 2 ^ (W + 1) - 1 - A else A

private theorem nat_sub_one_sub_add_one_cast {P A : Nat}
    (hA : A < P) :
    ((P - 1 - A : Nat) : Int) + 1 = (P : Int) - (A : Int) := by
  have h : P - 1 - A + 1 = P - A := by omega
  have hcast : ((P - A : Nat) : Int) = (P : Int) - (A : Int) := by omega
  omega

private theorem lt_two_pow_of_top_bit_false {W A : Nat}
    (hA : A < 2 ^ (W + 1)) (hbit : A.testBit W = false) :
    A < 2 ^ W := by
  apply Nat.lt_of_not_le
  intro hge
  have htrue : A.testBit W = true := bit_w_of_range hge hA
  rw [hbit] at htrue
  cases htrue

private theorem signedMag_bound {W A : Nat}
    (hA : A < 2 ^ (W + 1)) :
    signedMag W A < 2 ^ W := by
  by_cases hs : A.testBit W = true
  · have hge : 2 ^ W ≤ A := Nat.ge_two_pow_of_testBit hs
    have hPowSplit : 2 ^ (W + 1) = 2 ^ W + 2 ^ W := by
      have h : 2 ^ (W + 1) = 2 ^ W * 2 :=
        (pow_two_mul W 1).symm
      rw [h]
      omega
    dsimp [signedMag]
    rw [hs]
    rw [hPowSplit]
    have hle : 2 ^ W + 2 ^ W - 1 - A ≤ 2 ^ W - 1 := by
      omega
    exact Nat.lt_of_le_of_lt hle
      (Nat.sub_lt (Nat.two_pow_pos W) (by decide : 0 < 1))
  · have hsFalse : A.testBit W = false := Bool.eq_false_iff.2 hs
    simpa [signedMag, hsFalse] using
      lt_two_pow_of_top_bit_false hA hsFalse

private theorem signedOverflowMag_zero_eq_and
    (A B : Nat) (hA : A < 2 ^ 1) (hB : B < 2 ^ 1) :
    signedOverflowMag 0 (signedMag 0 A) (signedMag 0 B)
        (A.testBit 0) (B.testBit 0) =
      (A.testBit 0 && B.testBit 0) := by
  have hA01 : A = 0 ∨ A = 1 := by omega
  have hB01 : B = 0 ∨ B = 1 := by omega
  rcases hA01 with rfl | rfl <;>
    rcases hB01 with rfl | rfl <;>
    native_decide

private theorem binary_one_eq_bv1_of_lt_two
    (A : Nat) (hA : A < 2) :
    SmtValue.Binary 1 (A : Int) = bv1 (A.testBit 0) := by
  have hA01 : A = 0 ∨ A = 1 := by omega
  rcases hA01 with rfl | rfl <;> native_decide

private theorem signedMag_eq_xor_sign_mask
    (W A : Nat) (hA : A < 2 ^ (W + 1)) :
    A ^^^ (if A.testBit W then 2 ^ (W + 1) - 1 else 0) =
      signedMag W A := by
  cases hs : A.testBit W
  · simp [signedMag, hs, xor_zero_nat]
  · simp [signedMag, hs, xor_all_ones_nat hA]

private theorem eval_smuloSignedMagTerm
    (M : SmtModel) (t : Term) (W A : Nat)
    (hTy : __eo_typeof t =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hEval : __smtx_model_eval M (__eo_to_smt t) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
    (hA : A < 2 ^ (W + 1))
    (hNilNe : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof t) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (smuloSignedMagTerm t W)) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (signedMag W A : Int) := by
  let topIdx := Term.Numeral (native_nat_to_int W)
  let topExtract := Term.UOp2 UserOp2.extract topIdx topIdx
  let signExtendTop := Term.UOp1 UserOp1.sign_extend topIdx
  let topBit := Term.Apply topExtract t
  have htNe : t ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M t (native_nat_to_int (W + 1)) (A : Int) hEval
  have hTopMkEq : __eo_mk_apply topExtract t = topBit := by
    dsimp [topBit]
    exact eo_mk_apply_of_ne_stuck
      (term_uop2_ne_stuck UserOp2.extract topIdx topIdx) htNe
  have hTopEval :
      __smtx_model_eval M (__eo_to_smt topBit) =
        bv1 (A.testBit W) := by
    simpa [topBit, topExtract, topIdx] using
      eval_extract_bit_term M t (native_nat_to_int (W + 1)) (A : Int)
        W hEval (Int.natCast_nonneg A)
  have hTopTy :
      __eo_typeof topBit =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [topBit, topExtract, topIdx] using
      typeof_extract_bit_of_bv t (W + 1) W hTy (by omega)
  have hTopNe : topBit ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M topBit (A.testBit W) hTopEval
  let signExt := Term.Apply signExtendTop topBit
  let signExtRaw := __eo_mk_apply signExtendTop (__eo_mk_apply topExtract t)
  have hSignRawEq : signExtRaw = signExt := by
    dsimp [signExtRaw, signExt]
    rw [hTopMkEq]
    exact eo_mk_apply_of_ne_stuck
      (term_uop1_ne_stuck UserOp1.sign_extend topIdx) hTopNe
  let mask := if A.testBit W then 2 ^ (W + 1) - 1 else 0
  have hMaskBound : mask < 2 ^ (W + 1) := by
    dsimp [mask]
    cases A.testBit W
    · exact Nat.two_pow_pos (W + 1)
    · exact Nat.sub_lt (Nat.two_pow_pos (W + 1)) (by decide : 0 < 1)
  have hSignEval :
      __smtx_model_eval M (__eo_to_smt signExt) =
        SmtValue.Binary (native_nat_to_int (W + 1)) (mask : Int) := by
    dsimp [signExt, signExtendTop, topIdx]
    have h := eval_sign_extend_term M topIdx topBit
      (SmtValue.Numeral (native_nat_to_int W)) (bv1 (A.testBit W))
      (eval_numeral_term M (native_nat_to_int W)) hTopEval
    rw [h]
    have hMaskCast :
        ((mask : Nat) : Int) =
          (if A.testBit W then ((2 ^ (W + 1) - 1 : Nat) : Int) else 0) := by
      dsimp [mask]
      cases A.testBit W <;> rfl
    simpa [mask, hMaskCast] using sign_extend_bit_value W (A.testBit W)
  have hSignNe : signExt ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M signExt (native_nat_to_int (W + 1))
      (mask : Int) hSignEval
  let nilXor := __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof t)
  have hNilEq :
      nilXor = Term.Binary (native_nat_to_int (W + 1)) 0 := by
    dsimp [nilXor]
    rw [hTy]
    exact nil_bvxor_bitvec_succ_of_ne_stuck W (by
      simpa [hTy] using hNilNe)
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nilXor) =
        SmtValue.Binary (native_nat_to_int (W + 1)) 0 := by
    rw [hNilEq]
    exact eval_binary M (native_nat_to_int (W + 1)) 0
  have hNilNe' : nilXor ≠ Term.Stuck := by
    rw [hNilEq]
    exact term_binary_ne_stuck (native_nat_to_int (W + 1)) 0
  let innerHead := __eo_mk_apply (Term.UOp UserOp.bvxor) signExtRaw
  have hInnerHeadEq :
      innerHead = Term.Apply (Term.UOp UserOp.bvxor) signExt := by
    dsimp [innerHead]
    rw [hSignRawEq]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvxor) hSignNe
  let inner := __eo_mk_apply innerHead nilXor
  have hInnerEq :
      inner = Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) signExt) nilXor := by
    dsimp [inner]
    rw [hInnerHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilNe'
  have hInnerEval :
      __smtx_model_eval M (__eo_to_smt inner) =
        SmtValue.Binary (native_nat_to_int (W + 1)) (mask : Int) := by
    rw [hInnerEq]
    have h := eval_bvxor_binary_term M signExt nilXor (W + 1) mask 0
      hMaskBound (Nat.two_pow_pos (W + 1)) hSignEval hNilEval
    simpa [xor_zero_nat] using h
  have hInnerNe : inner ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M inner (native_nat_to_int (W + 1))
      (mask : Int) hInnerEval
  have hOuterEq :
      smuloSignedMagTerm t W =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) t) inner := by
    dsimp [smuloSignedMagTerm]
    change __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) t) inner =
      Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) t) inner
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hInnerNe
  rw [hOuterEq]
  have hOuter := eval_bvxor_binary_term M t inner (W + 1) A mask
    hA hMaskBound hEval hInnerEval
  rw [hOuter]
  rw [signedMag_eq_xor_sign_mask W A hA]

private theorem typeof_smuloSignedMagTerm
    (t : Term) (W : Nat)
    (hTy : __eo_typeof t =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hNilNe : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof t) ≠ Term.Stuck) :
    __eo_typeof (smuloSignedMagTerm t W) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))) := by
  let topIdx := Term.Numeral (native_nat_to_int W)
  let topExtract := Term.UOp2 UserOp2.extract topIdx topIdx
  let signExtendTop := Term.UOp1 UserOp1.sign_extend topIdx
  let topBit := Term.Apply topExtract t
  have htNe : t ≠ Term.Stuck := term_ne_stuck_of_typeof_bitvec hTy
  have hTopMkEq : __eo_mk_apply topExtract t = topBit := by
    dsimp [topBit]
    exact eo_mk_apply_of_ne_stuck
      (term_uop2_ne_stuck UserOp2.extract topIdx topIdx) htNe
  have hTopTy :
      __eo_typeof topBit =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [topBit, topExtract, topIdx] using
      typeof_extract_bit_of_bv t (W + 1) W hTy (by omega)
  have hTopNe : topBit ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bitvec (w := 1)
      (by simpa [native_nat_to_int] using hTopTy)
  let signExt := Term.Apply signExtendTop topBit
  let signExtRaw := __eo_mk_apply signExtendTop (__eo_mk_apply topExtract t)
  have hSignRawEq : signExtRaw = signExt := by
    dsimp [signExtRaw, signExt]
    rw [hTopMkEq]
    exact eo_mk_apply_of_ne_stuck
      (term_uop1_ne_stuck UserOp1.sign_extend topIdx) hTopNe
  have hSignTy :
      __eo_typeof signExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 1))) := by
    simpa [signExt, signExtendTop, topIdx] using
      typeof_sign_extend_bit_to_succ topBit W hTopTy
  have hSignNe : signExt ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bitvec hSignTy
  let nilXor := __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof t)
  have hNilEq :
      nilXor = Term.Binary (native_nat_to_int (W + 1)) 0 := by
    dsimp [nilXor]
    rw [hTy]
    exact nil_bvxor_bitvec_succ_of_ne_stuck W (by
      simpa [hTy] using hNilNe)
  have hNilTy :
      __eo_typeof nilXor =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 1))) := by
    rw [hNilEq]
    exact typeof_binary_bitvec_nat (W + 1) 0
  have hNilNe' : nilXor ≠ Term.Stuck := by
    rw [hNilEq]
    exact term_binary_ne_stuck (native_nat_to_int (W + 1)) 0
  let innerHead := __eo_mk_apply (Term.UOp UserOp.bvxor) signExtRaw
  have hInnerHeadEq :
      innerHead = Term.Apply (Term.UOp UserOp.bvxor) signExt := by
    dsimp [innerHead]
    rw [hSignRawEq]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvxor) hSignNe
  let inner := __eo_mk_apply innerHead nilXor
  have hInnerEq :
      inner = Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) signExt) nilXor := by
    dsimp [inner]
    rw [hInnerHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilNe'
  have hInnerTy :
      __eo_typeof inner =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 1))) := by
    rw [hInnerEq]
    exact typeof_bvxor_same_bitvec signExt nilXor (W + 1) hSignTy hNilTy
  have hInnerNe : inner ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bitvec hInnerTy
  have hOuterEq :
      smuloSignedMagTerm t W =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) t) inner := by
    dsimp [smuloSignedMagTerm]
    change __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) t) inner =
      Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) t) inner
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hInnerNe
  rw [hOuterEq]
  exact typeof_bvxor_same_bitvec t inner (W + 1) hTy hInnerTy

private theorem native_binary_uts_signedMag
    (W A : Nat) (hA : A < 2 ^ (W + 1)) :
    native_binary_uts (native_nat_to_int (W + 1)) (A : Int) =
      if A.testBit W then
        -(((signedMag W A + 1 : Nat) : Int))
      else
        (signedMag W A : Int) := by
  have hPred :
      native_zplus (native_nat_to_int (W + 1)) (native_zneg 1) =
        native_nat_to_int W := by
    have hEq : (((W + 1 : Nat) : Int) + -1 : Int) = (W : Int) := by omega
    simpa [native_zplus, native_zneg, native_nat_to_int] using hEq
  cases hs : A.testBit W
  · have hlt : A < 2 ^ W := lt_two_pow_of_top_bit_false hA hs
    simp [signedMag, hs]
    rw [native_binary_uts]
    change
      native_zplus
          (native_zmult 2
            (native_mod_total (A : Int)
              (native_int_pow2
                (native_zplus (native_nat_to_int (W + 1)) (native_zneg 1)))))
          (native_zneg (A : Int)) =
        (A : Int)
    rw [hPred, native_int_pow2_nat W]
    have hmod :
        native_mod_total (A : Int) (2 ^ W : Int) = (A : Int) :=
      native_mod_nat_of_lt (Nat.two_pow_pos W) hlt
    rw [hmod]
    simp [native_zplus, native_zmult, native_zneg]
    rw [Int.two_mul]
    exact Int.add_neg_cancel_right (A : Int) (A : Int)
  · have hge : 2 ^ W ≤ A := Nat.ge_two_pow_of_testBit hs
    let low := A - 2 ^ W
    have hPowSplit : 2 ^ (W + 1) = 2 ^ W + 2 ^ W := by
      have h : 2 ^ (W + 1) = 2 ^ W * 2 :=
        (pow_two_mul W 1).symm
      rw [h]
      omega
    have hlowLt : low < 2 ^ W := by
      dsimp [low]
      have hlt : A < 2 ^ W + 2 ^ W := by
        simpa [hPowSplit] using hA
      exact Nat.sub_lt_left_of_lt_add hge hlt
    have hAeq : A = 2 ^ W + low := by
      dsimp [low]
      omega
    have hmod :
        native_mod_total (A : Int) (2 ^ W : Int) = (low : Int) := by
      unfold native_mod_total
      change ((A : Int) % ((2 ^ W : Nat) : Int)) = (low : Int)
      rw [hAeq]
      norm_cast
      have hmodNat :
          (2 ^ W + low) % 2 ^ W = low := by
        have h :=
          Nat.add_mul_mod_self_left low (2 ^ W) 1
        rw [Nat.mul_one] at h
        rw [Nat.add_comm] at h
        rw [h, Nat.mod_eq_of_lt hlowLt]
      exact hmodNat
    simp [signedMag, hs]
    rw [native_binary_uts]
    change
      native_zplus
          (native_zmult 2
            (native_mod_total (A : Int)
              (native_int_pow2
                (native_zplus (native_nat_to_int (W + 1)) (native_zneg 1)))))
          (native_zneg (A : Int)) =
        -(((2 ^ (W + 1) - 1 - A + 1 : Nat) : Int))
    rw [hPred, native_int_pow2_nat W, hmod]
    simp [native_zplus, native_zmult, native_zneg]
    have hMagCast :
        ((2 ^ (W + 1) - 1 - A : Nat) : Int) + 1 =
          ((2 ^ (W + 1) : Nat) : Int) - (A : Int) :=
      nat_sub_one_sub_add_one_cast hA
    rw [hMagCast]
    change 2 * (low : Int) + -(A : Int) =
      -(((2 ^ (W + 1) : Nat) : Int) - (A : Int))
    rw [hPowSplit, hAeq]
    have hCast1 :
        ((2 ^ W + low : Nat) : Int) =
          ((2 ^ W : Nat) : Int) + (low : Int) := by
      norm_cast
    have hCast2 :
        ((2 ^ W + 2 ^ W : Nat) : Int) =
          ((2 ^ W : Nat) : Int) + ((2 ^ W : Nat) : Int) := by
      norm_cast
    rw [Int.two_mul, hCast1, hCast2]
    omega

private theorem bvsmulo_value
    (W A B : Nat)
    (hA : A < 2 ^ (W + 1)) (hB : B < 2 ^ (W + 1)) :
    __smtx_model_eval_bvsmulo
        (SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
        (SmtValue.Binary (native_nat_to_int (W + 1)) (B : Int)) =
      SmtValue.Boolean
        (signedOverflowMag W (signedMag W A) (signedMag W B)
          (A.testBit W) (B.testBit W)) := by
  let X := signedMag W A
  let Y := signedMag W B
  have hX : X < 2 ^ W := by simpa [X] using signedMag_bound (W := W) hA
  have hY : Y < 2 ^ W := by simpa [Y] using signedMag_bound (W := W) hB
  have hPow :
      native_int_pow2
          (native_zplus (native_nat_to_int (W + 1)) (native_zneg 1)) =
        ((2 ^ W : Nat) : Int) := by
    have hPred :
        native_zplus (native_nat_to_int (W + 1)) (native_zneg 1) =
          native_nat_to_int W := by
      have hEq : (((W + 1 : Nat) : Int) + -1 : Int) = (W : Int) := by omega
      simpa [native_zplus, native_zneg, native_nat_to_int] using hEq
    rw [hPred, native_int_pow2_nat W]
    norm_cast
  have hUtsA := native_binary_uts_signedMag W A hA
  have hUtsB := native_binary_uts_signedMag W B hB
  change
    SmtValue.Boolean
        (native_or
          (native_zleq
            (native_int_pow2
              (native_zplus (native_nat_to_int (W + 1)) (native_zneg 1)))
            (native_zmult
              (native_binary_uts (native_nat_to_int (W + 1)) (A : Int))
              (native_binary_uts (native_nat_to_int (W + 1)) (B : Int))))
          (native_zlt
            (native_zmult
              (native_binary_uts (native_nat_to_int (W + 1)) (A : Int))
              (native_binary_uts (native_nat_to_int (W + 1)) (B : Int)))
            (native_zneg
              (native_int_pow2
                (native_zplus (native_nat_to_int (W + 1)) (native_zneg 1)))))) =
      SmtValue.Boolean
        (signedOverflowMag W (signedMag W A) (signedMag W B)
          (A.testBit W) (B.testBit W))
  rw [hPow, hUtsA, hUtsB]
  cases hsa : A.testBit W <;> cases hsb : B.testBit W
  · simp [signedOverflowMag, X, Y, hsa, hsb, inc, native_or,
      native_zleq, native_zlt, native_zmult, native_zneg]
    have hProdNonneg :
        (0 : Int) ≤ (signedMag W A : Int) * (signedMag W B : Int) :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hNegPow : -((2 ^ W : Int)) < 0 := by
      have hpos : (0 : Int) < (2 ^ W : Int) := by
        exact_mod_cast Nat.two_pow_pos W
      omega
    have hSecond :
        ¬ ((signedMag W A : Int) * (signedMag W B : Int) <
            -((2 ^ W : Int))) := by
      intro hlt
      omega
    rw [decide_eq_false hSecond]
    by_cases hle : 2 ^ W ≤ signedMag W A * signedMag W B
    · have hleInt :
          (2 ^ W : Int) ≤
            (signedMag W A : Int) * (signedMag W B : Int) := by
        exact_mod_cast hle
      rw [decide_eq_true hleInt, decide_eq_true hle]
      simp
    · have hleInt :
          ¬ (2 ^ W : Int) ≤
            (signedMag W A : Int) * (signedMag W B : Int) := by
        intro h
        exact hle (by exact_mod_cast h)
      rw [decide_eq_false hleInt, decide_eq_false hle]
      simp
  · simp [signedOverflowMag, X, Y, hsa, hsb, inc, native_or,
      native_zleq, native_zlt, native_zmult, native_zneg]
    have hMul :
        (signedMag W A : Int) * -((signedMag W B : Int) + 1) =
          -((signedMag W A : Int) * ((signedMag W B + 1 : Nat) : Int)) := by
      rw [Int.mul_neg]
      simp
    rw [hMul]
    have hPowPos : (0 : Int) < (2 ^ W : Int) := by
      exact_mod_cast Nat.two_pow_pos W
    have hPnonneg :
        (0 : Int) ≤ (signedMag W A : Int) * ((signedMag W B + 1 : Nat) : Int) :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hFirst :
        ¬ (2 ^ W : Int) ≤
          -((signedMag W A : Int) * ((signedMag W B + 1 : Nat) : Int)) := by
      intro hle
      omega
    rw [decide_eq_false hFirst]
    have hIff :
        (-((signedMag W A : Int) * ((signedMag W B + 1 : Nat) : Int)) <
            -((2 ^ W : Int))) ↔
          2 ^ W < signedMag W A * (signedMag W B + 1) := by
      constructor
      · intro h
        have hpos :
            (2 ^ W : Int) <
              (signedMag W A : Int) * ((signedMag W B + 1 : Nat) : Int) := by
          exact (Int.neg_lt_neg_iff.mp h)
        exact_mod_cast hpos
      · intro h
        have hpos :
            (2 ^ W : Int) <
              (signedMag W A : Int) * ((signedMag W B + 1 : Nat) : Int) := by
          exact_mod_cast h
        exact Int.neg_lt_neg hpos
    by_cases hlt : 2 ^ W < signedMag W A * (signedMag W B + 1)
    · rw [decide_eq_true (hIff.2 hlt), decide_eq_true hlt]
      simp
    · rw [decide_eq_false (fun h => hlt (hIff.1 h)), decide_eq_false hlt]
      simp
  · simp [signedOverflowMag, X, Y, hsa, hsb, inc, native_or,
      native_zleq, native_zlt, native_zmult, native_zneg]
    have hMul :
        -((signedMag W A : Int) + 1) * (signedMag W B : Int) =
          -(((signedMag W A + 1 : Nat) : Int) * (signedMag W B : Int)) := by
      rw [Int.neg_mul]
      simp
    rw [hMul]
    have hPnonneg :
        (0 : Int) ≤ ((signedMag W A + 1 : Nat) : Int) * (signedMag W B : Int) :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hFirst :
        ¬ (2 ^ W : Int) ≤
          -(((signedMag W A + 1 : Nat) : Int) * (signedMag W B : Int)) := by
      intro hle
      have hPowPos : (0 : Int) < (2 ^ W : Int) := by
        exact_mod_cast Nat.two_pow_pos W
      omega
    rw [decide_eq_false hFirst]
    have hIff :
        (-(((signedMag W A + 1 : Nat) : Int) * (signedMag W B : Int)) <
            -((2 ^ W : Int))) ↔
          2 ^ W < (signedMag W A + 1) * signedMag W B := by
      constructor
      · intro h
        have hpos :
            (2 ^ W : Int) <
              ((signedMag W A + 1 : Nat) : Int) * (signedMag W B : Int) := by
          exact (Int.neg_lt_neg_iff.mp h)
        exact_mod_cast hpos
      · intro h
        have hpos :
            (2 ^ W : Int) <
              ((signedMag W A + 1 : Nat) : Int) * (signedMag W B : Int) := by
          exact_mod_cast h
        exact Int.neg_lt_neg hpos
    by_cases hlt : 2 ^ W < (signedMag W A + 1) * signedMag W B
    · rw [decide_eq_true (hIff.2 hlt), decide_eq_true hlt]
      simp
    · rw [decide_eq_false (fun h => hlt (hIff.1 h)), decide_eq_false hlt]
      simp
  · simp [signedOverflowMag, X, Y, hsa, hsb, inc, native_or,
      native_zleq, native_zlt, native_zmult, native_zneg]
    have hMul :
        -((signedMag W A : Int) + 1) * -((signedMag W B : Int) + 1) =
          ((signedMag W A + 1 : Nat) : Int) *
            ((signedMag W B + 1 : Nat) : Int) := by
      rw [Int.neg_mul, Int.mul_neg]
      simp
    rw [hMul]
    have hProdNonneg :
        (0 : Int) ≤
          ((signedMag W A + 1 : Nat) : Int) *
            ((signedMag W B + 1 : Nat) : Int) :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hNegFalse :
        ¬ (((signedMag W A + 1 : Nat) : Int) *
              ((signedMag W B + 1 : Nat) : Int) <
            -((2 ^ W : Int))) := by
      intro hlt
      have hPowPos : (0 : Int) < (2 ^ W : Int) := by
        exact_mod_cast Nat.two_pow_pos W
      omega
    rw [decide_eq_false hNegFalse]
    by_cases hle : 2 ^ W ≤ (signedMag W A + 1) * (signedMag W B + 1)
    · have hleInt :
          (2 ^ W : Int) ≤
            ((signedMag W A + 1 : Nat) : Int) *
              ((signedMag W B + 1 : Nat) : Int) := by
        exact_mod_cast hle
      rw [decide_eq_true hleInt, decide_eq_true hle]
      simp
    · have hleInt :
          ¬ (2 ^ W : Int) ≤
            ((signedMag W A + 1 : Nat) : Int) *
              ((signedMag W B + 1 : Nat) : Int) := by
        intro h
        exact hle (by exact_mod_cast h)
      rw [decide_eq_false hleInt, decide_eq_false hle]
      simp

private def signedExtPayload (W A : Nat) : Nat :=
  if A.testBit W then 2 ^ (W + 2) - (signedMag W A + 1) else signedMag W A

private theorem signedExtPayload_bound
    {W A : Nat} (hA : A < 2 ^ (W + 1)) :
    signedExtPayload W A < 2 ^ (W + 2) := by
  have hMag : signedMag W A < 2 ^ W := signedMag_bound (W := W) hA
  dsimp [signedExtPayload]
  cases A.testBit W
  · exact Nat.lt_trans hMag
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : W < W + 2))
  · have hpos : 0 < signedMag W A + 1 := Nat.succ_pos _
    exact Nat.sub_lt (Nat.two_pow_pos _) hpos

private theorem native_mod_neg_nat_of_pos_lt
    {k m : Nat} (hm0 : 0 < m) (hm : m < 2 ^ k) :
    native_mod_total (-(m : Int)) (native_int_pow2 (native_nat_to_int k)) =
      ((2 ^ k - m : Nat) : Int) := by
  unfold native_mod_total
  rw [native_int_pow2_nat k]
  change (-(m : Int)) % ((2 ^ k : Nat) : Int) =
    ((2 ^ k - m : Nat) : Int)
  have hEqMod :
      (-(m : Int)) % ((2 ^ k : Nat) : Int) =
        (((2 ^ k - m : Nat) : Int) % ((2 ^ k : Nat) : Int)) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hsub :
        (-(m : Int)) - ((2 ^ k - m : Nat) : Int) =
          -((2 ^ k : Nat) : Int) := by
      omega
    rw [hsub]
    exact Int.emod_eq_zero_of_dvd ⟨(-1 : Int), by simp⟩
  rw [hEqMod]
  exact Int.emod_eq_of_lt (by omega) (by omega)

private theorem sign_extend_one_value
    (W A : Nat) (hA : A < 2 ^ (W + 1)) :
    __smtx_model_eval_sign_extend
        (SmtValue.Numeral 1)
        (SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int)) =
      SmtValue.Binary (native_nat_to_int (W + 2))
        (signedExtPayload W A : Int) := by
  have hWidth :
      native_zplus 1 (native_nat_to_int (W + 1)) =
        native_nat_to_int (W + 2) := by
    have hEq : (1 : Int) + ((W + 1 : Nat) : Int) =
        ((W + 2 : Nat) : Int) := by
      omega
    simpa [native_zplus, native_nat_to_int] using hEq
  have hMag : signedMag W A < 2 ^ W := signedMag_bound (W := W) hA
  have hUts := native_binary_uts_signedMag W A hA
  change
    SmtValue.Binary (native_zplus 1 (native_nat_to_int (W + 1)))
      (native_mod_total
        (native_binary_uts (native_nat_to_int (W + 1)) (A : Int))
        (native_int_pow2 (native_zplus 1 (native_nat_to_int (W + 1))))) =
      SmtValue.Binary (native_nat_to_int (W + 2))
        (signedExtPayload W A : Int)
  rw [hWidth]
  cases hs : A.testBit W
  · rw [hUts]
    simp [hs, signedExtPayload]
    rw [native_int_pow2_nat (W + 2)]
    exact native_mod_nat_of_lt (Nat.two_pow_pos (W + 2))
      (Nat.lt_trans hMag
        (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : W < W + 2)))
  · rw [hUts]
    simp [hs, signedExtPayload]
    exact native_mod_neg_nat_of_pos_lt
      (Nat.succ_pos (signedMag W A))
      (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hMag)
        (Nat.pow_lt_pow_right (by decide : 1 < 2)
          (by omega : W < W + 2)))

private theorem bvmul_value_nat
    (K A B : Nat) :
    __smtx_model_eval_bvmul
        (SmtValue.Binary (native_nat_to_int K) (A : Int))
        (SmtValue.Binary (native_nat_to_int K) (B : Int)) =
      SmtValue.Binary (native_nat_to_int K)
        (((A * B) % 2 ^ K : Nat) : Int) := by
  change
    SmtValue.Binary (native_nat_to_int K)
      (native_mod_total (native_zmult (A : Int) (B : Int))
        (native_int_pow2 (native_nat_to_int K))) =
      SmtValue.Binary (native_nat_to_int K)
        (((A * B) % 2 ^ K : Nat) : Int)
  simp [native_zmult]
  unfold native_mod_total
  rw [native_int_pow2_nat K]

private def smuloSignExtendOneTerm (t : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral 1)) t

private def smuloProductTerm (a b : Term) : Term :=
  let aExt := smuloSignExtendOneTerm a
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt)
    (__eo_mk_apply
      (Term.Apply (Term.UOp UserOp.bvmul) (smuloSignExtendOneTerm b))
      (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)))

private theorem typeof_sign_extend_one_of_bv
    (a : Term) (W : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1)))) :
    __eo_typeof (smuloSignExtendOneTerm a) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 2))) := by
  dsimp [smuloSignExtendOneTerm]
  change
    __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral 1)
      (__eo_typeof a) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 2)))
  rw [haTy]
  change
    __eo_requires
      (__eo_gt (Term.Numeral 1) (Term.Numeral (-1 : native_Int)))
      (Term.Boolean true)
      (__eo_mk_apply (Term.UOp UserOp.BitVec)
        (__eo_add (Term.Numeral (native_nat_to_int (W + 1)))
          (Term.Numeral 1))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 2)))
  have hGt :
      __eo_gt (Term.Numeral 1) (Term.Numeral (-1 : native_Int)) =
        Term.Boolean true := by
    native_decide
  have hAdd :
      __eo_add (Term.Numeral (native_nat_to_int (W + 1))) (Term.Numeral 1) =
        Term.Numeral (native_nat_to_int (W + 2)) := by
    simp [__eo_add, native_zplus, native_nat_to_int, Int.add_assoc]
  rw [hGt, hAdd]
  change
    __eo_requires (Term.Boolean true) (Term.Boolean true)
      (__eo_mk_apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 2)))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 2)))
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.BitVec)
    (term_numeral_ne_stuck _)

private theorem eval_smuloProductTerm
    (M : SmtModel) (a b : Term) (W A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (B : Int))
    (haBound : A < 2 ^ (W + 1)) (hbBound : B < 2 ^ (W + 1))
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (smuloSignExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (smuloProductTerm a b)) =
      SmtValue.Binary (native_nat_to_int (W + 2))
        (((signedExtPayload W A) * (signedExtPayload W B)) %
          2 ^ (W + 2) : Nat) := by
  let aExt := smuloSignExtendOneTerm a
  let bExt := smuloSignExtendOneTerm b
  have haExtEval :
      __smtx_model_eval M (__eo_to_smt aExt) =
        SmtValue.Binary (native_nat_to_int (W + 2))
          (signedExtPayload W A : Int) := by
    simpa [aExt, smuloSignExtendOneTerm] using
      (eval_sign_extend_term M (Term.Numeral 1) a
        (SmtValue.Numeral 1)
        (SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
        (eval_numeral_term M 1) haEval).trans
        (sign_extend_one_value W A haBound)
  have hbExtEval :
      __smtx_model_eval M (__eo_to_smt bExt) =
        SmtValue.Binary (native_nat_to_int (W + 2))
          (signedExtPayload W B : Int) := by
    simpa [bExt, smuloSignExtendOneTerm] using
      (eval_sign_extend_term M (Term.Numeral 1) b
        (SmtValue.Numeral 1)
        (SmtValue.Binary (native_nat_to_int (W + 1)) (B : Int))
        (eval_numeral_term M 1) hbEval).trans
        (sign_extend_one_value W B hbBound)
  have haExtTy :
      __eo_typeof aExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 2))) := by
    simpa [aExt] using typeof_sign_extend_one_of_bv a W haTy
  let nilMul := __eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)
  have hNilNe' : nilMul ≠ Term.Stuck := by
    simpa [nilMul, aExt] using hNilNe
  have hNilEq :
      nilMul = Term.Binary (native_nat_to_int (W + 2)) 1 := by
    dsimp [nilMul]
    rw [haExtTy]
    exact nil_bvmul_bitvec_succ_of_ne_stuck (W + 1) (by
      simpa [nilMul, haExtTy] using hNilNe')
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nilMul) =
        SmtValue.Binary (native_nat_to_int (W + 2)) 1 := by
    rw [hNilEq]
    change __smtx_model_eval M
      (SmtTerm.Binary (native_nat_to_int (W + 2)) 1) =
      SmtValue.Binary (native_nat_to_int (W + 2)) 1
    simp only [__smtx_model_eval]
  let bTimesOne := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul
  have hbTimesOneEq :
      bTimesOne = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul := by
    dsimp [bTimesOne]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by rw [hNilEq]; exact term_binary_ne_stuck _ _)
  have hbTimesOneEval :
      __smtx_model_eval M (__eo_to_smt bTimesOne) =
        SmtValue.Binary (native_nat_to_int (W + 2))
          (signedExtPayload W B : Int) := by
    rw [hbTimesOneEq]
    have hMul :=
      eval_bvmul_term M bExt nilMul
        (SmtValue.Binary (native_nat_to_int (W + 2))
          (signedExtPayload W B : Int))
        (SmtValue.Binary (native_nat_to_int (W + 2)) 1)
        hbExtEval hNilEval
    rw [hMul]
    have hBExtBound : signedExtPayload W B < 2 ^ (W + 2) :=
      signedExtPayload_bound hbBound
    simpa [Nat.mod_eq_of_lt hBExtBound] using
      bvmul_value_nat (W + 2) (signedExtPayload W B) 1
  have hbTimesOneNe : bTimesOne ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M bTimesOne (native_nat_to_int (W + 2))
      (signedExtPayload W B : Int) hbTimesOneEval
  let product := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne
  have hProductEq :
      product = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne := by
    dsimp [product]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hbTimesOneNe
  have hProductEval :
      __smtx_model_eval M (__eo_to_smt product) =
        SmtValue.Binary (native_nat_to_int (W + 2))
          (((signedExtPayload W A) * (signedExtPayload W B)) %
            2 ^ (W + 2) : Nat) := by
    rw [hProductEq]
    have hMul :=
      eval_bvmul_term M aExt bTimesOne
        (SmtValue.Binary (native_nat_to_int (W + 2))
          (signedExtPayload W A : Int))
        (SmtValue.Binary (native_nat_to_int (W + 2))
          (signedExtPayload W B : Int))
        haExtEval hbTimesOneEval
    rw [hMul]
    exact bvmul_value_nat (W + 2) (signedExtPayload W A)
      (signedExtPayload W B)
  dsimp [smuloProductTerm]
  exact hProductEval

private theorem typeof_smuloProductTerm
    (a b : Term) (W : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (smuloSignExtendOneTerm a)) ≠ Term.Stuck) :
    __eo_typeof (smuloProductTerm a b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 2))) := by
  let aExt := smuloSignExtendOneTerm a
  let bExt := smuloSignExtendOneTerm b
  have haExtTy :
      __eo_typeof aExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 2))) := by
    simpa [aExt] using typeof_sign_extend_one_of_bv a W haTy
  have hbExtTy :
      __eo_typeof bExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 2))) := by
    simpa [bExt] using typeof_sign_extend_one_of_bv b W hbTy
  let nilMul := __eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)
  have hNilNe' : nilMul ≠ Term.Stuck := by
    simpa [nilMul, aExt] using hNilNe
  have hNilEq :
      nilMul = Term.Binary (native_nat_to_int (W + 2)) 1 := by
    dsimp [nilMul]
    rw [haExtTy]
    exact nil_bvmul_bitvec_succ_of_ne_stuck (W + 1) (by
      simpa [nilMul, haExtTy] using hNilNe')
  have hNilTy :
      __eo_typeof nilMul =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 2))) := by
    rw [hNilEq]
    exact typeof_binary_bitvec_nat (W + 2) 1
  let bTimesOne := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul
  have hbTimesOneEq :
      bTimesOne = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul := by
    dsimp [bTimesOne]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by rw [hNilEq]; exact term_binary_ne_stuck _ _)
  have hbTimesOneTy :
      __eo_typeof bTimesOne =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 2))) := by
    rw [hbTimesOneEq]
    exact typeof_bvmul_same_bitvec bExt nilMul (W + 2) hbExtTy hNilTy
  let product := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne
  have hProductEq :
      product = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne := by
    dsimp [product]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by
        intro h
        have hTyStuck : __eo_typeof bTimesOne = __eo_typeof Term.Stuck := by
          rw [h]
        rw [hbTimesOneTy] at hTyStuck
        change Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 2))) = Term.Stuck at hTyStuck
        cases hTyStuck)
  have hProductTy :
      __eo_typeof product =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 2))) := by
    rw [hProductEq]
    exact typeof_bvmul_same_bitvec aExt bTimesOne (W + 2) haExtTy hbTimesOneTy
  dsimp [smuloProductTerm]
  exact hProductTy

private def smuloProdTopDiffTerm (a b : Term) (W : Nat) : Term :=
  let product := smuloProductTerm a b
  let hiIdx := Term.Numeral (native_nat_to_int (W + 1))
  let loIdx := Term.Numeral (native_nat_to_int W)
  let prodHi := __eo_mk_apply (Term.UOp2 UserOp2.extract hiIdx hiIdx) product
  let prodLo := __eo_mk_apply (Term.UOp2 UserOp2.extract loIdx loIdx) product
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.bvxor) prodHi)
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.bvxor) prodLo)
      (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof prodHi)))

private theorem eval_smuloProdTopDiffTerm
    (M : SmtModel) (a b : Term) (W A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (B : Int))
    (haBound : A < 2 ^ (W + 1)) (hbBound : B < 2 ^ (W + 1))
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (smuloSignExtendOneTerm a)) ≠ Term.Stuck) :
    let P :=
      ((signedExtPayload W A) * (signedExtPayload W B)) %
        2 ^ (W + 2)
    __smtx_model_eval M (__eo_to_smt (smuloProdTopDiffTerm a b W)) =
      bv1 (P.testBit (W + 1) ^^ P.testBit W) := by
  let P :=
    ((signedExtPayload W A) * (signedExtPayload W B)) %
      2 ^ (W + 2)
  let product := smuloProductTerm a b
  have hProductEval :
      __smtx_model_eval M (__eo_to_smt product) =
        SmtValue.Binary (native_nat_to_int (W + 2)) (P : Int) := by
    simpa [product, P] using
      eval_smuloProductTerm M a b W A B haTy haEval hbEval
        haBound hbBound hNilNe
  have hProductTy :
      __eo_typeof product =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 2))) := by
    simpa [product] using
      typeof_smuloProductTerm a b W haTy hbTy hNilNe
  have hProductNe : product ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M product (native_nat_to_int (W + 2))
      (P : Int) hProductEval
  let hiIdx := Term.Numeral (native_nat_to_int (W + 1))
  let loIdx := Term.Numeral (native_nat_to_int W)
  let prodHiRaw := __eo_mk_apply (Term.UOp2 UserOp2.extract hiIdx hiIdx) product
  let prodHi := Term.Apply (Term.UOp2 UserOp2.extract hiIdx hiIdx) product
  have hProdHiRawEq : prodHiRaw = prodHi := by
    dsimp [prodHiRaw, prodHi]
    exact eo_mk_apply_of_ne_stuck
      (term_uop2_ne_stuck UserOp2.extract hiIdx hiIdx) hProductNe
  have hProdHiEval :
      __smtx_model_eval M (__eo_to_smt prodHi) =
        bv1 (P.testBit (W + 1)) := by
    simpa [prodHi, hiIdx] using
      eval_extract_bit_term M product (native_nat_to_int (W + 2)) (P : Int)
        (W + 1) hProductEval (Int.natCast_nonneg P)
  have hProdHiTy :
      __eo_typeof prodHi =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [prodHi, hiIdx] using
      typeof_extract_bit_of_bv product (W + 2) (W + 1) hProductTy
        (by omega)
  let prodLoRaw := __eo_mk_apply (Term.UOp2 UserOp2.extract loIdx loIdx) product
  let prodLo := Term.Apply (Term.UOp2 UserOp2.extract loIdx loIdx) product
  have hProdLoRawEq : prodLoRaw = prodLo := by
    dsimp [prodLoRaw, prodLo]
    exact eo_mk_apply_of_ne_stuck
      (term_uop2_ne_stuck UserOp2.extract loIdx loIdx) hProductNe
  have hProdLoEval :
      __smtx_model_eval M (__eo_to_smt prodLo) =
        bv1 (P.testBit W) := by
    simpa [prodLo, loIdx] using
      eval_extract_bit_term M product (native_nat_to_int (W + 2)) (P : Int)
        W hProductEval (Int.natCast_nonneg P)
  have hProdHiNe : prodHi ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M prodHi (P.testBit (W + 1)) hProdHiEval
  have hProdLoNe : prodLo ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M prodLo (P.testBit W) hProdLoEval
  let nilXor := __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof prodHiRaw)
  have hNilXorEq : nilXor = Term.Binary 1 0 := by
    dsimp [nilXor]
    rw [hProdHiRawEq, hProdHiTy, nil_bvxor_bit]
  have hNilXorEval :
      __smtx_model_eval M (__eo_to_smt nilXor) = bv1 false := by
    rw [hNilXorEq]
    simpa [bv1] using eval_binary M 1 0
  have hNilXorNe : nilXor ≠ Term.Stuck := by
    rw [hNilXorEq]
    exact term_binary_ne_stuck 1 0
  let loXorHead := __eo_mk_apply (Term.UOp UserOp.bvxor) prodLoRaw
  have hLoXorHeadEq :
      loXorHead = Term.Apply (Term.UOp UserOp.bvxor) prodLo := by
    dsimp [loXorHead]
    rw [hProdLoRawEq]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvxor)
      hProdLoNe
  let loXorNil := __eo_mk_apply loXorHead nilXor
  have hLoXorNilEq :
      loXorNil =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) prodLo) nilXor := by
    dsimp [loXorNil]
    rw [hLoXorHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilXorNe
  have hLoXorNilEval :
      __smtx_model_eval M (__eo_to_smt loXorNil) =
        bv1 (P.testBit W) := by
    rw [hLoXorNilEq]
    have h := eval_bvxor_term M prodLo nilXor (P.testBit W) false
      hProdLoEval hNilXorEval
    simpa using h
  have hLoXorNilNe : loXorNil ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M loXorNil (P.testBit W) hLoXorNilEval
  let hiXorHead := __eo_mk_apply (Term.UOp UserOp.bvxor) prodHiRaw
  have hHiXorHeadEq :
      hiXorHead = Term.Apply (Term.UOp UserOp.bvxor) prodHi := by
    dsimp [hiXorHead]
    rw [hProdHiRawEq]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvxor)
      hProdHiNe
  let topDiff := __eo_mk_apply hiXorHead loXorNil
  have hTopDiffEq :
      topDiff =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) prodHi) loXorNil := by
    dsimp [topDiff]
    rw [hHiXorHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hLoXorNilNe
  have hTopDiffEval :
      __smtx_model_eval M (__eo_to_smt topDiff) =
        bv1 (P.testBit (W + 1) ^^ P.testBit W) := by
    rw [hTopDiffEq]
    exact eval_bvxor_term M prodHi loXorNil
      (P.testBit (W + 1)) (P.testBit W) hProdHiEval hLoXorNilEval
  dsimp [smuloProdTopDiffTerm]
  exact hTopDiffEval

private theorem nat_mul_complement_mod_of_lt
    {M x y : Nat} (hM0 : 0 < M) (hy : y ≤ M)
    (hxylt : x * y < M) :
    (x * (M - y)) % M =
      if x * y = 0 then 0 else M - x * y := by
  by_cases hxy0 : x * y = 0
  · rcases Nat.mul_eq_zero.mp hxy0 with hx | hy0
    · subst x
      simp
    · subst y
      have hmod : x * M % M = 0 := by
        rw [Nat.mul_comm]
        exact Nat.mul_mod_right M x
      simpa [hxy0] using hmod
  · have hxpos : 0 < x := by
      exact Nat.pos_of_ne_zero (by intro hx; subst x; simp at hxy0)
    have hEq :
        x * (M - y) = x * M - x * y :=
      Nat.mul_sub_left_distrib x M y
    have hDecomp :
        x * M - x * y = (M - x * y) + M * (x - 1) := by
      have hxEq : x = x - 1 + 1 := by omega
      have hMulEq : x * M = (x - 1) * M + M := by
        calc
          x * M = (x - 1 + 1) * M :=
            congrArg (fun z => z * M) hxEq
          _ = (x - 1) * M + 1 * M := by rw [Nat.add_mul]
          _ = (x - 1) * M + M := by simp
      calc
        x * M - x * y = ((x - 1) * M + M) - x * y := by rw [hMulEq]
        _ = (M - x * y) + (x - 1) * M := by omega
        _ = (M - x * y) + M * (x - 1) := by
          rw [Nat.mul_comm (x - 1) M]
    rw [hEq, hDecomp]
    have hlow : M - x * y < M :=
      Nat.sub_lt hM0 (Nat.pos_of_ne_zero hxy0)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
    simp [hxy0]

private theorem nat_complement_mul_complement_mod_of_lt
    {M a b : Nat} (ha : a ≤ M) (hb : b ≤ M)
    (hsum : a + b ≤ M) (hablt : a * b < M) :
    ((M - a) * (M - b)) % M = a * b := by
  have hLeftAdd :
      (M - a) * (M - b) + (M - a) * b = (M - a) * M := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hb]
  have hAB :
      a * b + (M - a) * b = M * b := by
    rw [← Nat.add_mul]
    rw [Nat.add_sub_of_le ha]
  have hbLeMa : b ≤ M - a := by omega
  have hRightAdd :
      (a * b + M * (M - a - b)) + (M - a) * b =
        (M - a) * M := by
    calc
      (a * b + M * (M - a - b)) + (M - a) * b =
          (a * b + (M - a) * b) + M * (M - a - b) := by
            ac_rfl
      _ = M * b + M * (M - a - b) := by rw [hAB]
      _ = M * (b + (M - a - b)) := by rw [Nat.mul_add]
      _ = M * (M - a) := by rw [Nat.add_sub_of_le hbLeMa]
      _ = (M - a) * M := by rw [Nat.mul_comm]
  have hDecomp :
      (M - a) * (M - b) = a * b + M * (M - a - b) := by
    exact Nat.add_right_cancel
      (show
        (M - a) * (M - b) + (M - a) * b =
          (a * b + M * (M - a - b)) + (M - a) * b by
        rw [hLeftAdd, hRightAdd])
  rw [hDecomp]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hablt]

private theorem signedExtProduct_topDiff_eq_of_bound
    (W A B : Nat)
    (hA : A < 2 ^ (W + 1)) (hB : B < 2 ^ (W + 1))
    (hBound :
      (signedMag W A + 1) * (signedMag W B + 1) ≤ 2 ^ (W + 1)) :
    let Pext :=
      ((signedExtPayload W A) * (signedExtPayload W B)) %
        2 ^ (W + 2)
    (Pext.testBit (W + 1) ^^ Pext.testBit W) =
      topDiffMag W (signedMag W A) (signedMag W B)
        (A.testBit W) (B.testBit W) := by
  let X := signedMag W A
  let Y := signedMag W B
  let M := 2 ^ (W + 2)
  have hX : X < 2 ^ W := by
    simpa [X] using signedMag_bound (W := W) hA
  have hY : Y < 2 ^ W := by
    simpa [Y] using signedMag_bound (W := W) hB
  have hX1 : X + 1 ≤ 2 ^ W := Nat.succ_le_of_lt hX
  have hY1 : Y + 1 ≤ 2 ^ W := Nat.succ_le_of_lt hY
  have hBoundXY : (X + 1) * (Y + 1) ≤ 2 ^ (W + 1) := by
    simpa [X, Y] using hBound
  have hPowLt : 2 ^ (W + 1) < M := by
    dsimp [M]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2)
      (by omega : W + 1 < W + 2)
  have hBoundM : (X + 1) * (Y + 1) < M :=
    Nat.lt_of_le_of_lt hBoundXY hPowLt
  have hPowWLeM : 2 ^ W ≤ M := by
    dsimp [M]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  cases hsa : A.testBit W <;> cases hsb : B.testBit W
  · have hPLe : X * Y ≤ (X + 1) * (Y + 1) :=
      Nat.mul_le_mul (Nat.le_succ X) (Nat.le_succ Y)
    have hPlt : X * Y < M := Nat.lt_of_le_of_lt hPLe hBoundM
    have hMod : (X * Y) % M = X * Y := Nat.mod_eq_of_lt hPlt
    simpa [topDiffMag, signedExtPayload, inc, X, Y, M, hsa, hsb, hMod]
  · have hPLe : X * (Y + 1) ≤ (X + 1) * (Y + 1) :=
      Nat.mul_le_mul_right (Y + 1) (Nat.le_succ X)
    have hPlt : X * (Y + 1) < M := Nat.lt_of_le_of_lt hPLe hBoundM
    have hY1M : Y + 1 ≤ M := Nat.le_trans hY1 hPowWLeM
    have hMod :
        (X * (M - (Y + 1))) % M =
          if X * (Y + 1) = 0 then 0 else M - X * (Y + 1) :=
      nat_mul_complement_mod_of_lt (M := M) (x := X) (y := Y + 1)
        (Nat.two_pow_pos (W + 2)) hY1M hPlt
    simpa [topDiffMag, signedExtPayload, inc, X, Y, M, hsa, hsb, hMod]
  · have hPLe : (X + 1) * Y ≤ (X + 1) * (Y + 1) :=
      Nat.mul_le_mul_left (X + 1) (Nat.le_succ Y)
    have hPlt : (X + 1) * Y < M := Nat.lt_of_le_of_lt hPLe hBoundM
    have hX1M : X + 1 ≤ M := Nat.le_trans hX1 hPowWLeM
    have hModRaw :
        (Y * (M - (X + 1))) % M =
          if Y * (X + 1) = 0 then 0 else M - Y * (X + 1) :=
      nat_mul_complement_mod_of_lt (M := M) (x := Y) (y := X + 1)
        (Nat.two_pow_pos (W + 2)) hX1M
        (by simpa [Nat.mul_comm] using hPlt)
    have hMod :
        ((M - (X + 1)) * Y) % M =
          if (X + 1) * Y = 0 then 0 else M - (X + 1) * Y := by
      rw [Nat.mul_comm (M - (X + 1)) Y]
      simpa [Nat.mul_comm] using hModRaw
    simpa [topDiffMag, signedExtPayload, inc, X, Y, M, hsa, hsb, hMod]
  · have hX1M : X + 1 ≤ M := Nat.le_trans hX1 hPowWLeM
    have hY1M : Y + 1 ≤ M := Nat.le_trans hY1 hPowWLeM
    have hPowDouble :
        2 ^ W + 2 ^ W = 2 ^ (W + 1) := by
      have h : 2 ^ (W + 1) = 2 ^ W * 2 :=
        (pow_two_mul W 1).symm
      rw [h]
      omega
    have hSumLeM : (X + 1) + (Y + 1) ≤ M := by
      have hsum : (X + 1) + (Y + 1) ≤ 2 ^ W + 2 ^ W :=
        Nat.add_le_add hX1 hY1
      have hpow : 2 ^ W + 2 ^ W ≤ M := by
        rw [hPowDouble]
        exact Nat.le_of_lt hPowLt
      exact Nat.le_trans hsum hpow
    have hMod :
        ((M - (X + 1)) * (M - (Y + 1))) % M =
          (X + 1) * (Y + 1) :=
      nat_complement_mul_complement_mod_of_lt
        (M := M) (a := X + 1) (b := Y + 1)
        hX1M hY1M hSumLeM hBoundM
    simpa [topDiffMag, signedExtPayload, inc, X, Y, M, hsa, hsb, hMod]

private theorem bvsmulo_typeof_args_of_non_none
    {a b : Term}
    (hNN : term_has_non_none_type
      (SmtTerm.bvsmulo (__eo_to_smt a) (__eo_to_smt b))) :
    ∃ w,
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w := by
  apply bv_binop_ret_args_of_non_none
    (op := SmtTerm.bvsmulo) (ret := SmtType.Bool)
  · rw [__smtx_typeof.eq_def] <;> simp only
  · exact hNN

private def smuloWidthOneBranch (a b : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) a)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) b)
          (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof a)))))
    (Term.Binary 1 1)

private theorem eval_smuloWidthOneBranch
    (M : SmtModel) (a b : Term) (A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary 1 (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary 1 (B : Int))
    (haBound : A < 2) (hbBound : B < 2) :
    __smtx_model_eval M (__eo_to_smt (smuloWidthOneBranch a b)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) := by
  have haEval1 :
      __smtx_model_eval M (__eo_to_smt a) = bv1 (A.testBit 0) := by
    rw [haEval, binary_one_eq_bv1_of_lt_two A haBound]
  have hbEval1 :
      __smtx_model_eval M (__eo_to_smt b) = bv1 (B.testBit 0) := by
    rw [hbEval, binary_one_eq_bv1_of_lt_two B hbBound]
  have haNe : a ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M a (A.testBit 0) haEval1
  have hbNe : b ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M b (B.testBit 0) hbEval1
  let nilAnd := __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof a)
  have hNilAndEq : nilAnd = Term.Binary 1 1 := by
    dsimp [nilAnd]
    rw [haTy, nil_bvand_bit]
  have hNilAndEval :
      __smtx_model_eval M (__eo_to_smt nilAnd) = bv1 true := by
    rw [hNilAndEq]
    simpa [bv1] using eval_binary M 1 1
  have hNilAndNe : nilAnd ≠ Term.Stuck := by
    rw [hNilAndEq]
    exact term_binary_ne_stuck 1 1
  let bAndNil :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) b) nilAnd
  have hBAndNilEq :
      bAndNil =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvand) b) nilAnd := by
    dsimp [bAndNil]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilAndNe
  have hBAndNilEval :
      __smtx_model_eval M (__eo_to_smt bAndNil) = bv1 (B.testBit 0) := by
    rw [hBAndNilEq]
    have h := eval_bvand_term M b nilAnd (B.testBit 0) true
      hbEval1 hNilAndEval
    simpa using h
  have hBAndNilNe : bAndNil ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M bAndNil (B.testBit 0) hBAndNilEval
  let aAnd :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) a) bAndNil
  have hAAndEq :
      aAnd =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) bAndNil := by
    dsimp [aAnd]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hBAndNilNe
  let both := A.testBit 0 && B.testBit 0
  have hAAndEval :
      __smtx_model_eval M (__eo_to_smt aAnd) = bv1 both := by
    rw [hAAndEq]
    exact eval_bvand_term M a bAndNil (A.testBit 0) (B.testBit 0)
      haEval1 hBAndNilEval
  have hAAndNe : aAnd ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M aAnd both hAAndEval
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) aAnd
  have hEqHeadEq :
      eqHead = Term.Apply (Term.UOp UserOp.eq) aAnd := by
    dsimp [eqHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.eq) hAAndNe
  let eqTerm := __eo_mk_apply eqHead (Term.Binary 1 1)
  have hEqTermEq :
      eqTerm =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) aAnd) (Term.Binary 1 1) := by
    dsimp [eqTerm]
    rw [hEqHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (term_binary_ne_stuck 1 1)
  have hBranchEval :
      __smtx_model_eval M (__eo_to_smt (smuloWidthOneBranch a b)) =
        SmtValue.Boolean both := by
    dsimp [smuloWidthOneBranch]
    change __smtx_model_eval M (__eo_to_smt eqTerm) = SmtValue.Boolean both
    rw [hEqTermEq]
    exact eval_eq_bv1_one_term M aAnd both hAAndEval
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) =
        SmtValue.Boolean
          (signedOverflowMag 0 (signedMag 0 A) (signedMag 0 B)
            (A.testBit 0) (B.testBit 0)) := by
    have h := eval_bvsmulo_term M a b
      (SmtValue.Binary 1 (A : Int)) (SmtValue.Binary 1 (B : Int))
      haEval hbEval
    rw [h]
    simpa [native_nat_to_int] using bvsmulo_value 0 A B haBound hbBound
  rw [hBranchEval, hOrigEval]
  rw [signedOverflowMag_zero_eq_and A B (by simpa using haBound)
    (by simpa using hbBound)]

private theorem signedExtProduct_topDiff_width_one_eq_overflow
    (A B : Nat) (hA : A < 2 ^ (1 + 1)) (hB : B < 2 ^ (1 + 1)) :
    let P :=
      ((signedExtPayload 1 A) * (signedExtPayload 1 B)) %
        2 ^ (1 + 2)
    (P.testBit (1 + 1) ^^ P.testBit 1) =
      signedOverflowMag 1 (signedMag 1 A) (signedMag 1 B)
        (A.testBit 1) (B.testBit 1) := by
  have hAcases : A = 0 ∨ A = 1 ∨ A = 2 ∨ A = 3 := by omega
  have hBcases : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := by omega
  rcases hAcases with rfl | rfl | rfl | rfl <;>
    rcases hBcases with rfl | rfl | rfl | rfl <;>
    native_decide

private def smuloProdTopDiffBranch (a b : Term) (W : Nat) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq) (smuloProdTopDiffTerm a b W))
    (Term.Binary 1 1)

private theorem eval_smuloProdTopDiffBranch_width_one
    (M : SmtModel) (a b : Term) (A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int 2)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int 2)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int 2) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int 2) (B : Int))
    (haBound : A < 2 ^ 2) (hbBound : B < 2 ^ 2)
    (hNilMul :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (smuloSignExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (smuloProdTopDiffBranch a b 1)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) := by
  let P :=
    ((signedExtPayload 1 A) * (signedExtPayload 1 B)) %
      2 ^ (1 + 2)
  have hTopEval :
      __smtx_model_eval M (__eo_to_smt (smuloProdTopDiffTerm a b 1)) =
        bv1 (P.testBit (1 + 1) ^^ P.testBit 1) := by
    simpa [P, native_nat_to_int] using
      eval_smuloProdTopDiffTerm M a b 1 A B haTy hbTy haEval hbEval
        (by simpa using haBound) (by simpa using hbBound) hNilMul
  have hTopNe : smuloProdTopDiffTerm a b 1 ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M (smuloProdTopDiffTerm a b 1)
      (P.testBit (1 + 1) ^^ P.testBit 1) hTopEval
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) (smuloProdTopDiffTerm a b 1)
  have hEqHeadEq :
      eqHead = Term.Apply (Term.UOp UserOp.eq) (smuloProdTopDiffTerm a b 1) := by
    dsimp [eqHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.eq) hTopNe
  let eqTerm := __eo_mk_apply eqHead (Term.Binary 1 1)
  have hEqTermEq :
      eqTerm =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) (smuloProdTopDiffTerm a b 1))
          (Term.Binary 1 1) := by
    dsimp [eqTerm]
    rw [hEqHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (term_binary_ne_stuck 1 1)
  have hBranchEval :
      __smtx_model_eval M (__eo_to_smt (smuloProdTopDiffBranch a b 1)) =
        SmtValue.Boolean (P.testBit (1 + 1) ^^ P.testBit 1) := by
    dsimp [smuloProdTopDiffBranch]
    change __smtx_model_eval M (__eo_to_smt eqTerm) =
      SmtValue.Boolean (P.testBit (1 + 1) ^^ P.testBit 1)
    rw [hEqTermEq]
    exact eval_eq_bv1_one_term M (smuloProdTopDiffTerm a b 1)
      (P.testBit (1 + 1) ^^ P.testBit 1) hTopEval
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) =
        SmtValue.Boolean
          (signedOverflowMag 1 (signedMag 1 A) (signedMag 1 B)
            (A.testBit 1) (B.testBit 1)) := by
    have h := eval_bvsmulo_term M a b
      (SmtValue.Binary (native_nat_to_int 2) (A : Int))
      (SmtValue.Binary (native_nat_to_int 2) (B : Int))
      haEval hbEval
    rw [h]
    simpa [native_nat_to_int] using
      bvsmulo_value 1 A B (by simpa using haBound) (by simpa using hbBound)
  rw [hBranchEval, hOrigEval]
  exact congrArg SmtValue.Boolean
    (signedExtProduct_topDiff_width_one_eq_overflow A B
      (by simpa using haBound) (by simpa using hbBound))

private theorem smulo_rec_nil_eq
    {xa xb ppc res nm2 : Term}
    (hxa : xa ≠ Term.Stuck) (hxb : xb ≠ Term.Stuck)
    (hp : ppc ≠ Term.Stuck) (hr : res ≠ Term.Stuck)
    (hnm2 : nm2 ≠ Term.Stuck) :
    __bv_smulo_elim_rec xa xb ppc res
      (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int)) nm2 = res := by
  simp [__bv_smulo_elim_rec, hxa, hxb, hp, hr, hnm2]

private theorem smulo_rec_cons_eq
    {xa xb ppc res i ns nm2 : Term}
    (hxa : xa ≠ Term.Stuck) (hxb : xb ≠ Term.Stuck)
    (hp : ppc ≠ Term.Stuck) (hr : res ≠ Term.Stuck)
    (hnm2 : nm2 ≠ Term.Stuck) :
    __bv_smulo_elim_rec xa xb ppc res
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) i) ns) nm2 =
      (let _v0 := __eo_add i (Term.Numeral 1)
       let _v1 := __eo_mk_apply (Term.UOp2 UserOp2.extract _v0 _v0) xb
       let _v2 := __eo_add nm2 (__eo_neg i)
       let _v3 :=
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) ppc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.bvor)
              (__eo_mk_apply (Term.UOp2 UserOp2.extract _v2 _v2) xa))
            (Term.Binary 1 0))
       __bv_smulo_elim_rec xa xb _v3
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) res)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.bvor)
              (__eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp.bvand) _v1)
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.bvand) _v3)
                  (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof _v1)))))
            (Term.Binary 1 0)))
        ns nm2) := by
  simp [__bv_smulo_elim_rec, hxa, hxb, hp, hr, hnm2]

private theorem smulo_rec_list_stuck_eq
    (xa xb ppc res nm2 : Term) :
    __bv_smulo_elim_rec xa xb ppc res Term.Stuck nm2 = Term.Stuck := by
  by_cases hxa : xa = Term.Stuck
  · subst xa
    exact __bv_smulo_elim_rec.eq_1 xb ppc res Term.Stuck nm2
  by_cases hxb : xb = Term.Stuck
  · subst xb
    exact __bv_smulo_elim_rec.eq_2 xa ppc res Term.Stuck nm2 hxa
  by_cases hp : ppc = Term.Stuck
  · subst ppc
    exact __bv_smulo_elim_rec.eq_3 xa xb res Term.Stuck nm2 hxa hxb
  by_cases hr : res = Term.Stuck
  · subst res
    exact __bv_smulo_elim_rec.eq_4 xa xb ppc Term.Stuck nm2 hxa hxb hp
  by_cases hnm2 : nm2 = Term.Stuck
  · subst nm2
    exact __bv_smulo_elim_rec.eq_5 xa xb ppc res Term.Stuck hxa hxb hp hr
  exact __bv_smulo_elim_rec.eq_8 xa xb ppc res Term.Stuck nm2 hxa hxb hp hr
    (by intro h; cases h)
    (by intro i ns h; cases h)
    hnm2

private theorem smulo_rec_res_stuck_eq
    (xa xb ppc ns nm2 : Term) :
    __bv_smulo_elim_rec xa xb ppc Term.Stuck ns nm2 = Term.Stuck := by
  by_cases hxa : xa = Term.Stuck
  · subst xa
    exact __bv_smulo_elim_rec.eq_1 xb ppc Term.Stuck ns nm2
  by_cases hxb : xb = Term.Stuck
  · subst xb
    exact __bv_smulo_elim_rec.eq_2 xa ppc Term.Stuck ns nm2 hxa
  by_cases hp : ppc = Term.Stuck
  · subst ppc
    exact __bv_smulo_elim_rec.eq_3 xa xb Term.Stuck ns nm2 hxa hxb
  exact __bv_smulo_elim_rec.eq_4 xa xb ppc ns nm2 hxa hxb hp

private theorem smulo_rec_eval
    (M : SmtModel) (xa xb ppc res : Term)
    (W X Y start len : Nat) (ppcB resB : Bool)
    (hxaTy : __eo_typeof xa =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hxbTy : __eo_typeof xb =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hxaEval : __smtx_model_eval M (__eo_to_smt xa) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (X : Int))
    (hxbEval : __smtx_model_eval M (__eo_to_smt xb) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (Y : Int))
    (hppcEval : __smtx_model_eval M (__eo_to_smt ppc) = bv1 ppcB)
    (hresEval : __smtx_model_eval M (__eo_to_smt res) = bv1 resB)
    (hbound : start + len ≤ W - 1) :
    __smtx_model_eval M
      (__eo_to_smt
        (__bv_smulo_elim_rec xa xb ppc res (intRangeList start len)
          (Term.Numeral (native_nat_to_int (W - 1))))) =
      bv1 (smScanRec W X Y start len ppcB resB) := by
  have hxaNe : xa ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M xa (native_nat_to_int (W + 1)) (X : Int)
      hxaEval
  have hxbNe : xb ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M xb (native_nat_to_int (W + 1)) (Y : Int)
      hxbEval
  induction len generalizing start ppc ppcB res resB with
  | zero =>
      have hpNe : ppc ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M ppc ppcB hppcEval
      have hrNe : res ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M res resB hresEval
      change
        __smtx_model_eval M
          (__eo_to_smt
            (__bv_smulo_elim_rec xa xb ppc res
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
                (Term.UOp UserOp.Int))
              (Term.Numeral (native_nat_to_int (W - 1))))) =
          bv1 (smScanRec W X Y start 0 ppcB resB)
      rw [smulo_rec_nil_eq hxaNe hxbNe hpNe hrNe (term_numeral_ne_stuck _)]
      simpa [intRangeList, smScanRec] using hresEval
  | succ len ih =>
      have hpNe : ppc ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M ppc ppcB hppcEval
      have hrNe : res ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M res resB hresEval
      have hstartLt : start < W - 1 := by omega
      have htailBound : start + 1 + len ≤ W - 1 := by omega
      have hIdxPlus :
          __eo_add (Term.Numeral (native_nat_to_int start)) (Term.Numeral 1) =
            Term.Numeral (native_nat_to_int (start + 1)) := by
        simp [__eo_add, native_zplus, native_nat_to_int]
      have hIdxMinus :
          __eo_add (Term.Numeral (native_nat_to_int (W - 1)))
              (__eo_neg (Term.Numeral (native_nat_to_int start))) =
            Term.Numeral (native_nat_to_int (W - 1 - start)) := by
        have hEq :
            (((W - 1 : Nat) : Int) + -((start : Nat) : Int) : Int) =
              ((W - 1 - start : Nat) : Int) := by
          omega
        simp [__eo_add, __eo_neg, native_zplus, native_zneg,
          native_nat_to_int, hEq]
      change
        __smtx_model_eval M
          (__eo_to_smt
            (__bv_smulo_elim_rec xa xb ppc res
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral (native_nat_to_int start)))
                (intRangeList (start + 1) len))
              (Term.Numeral (native_nat_to_int (W - 1))))) =
          bv1 (smScanRec W X Y start (Nat.succ len) ppcB resB)
      rw [smulo_rec_cons_eq hxaNe hxbNe hpNe hrNe (term_numeral_ne_stuck _)]
      rw [hIdxPlus, hIdxMinus]
      let xbIdx := Term.Numeral (native_nat_to_int (start + 1))
      let xaIdx := Term.Numeral (native_nat_to_int (W - 1 - start))
      let v1Raw := __eo_mk_apply (Term.UOp2 UserOp2.extract xbIdx xbIdx) xb
      let v1 := Term.Apply (Term.UOp2 UserOp2.extract xbIdx xbIdx) xb
      let xaBitRaw := __eo_mk_apply (Term.UOp2 UserOp2.extract xaIdx xaIdx) xa
      let xaBit := Term.Apply (Term.UOp2 UserOp2.extract xaIdx xaIdx) xa
      have hv1RawEq : v1Raw = v1 := by
        dsimp [v1Raw, v1]
        exact eo_mk_apply_of_ne_stuck
          (term_uop2_ne_stuck UserOp2.extract xbIdx xbIdx) hxbNe
      have hXaBitRawEq : xaBitRaw = xaBit := by
        dsimp [xaBitRaw, xaBit]
        exact eo_mk_apply_of_ne_stuck
          (term_uop2_ne_stuck UserOp2.extract xaIdx xaIdx) hxaNe
      have hv1Eval :
          __smtx_model_eval M (__eo_to_smt v1) =
            bv1 (Y.testBit (start + 1)) := by
        simpa [v1, xbIdx] using
          eval_extract_bit_term M xb (native_nat_to_int (W + 1)) (Y : Int)
            (start + 1) hxbEval (Int.natCast_nonneg Y)
      have hXaBitEval :
          __smtx_model_eval M (__eo_to_smt xaBit) =
            bv1 (X.testBit (W - 1 - start)) := by
        simpa [xaBit, xaIdx] using
          eval_extract_bit_term M xa (native_nat_to_int (W + 1)) (X : Int)
            (W - 1 - start) hxaEval (Int.natCast_nonneg X)
      have hv1Ty :
          __eo_typeof v1 =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        simpa [v1, xbIdx] using
          typeof_extract_bit_of_bv xb (W + 1) (start + 1) hxbTy (by omega)
      let zero := Term.Binary 1 0
      have hZeroEval :
          __smtx_model_eval M (__eo_to_smt zero) = bv1 false := by
        simpa [zero, bv1] using eval_binary M 1 0
      have hZeroNe : zero ≠ Term.Stuck := by
        dsimp [zero]
        exact term_binary_ne_stuck 1 0
      let xaOrHead := __eo_mk_apply (Term.UOp UserOp.bvor) xaBitRaw
      have hXaOrHeadEq :
          xaOrHead = Term.Apply (Term.UOp UserOp.bvor) xaBit := by
        dsimp [xaOrHead]
        rw [hXaBitRawEq]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
          (term_ne_stuck_of_eval_bv1 M xaBit _ hXaBitEval)
      let xaOrZero := __eo_mk_apply xaOrHead zero
      have hXaOrZeroEq :
          xaOrZero =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) xaBit) zero := by
        dsimp [xaOrZero]
        rw [hXaOrHeadEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hZeroNe
      have hXaOrZeroEval :
          __smtx_model_eval M (__eo_to_smt xaOrZero) =
            bv1 (X.testBit (W - 1 - start)) := by
        rw [hXaOrZeroEq]
        have h := eval_bvor_term M xaBit zero
          (X.testBit (W - 1 - start)) false hXaBitEval hZeroEval
        simpa using h
      have hXaOrZeroNe : xaOrZero ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M xaOrZero _ hXaOrZeroEval
      let newPpc := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) ppc) xaOrZero
      let newPpcB := X.testBit (W - 1 - start) || ppcB
      have hNewPpcEq :
          newPpc =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) ppc) xaOrZero := by
        dsimp [newPpc]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hXaOrZeroNe
      have hNewPpcEval :
          __smtx_model_eval M (__eo_to_smt newPpc) = bv1 newPpcB := by
        rw [hNewPpcEq]
        have h := eval_bvor_term M ppc xaOrZero ppcB
          (X.testBit (W - 1 - start)) hppcEval hXaOrZeroEval
        cases hpv : ppcB <;>
          cases hxv : X.testBit (W - 1 - start) <;>
          simpa [newPpcB, hpv, hxv] using h
      have hNewPpcNe : newPpc ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M newPpc newPpcB hNewPpcEval
      let nilAnd := __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof v1Raw)
      have hNilAndEq : nilAnd = Term.Binary 1 1 := by
        dsimp [nilAnd]
        rw [hv1RawEq, hv1Ty, nil_bvand_bit]
      have hNilAndEval :
          __smtx_model_eval M (__eo_to_smt nilAnd) = bv1 true := by
        rw [hNilAndEq]
        simpa [bv1] using eval_binary M 1 1
      have hNilAndNe : nilAnd ≠ Term.Stuck := by
        rw [hNilAndEq]
        exact term_binary_ne_stuck 1 1
      let ppcAndHead := __eo_mk_apply (Term.UOp UserOp.bvand) newPpc
      have hPpcAndHeadEq :
          ppcAndHead = Term.Apply (Term.UOp UserOp.bvand) newPpc := by
        dsimp [ppcAndHead]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvand)
          hNewPpcNe
      let ppcAndNil := __eo_mk_apply ppcAndHead nilAnd
      have hPpcAndNilEq :
          ppcAndNil =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvand) newPpc) nilAnd := by
        dsimp [ppcAndNil]
        rw [hPpcAndHeadEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilAndNe
      have hPpcAndNilEval :
          __smtx_model_eval M (__eo_to_smt ppcAndNil) = bv1 newPpcB := by
        rw [hPpcAndNilEq]
        have h := eval_bvand_term M newPpc nilAnd newPpcB true
          hNewPpcEval hNilAndEval
        simpa using h
      have hPpcAndNilNe : ppcAndNil ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M ppcAndNil newPpcB hPpcAndNilEval
      let v1AndHead := __eo_mk_apply (Term.UOp UserOp.bvand) v1Raw
      have hV1AndHeadEq :
          v1AndHead = Term.Apply (Term.UOp UserOp.bvand) v1 := by
        dsimp [v1AndHead]
        rw [hv1RawEq]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvand)
          (term_ne_stuck_of_eval_bv1 M v1 _ hv1Eval)
      let headAnd := __eo_mk_apply v1AndHead ppcAndNil
      have hHeadAndEq :
          headAnd =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvand) v1) ppcAndNil := by
        dsimp [headAnd]
        rw [hV1AndHeadEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hPpcAndNilNe
      let headAndB := Y.testBit (start + 1) && newPpcB
      have hHeadAndEval :
          __smtx_model_eval M (__eo_to_smt headAnd) = bv1 headAndB := by
        rw [hHeadAndEq]
        exact eval_bvand_term M v1 ppcAndNil
          (Y.testBit (start + 1)) newPpcB hv1Eval hPpcAndNilEval
      have hHeadAndNe : headAnd ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M headAnd headAndB hHeadAndEval
      let headOrHead := __eo_mk_apply (Term.UOp UserOp.bvor) headAnd
      have hHeadOrHeadEq :
          headOrHead = Term.Apply (Term.UOp UserOp.bvor) headAnd := by
        dsimp [headOrHead]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
          hHeadAndNe
      let headOrZero := __eo_mk_apply headOrHead zero
      have hHeadOrZeroEq :
          headOrZero =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) headAnd) zero := by
        dsimp [headOrZero]
        rw [hHeadOrHeadEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hZeroNe
      have hHeadOrZeroEval :
          __smtx_model_eval M (__eo_to_smt headOrZero) = bv1 headAndB := by
        rw [hHeadOrZeroEq]
        have h := eval_bvor_term M headAnd zero headAndB false
          hHeadAndEval hZeroEval
        simpa using h
      have hHeadOrZeroNe : headOrZero ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M headOrZero headAndB hHeadOrZeroEval
      let newRes := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) res) headOrZero
      let newResB := resB || headAndB
      have hNewResEq :
          newRes =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) res) headOrZero := by
        dsimp [newRes]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hHeadOrZeroNe
      have hNewResEval :
          __smtx_model_eval M (__eo_to_smt newRes) = bv1 newResB := by
        rw [hNewResEq]
        exact eval_bvor_term M res headOrZero resB headAndB
          hresEval hHeadOrZeroEval
      have hTailEval :=
        ih newPpc newRes (start + 1) newPpcB newResB
          hNewPpcEval hNewResEval htailBound
      let tail :=
        __bv_smulo_elim_rec xa xb newPpc newRes
          (intRangeList (start + 1) len)
          (Term.Numeral (native_nat_to_int (W - 1)))
      have hTailEval' :
          __smtx_model_eval M (__eo_to_smt tail) =
            bv1 (smScanRec W X Y (start + 1) len newPpcB newResB) := by
        simpa [tail] using hTailEval
      simpa [smScanRec, xbIdx, xaIdx, v1Raw, xaBitRaw, xaOrHead, xaOrZero,
        newPpc, newPpcB, nilAnd, ppcAndHead, ppcAndNil, v1AndHead,
        headAnd, headAndB, headOrHead, headOrZero, newRes, newResB, tail]
        using hTailEval'

private theorem smulo_rec_type
    (xa xb ppc res : Term)
    (W start len : Nat)
    (hxaTy : __eo_typeof xa =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hxbTy : __eo_typeof xb =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hppcTy : __eo_typeof ppc =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
    (hresTy : __eo_typeof res =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
    (hbound : start + len ≤ W - 1) :
    __eo_typeof
      (__bv_smulo_elim_rec xa xb ppc res (intRangeList start len)
        (Term.Numeral (native_nat_to_int (W - 1)))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  have hxaNe : xa ≠ Term.Stuck := term_ne_stuck_of_typeof_bitvec hxaTy
  have hxbNe : xb ≠ Term.Stuck := term_ne_stuck_of_typeof_bitvec hxbTy
  induction len generalizing start ppc res with
  | zero =>
      have hpNe : ppc ≠ Term.Stuck :=
        term_ne_stuck_of_typeof_bitvec (w := 1)
          (by simpa [native_nat_to_int] using hppcTy)
      have hrNe : res ≠ Term.Stuck :=
        term_ne_stuck_of_typeof_bitvec (w := 1)
          (by simpa [native_nat_to_int] using hresTy)
      change
        __eo_typeof
          (__bv_smulo_elim_rec xa xb ppc res
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
              (Term.UOp UserOp.Int))
            (Term.Numeral (native_nat_to_int (W - 1)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
      rw [smulo_rec_nil_eq hxaNe hxbNe hpNe hrNe (term_numeral_ne_stuck _)]
      exact hresTy
  | succ len ih =>
      have hpNe : ppc ≠ Term.Stuck :=
        term_ne_stuck_of_typeof_bitvec (w := 1)
          (by simpa [native_nat_to_int] using hppcTy)
      have hrNe : res ≠ Term.Stuck :=
        term_ne_stuck_of_typeof_bitvec (w := 1)
          (by simpa [native_nat_to_int] using hresTy)
      have htailBound : start + 1 + len ≤ W - 1 := by omega
      have hIdxPlus :
          __eo_add (Term.Numeral (native_nat_to_int start)) (Term.Numeral 1) =
            Term.Numeral (native_nat_to_int (start + 1)) := by
        simp [__eo_add, native_zplus, native_nat_to_int]
      have hIdxMinus :
          __eo_add (Term.Numeral (native_nat_to_int (W - 1)))
              (__eo_neg (Term.Numeral (native_nat_to_int start))) =
            Term.Numeral (native_nat_to_int (W - 1 - start)) := by
        have hEq :
            (((W - 1 : Nat) : Int) + -((start : Nat) : Int) : Int) =
              ((W - 1 - start : Nat) : Int) := by
          omega
        simp [__eo_add, __eo_neg, native_zplus, native_zneg,
          native_nat_to_int, hEq]
      change
        __eo_typeof
          (__bv_smulo_elim_rec xa xb ppc res
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral (native_nat_to_int start)))
              (intRangeList (start + 1) len))
            (Term.Numeral (native_nat_to_int (W - 1)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
      rw [smulo_rec_cons_eq hxaNe hxbNe hpNe hrNe (term_numeral_ne_stuck _)]
      rw [hIdxPlus, hIdxMinus]
      let xbIdx := Term.Numeral (native_nat_to_int (start + 1))
      let xaIdx := Term.Numeral (native_nat_to_int (W - 1 - start))
      let v1Raw := __eo_mk_apply (Term.UOp2 UserOp2.extract xbIdx xbIdx) xb
      let v1 := Term.Apply (Term.UOp2 UserOp2.extract xbIdx xbIdx) xb
      let xaBitRaw := __eo_mk_apply (Term.UOp2 UserOp2.extract xaIdx xaIdx) xa
      let xaBit := Term.Apply (Term.UOp2 UserOp2.extract xaIdx xaIdx) xa
      have hv1RawEq : v1Raw = v1 := by
        dsimp [v1Raw, v1]
        exact eo_mk_apply_of_ne_stuck
          (term_uop2_ne_stuck UserOp2.extract xbIdx xbIdx) hxbNe
      have hXaBitRawEq : xaBitRaw = xaBit := by
        dsimp [xaBitRaw, xaBit]
        exact eo_mk_apply_of_ne_stuck
          (term_uop2_ne_stuck UserOp2.extract xaIdx xaIdx) hxaNe
      have hv1Ty :
          __eo_typeof v1 =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        simpa [v1, xbIdx] using
          typeof_extract_bit_of_bv xb (W + 1) (start + 1) hxbTy (by omega)
      have hv1RawTy :
          __eo_typeof v1Raw =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hv1RawEq]
        exact hv1Ty
      have hXaBitTy :
          __eo_typeof xaBit =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        simpa [xaBit, xaIdx] using
          typeof_extract_bit_of_bv xa (W + 1) (W - 1 - start) hxaTy
            (by omega)
      have hXaBitRawTy :
          __eo_typeof xaBitRaw =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hXaBitRawEq]
        exact hXaBitTy
      let zero := Term.Binary 1 0
      have hZeroTy :
          __eo_typeof zero =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        simpa [zero, native_nat_to_int] using typeof_binary_bitvec_nat 1 0
      have hZeroNe : zero ≠ Term.Stuck := by
        dsimp [zero]
        exact term_binary_ne_stuck 1 0
      let xaOrHead := __eo_mk_apply (Term.UOp UserOp.bvor) xaBitRaw
      have hXaOrHeadEq :
          xaOrHead = Term.Apply (Term.UOp UserOp.bvor) xaBitRaw := by
        dsimp [xaOrHead]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
          (term_ne_stuck_of_typeof_bitvec (w := 1)
            (by simpa [native_nat_to_int] using hXaBitRawTy))
      let xaOrZero := __eo_mk_apply xaOrHead zero
      have hXaOrZeroEq :
          xaOrZero =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) xaBitRaw) zero := by
        dsimp [xaOrZero]
        rw [hXaOrHeadEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hZeroNe
      have hXaOrZeroTy :
          __eo_typeof xaOrZero =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hXaOrZeroEq]
        exact typeof_bvor_same_bitvec xaBitRaw zero 1
          (by simpa [native_nat_to_int] using hXaBitRawTy)
          (by simpa [native_nat_to_int] using hZeroTy)
      let newPpc := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) ppc) xaOrZero
      have hNewPpcEq :
          newPpc =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) ppc) xaOrZero := by
        dsimp [newPpc]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
          (term_ne_stuck_of_typeof_bitvec (w := 1)
            (by simpa [native_nat_to_int] using hXaOrZeroTy))
      have hNewPpcTy :
          __eo_typeof newPpc =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hNewPpcEq]
        exact typeof_bvor_same_bitvec ppc xaOrZero 1
          (by simpa [native_nat_to_int] using hppcTy)
          (by simpa [native_nat_to_int] using hXaOrZeroTy)
      let nilAnd := __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof v1Raw)
      have hNilAndEq : nilAnd = Term.Binary 1 1 := by
        dsimp [nilAnd]
        rw [hv1RawTy, nil_bvand_bit]
      have hNilAndTy :
          __eo_typeof nilAnd =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hNilAndEq]
        simpa [native_nat_to_int] using typeof_binary_bitvec_nat 1 1
      have hNilAndNe : nilAnd ≠ Term.Stuck := by
        rw [hNilAndEq]
        exact term_binary_ne_stuck 1 1
      let ppcAndHead := __eo_mk_apply (Term.UOp UserOp.bvand) newPpc
      have hPpcAndHeadEq :
          ppcAndHead = Term.Apply (Term.UOp UserOp.bvand) newPpc := by
        dsimp [ppcAndHead]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvand)
          (term_ne_stuck_of_typeof_bitvec (w := 1)
            (by simpa [native_nat_to_int] using hNewPpcTy))
      let ppcAndNil := __eo_mk_apply ppcAndHead nilAnd
      have hPpcAndNilEq :
          ppcAndNil =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvand) newPpc) nilAnd := by
        dsimp [ppcAndNil]
        rw [hPpcAndHeadEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilAndNe
      have hPpcAndNilTy :
          __eo_typeof ppcAndNil =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hPpcAndNilEq]
        exact typeof_bvand_same_bitvec newPpc nilAnd 1
          (by simpa [native_nat_to_int] using hNewPpcTy)
          (by simpa [native_nat_to_int] using hNilAndTy)
      let v1AndHead := __eo_mk_apply (Term.UOp UserOp.bvand) v1Raw
      have hV1AndHeadEq :
          v1AndHead = Term.Apply (Term.UOp UserOp.bvand) v1Raw := by
        dsimp [v1AndHead]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvand)
          (term_ne_stuck_of_typeof_bitvec (w := 1)
            (by simpa [native_nat_to_int] using hv1RawTy))
      let headAnd := __eo_mk_apply v1AndHead ppcAndNil
      have hHeadAndEq :
          headAnd =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvand) v1Raw) ppcAndNil := by
        dsimp [headAnd]
        rw [hV1AndHeadEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
          (term_ne_stuck_of_typeof_bitvec (w := 1)
            (by simpa [native_nat_to_int] using hPpcAndNilTy))
      have hHeadAndTy :
          __eo_typeof headAnd =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hHeadAndEq]
        exact typeof_bvand_same_bitvec v1Raw ppcAndNil 1
          (by simpa [native_nat_to_int] using hv1RawTy)
          (by simpa [native_nat_to_int] using hPpcAndNilTy)
      let headOrHead := __eo_mk_apply (Term.UOp UserOp.bvor) headAnd
      have hHeadOrHeadEq :
          headOrHead = Term.Apply (Term.UOp UserOp.bvor) headAnd := by
        dsimp [headOrHead]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
          (term_ne_stuck_of_typeof_bitvec (w := 1)
            (by simpa [native_nat_to_int] using hHeadAndTy))
      let headOrZero := __eo_mk_apply headOrHead zero
      have hHeadOrZeroEq :
          headOrZero =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) headAnd) zero := by
        dsimp [headOrZero]
        rw [hHeadOrHeadEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hZeroNe
      have hHeadOrZeroTy :
          __eo_typeof headOrZero =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hHeadOrZeroEq]
        exact typeof_bvor_same_bitvec headAnd zero 1
          (by simpa [native_nat_to_int] using hHeadAndTy)
          (by simpa [native_nat_to_int] using hZeroTy)
      let newRes := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) res) headOrZero
      have hNewResEq :
          newRes =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) res) headOrZero := by
        dsimp [newRes]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
          (term_ne_stuck_of_typeof_bitvec (w := 1)
            (by simpa [native_nat_to_int] using hHeadOrZeroTy))
      have hNewResTy :
          __eo_typeof newRes =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        rw [hNewResEq]
        exact typeof_bvor_same_bitvec res headOrZero 1
          (by simpa [native_nat_to_int] using hresTy)
          (by simpa [native_nat_to_int] using hHeadOrZeroTy)
      have hTailTy := ih newPpc newRes (start + 1) hNewPpcTy hNewResTy htailBound
      let tail :=
        __bv_smulo_elim_rec xa xb newPpc newRes
          (intRangeList (start + 1) len)
          (Term.Numeral (native_nat_to_int (W - 1)))
      simpa [tail, xbIdx, xaIdx, v1Raw, xaBitRaw, xaOrHead, xaOrZero,
        newPpc, nilAnd, ppcAndHead, ppcAndNil, v1AndHead, headAnd,
        headOrHead, headOrZero, newRes] using hTailTy

private theorem smulo_indices_eq
    (W : Nat) (hW : 2 ≤ W) :
    __eo_requires
      (__eo_is_neg
        (__eo_add
          (__eo_add (Term.Numeral 1)
            (__eo_add (Term.Numeral (-1 : native_Int))
              (Term.Numeral (native_nat_to_int (W - 1)))))
          (Term.Numeral (-1 : native_Int))))
      (Term.Boolean false)
      (__iota_rec
        (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (__eo_add
            (__eo_add (Term.Numeral 1)
              (__eo_add (Term.Numeral (-1 : native_Int))
                (Term.Numeral (native_nat_to_int (W - 1)))))
            (Term.Numeral (-1 : native_Int))))
        (Term.Numeral 1)) =
      intRangeList 1 (W - 2) := by
  have hInner :
      __eo_add (Term.Numeral (-1 : native_Int))
          (Term.Numeral (native_nat_to_int (W - 1))) =
        Term.Numeral (native_nat_to_int (W - 2)) := by
    have hEq : ((-1 : Int) + ((W - 1 : Nat) : Int) : Int) =
        ((W - 2 : Nat) : Int) := by
      omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  have hLen :
      __eo_add
          (__eo_add (Term.Numeral 1)
            (Term.Numeral (native_nat_to_int (W - 2))))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (W - 2)) := by
    have hEq : ((1 : Int) + ((W - 2 : Nat) : Int) + (-1 : Int) : Int) =
        ((W - 2 : Nat) : Int) := by
      omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  rw [hInner, hLen]
  have hNotNeg :
      __eo_is_neg (Term.Numeral (native_nat_to_int (W - 2))) =
        Term.Boolean false := by
    have hNonneg : ¬ (((W - 2 : Nat) : Int) < 0) :=
      Int.not_lt_of_ge (Int.natCast_nonneg (W - 2))
    simp [__eo_is_neg, native_zlt, native_nat_to_int, hNonneg]
  have hRepeat :
      __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (Term.Numeral (native_nat_to_int (W - 2))) =
        intZeroList (W - 2) := by
    change
      native_ite
        (native_zlt (native_nat_to_int (W - 2)) (0 : native_Int))
        Term.Stuck
        (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (native_int_to_nat (native_nat_to_int (W - 2)))) =
        intZeroList (W - 2)
    have hNegFalse :
        native_zlt (native_nat_to_int (W - 2)) (0 : native_Int) = false := by
      simp only [native_zlt, native_nat_to_int]
      refine decide_eq_false ?_
      show ¬ (((W - 2 : Nat) : Int) < 0)
      omega
    have hToNat :
        native_int_to_nat (native_nat_to_int (W - 2)) = W - 2 := by
      simp [native_int_to_nat, native_nat_to_int]
    rw [hNegFalse, hToNat]
    simp [native_ite]
    exact intZeroList_repeat_rec_eq (W - 2)
  have hIota :
      __iota_rec (intZeroList (W - 2)) (Term.Numeral 1) =
        intRangeList 1 (W - 2) := by
    simpa [native_nat_to_int] using iota_rec_range_eq (W - 2) 1
  rw [hNotNeg, hRepeat, hIota]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

private def smuloScanTerm (a b : Term) (W : Nat) : Term :=
  let xb := smuloSignedMagTerm b W
  let xbBit1 := __eo_mk_apply
    (Term.UOp2 UserOp2.extract (Term.Numeral 1) (Term.Numeral 1)) xb
  let xa := smuloSignedMagTerm a W
  let xaTop := __eo_mk_apply
    (Term.UOp2 UserOp2.extract
      (Term.Numeral (native_nat_to_int (W - 1)))
      (Term.Numeral (native_nat_to_int (W - 1)))) xa
  __bv_smulo_elim_rec xa xb xaTop
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.bvand) xbBit1)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvand) xaTop)
        (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof xbBit1))))
    (intRangeList 1 (W - 2))
    (Term.Numeral (native_nat_to_int (W - 1)))

private theorem eval_smuloScanTerm
    (M : SmtModel) (a b : Term) (W A B : Nat)
    (hW : 2 ≤ W)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (B : Int))
    (haBound : A < 2 ^ (W + 1)) (hbBound : B < 2 ^ (W + 1))
    (hNilXorA : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof a) ≠ Term.Stuck)
    (hNilXorB : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof b) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (smuloScanTerm a b W)) =
      bv1
        (smScanRec W (signedMag W A) (signedMag W B) 1 (W - 2)
          ((signedMag W A).testBit (W - 1))
          ((signedMag W B).testBit 1 &&
            (signedMag W A).testBit (W - 1))) := by
  let xa := smuloSignedMagTerm a W
  let xb := smuloSignedMagTerm b W
  let X := signedMag W A
  let Y := signedMag W B
  have hxaEval :
      __smtx_model_eval M (__eo_to_smt xa) =
        SmtValue.Binary (native_nat_to_int (W + 1)) (X : Int) := by
    simpa [xa, X] using
      eval_smuloSignedMagTerm M a W A haTy haEval haBound hNilXorA
  have hxbEval :
      __smtx_model_eval M (__eo_to_smt xb) =
        SmtValue.Binary (native_nat_to_int (W + 1)) (Y : Int) := by
    simpa [xb, Y] using
      eval_smuloSignedMagTerm M b W B hbTy hbEval hbBound hNilXorB
  have hxaTy :
      __eo_typeof xa =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 1))) := by
    simpa [xa] using typeof_smuloSignedMagTerm a W haTy hNilXorA
  have hxbTy :
      __eo_typeof xb =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 1))) := by
    simpa [xb] using typeof_smuloSignedMagTerm b W hbTy hNilXorB
  have hxaNe : xa ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M xa (native_nat_to_int (W + 1)) (X : Int)
      hxaEval
  have hxbNe : xb ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M xb (native_nat_to_int (W + 1)) (Y : Int)
      hxbEval
  let xbIdx := Term.Numeral 1
  let xbBit1Raw := __eo_mk_apply (Term.UOp2 UserOp2.extract xbIdx xbIdx) xb
  let xbBit1 := Term.Apply (Term.UOp2 UserOp2.extract xbIdx xbIdx) xb
  have hXbBit1RawEq : xbBit1Raw = xbBit1 := by
    dsimp [xbBit1Raw, xbBit1]
    exact eo_mk_apply_of_ne_stuck
      (term_uop2_ne_stuck UserOp2.extract xbIdx xbIdx) hxbNe
  have hXbBit1Eval :
      __smtx_model_eval M (__eo_to_smt xbBit1) = bv1 (Y.testBit 1) := by
    exact eval_extract_bit_term M xb (native_nat_to_int (W + 1)) (Y : Int) 1 hxbEval (Int.natCast_nonneg Y)
  have hXbBit1Ty :
      __eo_typeof xbBit1 =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [xbBit1, xbIdx, native_nat_to_int] using
      typeof_extract_bit_of_bv xb (W + 1) 1 hxbTy (by omega)
  have hXbBit1RawEval :
      __smtx_model_eval M (__eo_to_smt xbBit1Raw) = bv1 (Y.testBit 1) := by
    rw [hXbBit1RawEq]
    exact hXbBit1Eval
  let xaIdx := Term.Numeral (native_nat_to_int (W - 1))
  let xaTopRaw := __eo_mk_apply (Term.UOp2 UserOp2.extract xaIdx xaIdx) xa
  let xaTop := Term.Apply (Term.UOp2 UserOp2.extract xaIdx xaIdx) xa
  have hXaTopRawEq : xaTopRaw = xaTop := by
    dsimp [xaTopRaw, xaTop]
    exact eo_mk_apply_of_ne_stuck
      (term_uop2_ne_stuck UserOp2.extract xaIdx xaIdx) hxaNe
  have hXaTopEval :
      __smtx_model_eval M (__eo_to_smt xaTop) =
        bv1 (X.testBit (W - 1)) := by
    simpa [xaTop, xaIdx] using
      eval_extract_bit_term M xa (native_nat_to_int (W + 1)) (X : Int)
        (W - 1) hxaEval (Int.natCast_nonneg X)
  have hXaTopTy :
      __eo_typeof xaTop =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [xaTop, xaIdx] using
      typeof_extract_bit_of_bv xa (W + 1) (W - 1) hxaTy (by omega)
  have hXaTopRawEval :
      __smtx_model_eval M (__eo_to_smt xaTopRaw) =
        bv1 (X.testBit (W - 1)) := by
    rw [hXaTopRawEq]
    exact hXaTopEval
  have hXaTopRawNe : xaTopRaw ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M xaTopRaw (X.testBit (W - 1))
      hXaTopRawEval
  let nilAnd := __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof xbBit1Raw)
  have hNilAndEq : nilAnd = Term.Binary 1 1 := by
    dsimp [nilAnd]
    rw [hXbBit1RawEq, hXbBit1Ty, nil_bvand_bit]
  have hNilAndEval :
      __smtx_model_eval M (__eo_to_smt nilAnd) = bv1 true := by
    rw [hNilAndEq]
    simpa [bv1] using eval_binary M 1 1
  have hNilAndNe : nilAnd ≠ Term.Stuck := by
    rw [hNilAndEq]
    exact term_binary_ne_stuck 1 1
  let xaTopAndHead := __eo_mk_apply (Term.UOp UserOp.bvand) xaTopRaw
  have hXaTopAndHeadEq :
      xaTopAndHead = Term.Apply (Term.UOp UserOp.bvand) xaTopRaw := by
    dsimp [xaTopAndHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvand)
      hXaTopRawNe
  let xaTopAndNil := __eo_mk_apply xaTopAndHead nilAnd
  have hXaTopAndNilEq :
      xaTopAndNil =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvand) xaTopRaw) nilAnd := by
    dsimp [xaTopAndNil]
    rw [hXaTopAndHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilAndNe
  have hXaTopAndNilEval :
      __smtx_model_eval M (__eo_to_smt xaTopAndNil) =
        bv1 (X.testBit (W - 1)) := by
    rw [hXaTopAndNilEq]
    have h := eval_bvand_term M xaTopRaw nilAnd (X.testBit (W - 1)) true
      hXaTopRawEval hNilAndEval
    simpa using h
  have hXaTopAndNilNe : xaTopAndNil ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M xaTopAndNil (X.testBit (W - 1))
      hXaTopAndNilEval
  let xbBitAndHead := __eo_mk_apply (Term.UOp UserOp.bvand) xbBit1Raw
  have hXbBitAndHeadEq :
      xbBitAndHead = Term.Apply (Term.UOp UserOp.bvand) xbBit1Raw := by
    dsimp [xbBitAndHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvand)
      (term_ne_stuck_of_eval_bv1 M xbBit1Raw (Y.testBit 1) hXbBit1RawEval)
  let initRes := __eo_mk_apply xbBitAndHead xaTopAndNil
  have hInitResEq :
      initRes =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvand) xbBit1Raw)
          xaTopAndNil := by
    dsimp [initRes]
    rw [hXbBitAndHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hXaTopAndNilNe
  have hInitResEval :
      __smtx_model_eval M (__eo_to_smt initRes) =
        bv1 (Y.testBit 1 && X.testBit (W - 1)) := by
    rw [hInitResEq]
    exact eval_bvand_term M xbBit1Raw xaTopAndNil
      (Y.testBit 1) (X.testBit (W - 1)) hXbBit1RawEval hXaTopAndNilEval
  have hRecEval :
      __smtx_model_eval M
        (__eo_to_smt
          (__bv_smulo_elim_rec xa xb xaTopRaw initRes
            (intRangeList 1 (W - 2))
            (Term.Numeral (native_nat_to_int (W - 1))))) =
        bv1
          (smScanRec W X Y 1 (W - 2) (X.testBit (W - 1))
            (Y.testBit 1 && X.testBit (W - 1))) := by
    exact smulo_rec_eval M xa xb xaTopRaw initRes W X Y 1 (W - 2)
      (X.testBit (W - 1)) (Y.testBit 1 && X.testBit (W - 1))
      hxaTy hxbTy hxaEval hxbEval hXaTopRawEval hInitResEval (by omega)
  dsimp [smuloScanTerm]
  simpa [xa, xb, X, Y, xbIdx, xbBit1Raw, xaIdx, xaTopRaw,
    xbBitAndHead, xaTopAndHead, xaTopAndNil, nilAnd, initRes]
    using hRecEval

private theorem typeof_smuloScanTerm
    (a b : Term) (W : Nat)
    (hW : 2 ≤ W)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hNilXorA : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof a) ≠ Term.Stuck)
    (hNilXorB : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof b) ≠ Term.Stuck) :
    __eo_typeof (smuloScanTerm a b W) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  let xa := smuloSignedMagTerm a W
  let xb := smuloSignedMagTerm b W
  have hxaTy :
      __eo_typeof xa =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 1))) := by
    simpa [xa] using typeof_smuloSignedMagTerm a W haTy hNilXorA
  have hxbTy :
      __eo_typeof xb =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (W + 1))) := by
    simpa [xb] using typeof_smuloSignedMagTerm b W hbTy hNilXorB
  have hxaNe : xa ≠ Term.Stuck := term_ne_stuck_of_typeof_bitvec hxaTy
  have hxbNe : xb ≠ Term.Stuck := term_ne_stuck_of_typeof_bitvec hxbTy
  let xbIdx := Term.Numeral 1
  let xbBit1Raw := __eo_mk_apply (Term.UOp2 UserOp2.extract xbIdx xbIdx) xb
  let xbBit1 := Term.Apply (Term.UOp2 UserOp2.extract xbIdx xbIdx) xb
  have hXbBit1RawEq : xbBit1Raw = xbBit1 := by
    dsimp [xbBit1Raw, xbBit1]
    exact eo_mk_apply_of_ne_stuck
      (term_uop2_ne_stuck UserOp2.extract xbIdx xbIdx) hxbNe
  have hXbBit1Ty :
      __eo_typeof xbBit1 =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [xbBit1, xbIdx, native_nat_to_int] using
      typeof_extract_bit_of_bv xb (W + 1) 1 hxbTy (by omega)
  have hXbBit1RawTy :
      __eo_typeof xbBit1Raw =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    rw [hXbBit1RawEq]
    exact hXbBit1Ty
  let xaIdx := Term.Numeral (native_nat_to_int (W - 1))
  let xaTopRaw := __eo_mk_apply (Term.UOp2 UserOp2.extract xaIdx xaIdx) xa
  let xaTop := Term.Apply (Term.UOp2 UserOp2.extract xaIdx xaIdx) xa
  have hXaTopRawEq : xaTopRaw = xaTop := by
    dsimp [xaTopRaw, xaTop]
    exact eo_mk_apply_of_ne_stuck
      (term_uop2_ne_stuck UserOp2.extract xaIdx xaIdx) hxaNe
  have hXaTopTy :
      __eo_typeof xaTop =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [xaTop, xaIdx] using
      typeof_extract_bit_of_bv xa (W + 1) (W - 1) hxaTy (by omega)
  have hXaTopRawTy :
      __eo_typeof xaTopRaw =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    rw [hXaTopRawEq]
    exact hXaTopTy
  let nilAnd := __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof xbBit1Raw)
  have hNilAndEq : nilAnd = Term.Binary 1 1 := by
    dsimp [nilAnd]
    rw [hXbBit1RawTy, nil_bvand_bit]
  have hNilAndTy :
      __eo_typeof nilAnd =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    rw [hNilAndEq]
    simpa [native_nat_to_int] using typeof_binary_bitvec_nat 1 1
  have hNilAndNe : nilAnd ≠ Term.Stuck := by
    rw [hNilAndEq]
    exact term_binary_ne_stuck 1 1
  let xaTopAndHead := __eo_mk_apply (Term.UOp UserOp.bvand) xaTopRaw
  have hXaTopAndHeadEq :
      xaTopAndHead = Term.Apply (Term.UOp UserOp.bvand) xaTopRaw := by
    dsimp [xaTopAndHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvand)
      (term_ne_stuck_of_typeof_bitvec (w := 1)
        (by simpa [native_nat_to_int] using hXaTopRawTy))
  let xaTopAndNil := __eo_mk_apply xaTopAndHead nilAnd
  have hXaTopAndNilEq :
      xaTopAndNil =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvand) xaTopRaw) nilAnd := by
    dsimp [xaTopAndNil]
    rw [hXaTopAndHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilAndNe
  have hXaTopAndNilTy :
      __eo_typeof xaTopAndNil =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    rw [hXaTopAndNilEq]
    exact typeof_bvand_same_bitvec xaTopRaw nilAnd 1
      (by simpa [native_nat_to_int] using hXaTopRawTy)
      (by simpa [native_nat_to_int] using hNilAndTy)
  let xbBitAndHead := __eo_mk_apply (Term.UOp UserOp.bvand) xbBit1Raw
  have hXbBitAndHeadEq :
      xbBitAndHead = Term.Apply (Term.UOp UserOp.bvand) xbBit1Raw := by
    dsimp [xbBitAndHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvand)
      (term_ne_stuck_of_typeof_bitvec (w := 1)
        (by simpa [native_nat_to_int] using hXbBit1RawTy))
  let initRes := __eo_mk_apply xbBitAndHead xaTopAndNil
  have hInitResEq :
      initRes =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvand) xbBit1Raw)
          xaTopAndNil := by
    dsimp [initRes]
    rw [hXbBitAndHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (term_ne_stuck_of_typeof_bitvec (w := 1)
        (by simpa [native_nat_to_int] using hXaTopAndNilTy))
  have hInitResTy :
      __eo_typeof initRes =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    rw [hInitResEq]
    exact typeof_bvand_same_bitvec xbBit1Raw xaTopAndNil 1
      (by simpa [native_nat_to_int] using hXbBit1RawTy)
      (by simpa [native_nat_to_int] using hXaTopAndNilTy)
  have hRecTy :
      __eo_typeof
        (__bv_smulo_elim_rec xa xb xaTopRaw initRes
          (intRangeList 1 (W - 2))
          (Term.Numeral (native_nat_to_int (W - 1)))) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    exact smulo_rec_type xa xb xaTopRaw initRes W 1 (W - 2)
      hxaTy hxbTy hXaTopRawTy hInitResTy (by omega)
  dsimp [smuloScanTerm]
  simpa [xa, xb, xbIdx, xbBit1Raw, xaIdx, xaTopRaw,
    xbBitAndHead, xaTopAndHead, xaTopAndNil, nilAnd, initRes]
    using hRecTy

private def smuloGeneralBranch (a b : Term) (W : Nat) : Term :=
  let scan := smuloScanTerm a b W
  let prodTopDiff := smuloProdTopDiffTerm a b W
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvor) scan)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.bvor) prodTopDiff)
          (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof scan)))))
    (Term.Binary 1 1)

private theorem eval_smuloGeneralBranch
    (M : SmtModel) (a b : Term) (W A B : Nat)
    (hW : 2 ≤ W)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (B : Int))
    (haBound : A < 2 ^ (W + 1)) (hbBound : B < 2 ^ (W + 1))
    (hNilXorA : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof a) ≠ Term.Stuck)
    (hNilXorB : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof b) ≠ Term.Stuck)
    (hNilMul :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (smuloSignExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (smuloGeneralBranch a b W)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) := by
  let X := signedMag W A
  let Y := signedMag W B
  let scanB :=
    smScanRec W X Y 1 (W - 2) (X.testBit (W - 1))
      (Y.testBit 1 && X.testBit (W - 1))
  let P :=
    ((signedExtPayload W A) * (signedExtPayload W B)) %
      2 ^ (W + 2)
  let td := P.testBit (W + 1) ^^ P.testBit W
  let scan := smuloScanTerm a b W
  let prodTopDiff := smuloProdTopDiffTerm a b W
  have hScanEval :
      __smtx_model_eval M (__eo_to_smt scan) = bv1 scanB := by
    simpa [scan, scanB, X, Y] using
      eval_smuloScanTerm M a b W A B hW haTy hbTy haEval hbEval
        haBound hbBound hNilXorA hNilXorB
  have hScanTy :
      __eo_typeof scan =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [scan] using
      typeof_smuloScanTerm a b W hW haTy hbTy hNilXorA hNilXorB
  have hScanNe : scan ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M scan scanB hScanEval
  have hProdTopEval :
      __smtx_model_eval M (__eo_to_smt prodTopDiff) = bv1 td := by
    simpa [prodTopDiff, P, td] using
      eval_smuloProdTopDiffTerm M a b W A B haTy hbTy haEval hbEval
        haBound hbBound hNilMul
  have hProdTopNe : prodTopDiff ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M prodTopDiff td hProdTopEval
  let nilOr := __eo_nil (Term.UOp UserOp.bvor) (__eo_typeof scan)
  have hNilOrEq : nilOr = Term.Binary 1 0 := by
    dsimp [nilOr]
    rw [hScanTy, nil_bvor_bit]
  have hNilOrEval :
      __smtx_model_eval M (__eo_to_smt nilOr) = bv1 false := by
    rw [hNilOrEq]
    simpa [bv1] using eval_binary M 1 0
  have hNilOrNe : nilOr ≠ Term.Stuck := by
    rw [hNilOrEq]
    exact term_binary_ne_stuck 1 0
  let prodOrHead := __eo_mk_apply (Term.UOp UserOp.bvor) prodTopDiff
  have hProdOrHeadEq :
      prodOrHead = Term.Apply (Term.UOp UserOp.bvor) prodTopDiff := by
    dsimp [prodOrHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
      hProdTopNe
  let prodOrNil := __eo_mk_apply prodOrHead nilOr
  have hProdOrNilEq :
      prodOrNil =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvor) prodTopDiff) nilOr := by
    dsimp [prodOrNil]
    rw [hProdOrHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hNilOrNe
  have hProdOrNilEval :
      __smtx_model_eval M (__eo_to_smt prodOrNil) = bv1 td := by
    rw [hProdOrNilEq]
    have h := eval_bvor_term M prodTopDiff nilOr td false
      hProdTopEval hNilOrEval
    simpa using h
  have hProdOrNilNe : prodOrNil ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M prodOrNil td hProdOrNilEval
  let scanOrHead := __eo_mk_apply (Term.UOp UserOp.bvor) scan
  have hScanOrHeadEq :
      scanOrHead = Term.Apply (Term.UOp UserOp.bvor) scan := by
    dsimp [scanOrHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
      hScanNe
  let scanOrProd := __eo_mk_apply scanOrHead prodOrNil
  have hScanOrProdEq :
      scanOrProd =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvor) scan) prodOrNil := by
    dsimp [scanOrProd]
    rw [hScanOrHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hProdOrNilNe
  have hScanOrProdEval :
      __smtx_model_eval M (__eo_to_smt scanOrProd) =
        bv1 (scanB || td) := by
    rw [hScanOrProdEq]
    exact eval_bvor_term M scan prodOrNil scanB td hScanEval hProdOrNilEval
  have hScanOrProdNe : scanOrProd ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M scanOrProd (scanB || td) hScanOrProdEval
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) scanOrProd
  have hEqHeadEq :
      eqHead = Term.Apply (Term.UOp UserOp.eq) scanOrProd := by
    dsimp [eqHead]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.eq)
      hScanOrProdNe
  let eqTerm := __eo_mk_apply eqHead (Term.Binary 1 1)
  have hEqTermEq :
      eqTerm =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) scanOrProd)
          (Term.Binary 1 1) := by
    dsimp [eqTerm]
    rw [hEqHeadEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (term_binary_ne_stuck 1 1)
  have hBranchEval :
      __smtx_model_eval M (__eo_to_smt (smuloGeneralBranch a b W)) =
        SmtValue.Boolean (scanB || td) := by
    dsimp [smuloGeneralBranch]
    change __smtx_model_eval M (__eo_to_smt eqTerm) =
      SmtValue.Boolean (scanB || td)
    rw [hEqTermEq]
    exact eval_eq_bv1_one_term M scanOrProd (scanB || td) hScanOrProdEval
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) =
        SmtValue.Boolean
          (signedOverflowMag W X Y (A.testBit W) (B.testBit W)) := by
    have h := eval_bvsmulo_term M a b
      (SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
      (SmtValue.Binary (native_nat_to_int (W + 1)) (B : Int))
      haEval hbEval
    rw [h]
    simpa [X, Y] using bvsmulo_value W A B haBound hbBound
  have hX : X < 2 ^ W := by
    simpa [X] using signedMag_bound (W := W) haBound
  have hY : Y < 2 ^ W := by
    simpa [Y] using signedMag_bound (W := W) hbBound
  have hScanIff :
      scanB = true ↔ highPair W X Y := by
    simpa [scanB] using smScanRec_iff_highPair (W := W) (X := X) (Y := Y)
      hW hX
  have hBool :
      (scanB || td) =
        signedOverflowMag W X Y (A.testBit W) (B.testBit W) := by
    by_cases hp : highPair W X Y
    · have hScanTrue : scanB = true := hScanIff.2 hp
      have hFormula :=
        signed_formula_value (W := W) (X := X) (Y := Y)
          (sx := A.testBit W) (sy := B.testBit W) (scan := scanB)
          hX hY hScanIff
      have hOverflowTrue :
          signedOverflowMag W X Y (A.testBit W) (B.testBit W) = true := by
        simpa [hScanTrue] using hFormula.symm
      rw [hScanTrue, hOverflowTrue]
      simp
    · have hScanFalse : scanB = false :=
        Bool.eq_false_iff.2 (fun hs => hp (hScanIff.1 hs))
      have hBound :
          (X + 1) * (Y + 1) ≤ 2 ^ (W + 1) :=
        no_highPair_succ_product_bound hX hY hp
      have hTd :
          td =
            topDiffMag W X Y (A.testBit W) (B.testBit W) := by
        simpa [td, P, X, Y] using
          signedExtProduct_topDiff_eq_of_bound W A B haBound hbBound
            (by simpa [X, Y] using hBound)
      have hFormula :=
        signed_formula_value (W := W) (X := X) (Y := Y)
          (sx := A.testBit W) (sy := B.testBit W) (scan := scanB)
          hX hY hScanIff
      have hTopEq :
          topDiffMag W X Y (A.testBit W) (B.testBit W) =
            signedOverflowMag W X Y (A.testBit W) (B.testBit W) := by
        simpa [hScanFalse] using hFormula
      rw [hScanFalse, hTd, hTopEq]
      simp
  rw [hBranchEval, hOrigEval]
  exact congrArg SmtValue.Boolean hBool

private theorem eval_bv_smulo_expanded_width_succ
    (M : SmtModel) (a b : Term) (W A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int (W + 1)) (B : Int))
    (haBound : A < 2 ^ (W + 1)) (hbBound : B < 2 ^ (W + 1))
    (hNilXorA : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof a) ≠ Term.Stuck)
    (hNilXorB : __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof b) ≠ Term.Stuck)
    (hNilMul :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (smuloSignExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (bvSmuloExpanded a b)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) := by
  have hWidth :
      __bv_bitwidth (__eo_typeof a) =
        Term.Numeral (native_nat_to_int (W + 1)) := by
    rw [haTy]
    rfl
  by_cases hW0 : W = 0
  · subst W
    have hCond :
        __eo_eq (Term.Numeral (native_nat_to_int (0 + 1)))
          (Term.Numeral 1) =
          Term.Boolean true := by
      native_decide
    dsimp [bvSmuloExpanded]
    rw [hWidth, hCond]
    simp [__eo_ite, native_ite, native_teq]
    simpa [smuloWidthOneBranch, native_nat_to_int] using
      eval_smuloWidthOneBranch M a b A B
        (by simpa [native_nat_to_int] using haTy)
        (by simpa [native_nat_to_int] using haEval)
        (by simpa [native_nat_to_int] using hbEval)
        (by simpa using haBound) (by simpa using hbBound)
  · by_cases hW1 : W = 1
    · subst W
      have hCond1 :
          __eo_eq (Term.Numeral (native_nat_to_int (1 + 1)))
            (Term.Numeral 1) =
            Term.Boolean false := by
        native_decide
      have hCond2 :
          __eo_eq (Term.Numeral (native_nat_to_int (1 + 1)))
            (Term.Numeral 2) =
            Term.Boolean true := by
        native_decide
      have hTop :
          __eo_add (Term.Numeral (native_nat_to_int (1 + 1)))
            (Term.Numeral (-1 : native_Int)) =
          Term.Numeral (native_nat_to_int 1) := by
        native_decide
      dsimp [bvSmuloExpanded]
      rw [hWidth, hTop, hCond1, hCond2]
      simp [__eo_ite, native_ite, native_teq]
      simpa [smuloProdTopDiffBranch, smuloProdTopDiffTerm,
        smuloProductTerm, smuloSignExtendOneTerm, native_nat_to_int] using
        eval_smuloProdTopDiffBranch_width_one M a b A B
          (by simpa [native_nat_to_int] using haTy)
          (by simpa [native_nat_to_int] using hbTy)
          (by simpa [native_nat_to_int] using haEval)
          (by simpa [native_nat_to_int] using hbEval)
          (by simpa using haBound) (by simpa using hbBound)
          (by simpa [smuloSignExtendOneTerm, native_nat_to_int] using hNilMul)
    · have hWge2 : 2 ≤ W := by omega
      have hCond1 :
          __eo_eq (Term.Numeral (native_nat_to_int (W + 1)))
            (Term.Numeral 1) =
            Term.Boolean false := by
        change Term.Boolean
            (native_teq (Term.Numeral 1)
              (Term.Numeral (native_nat_to_int (W + 1)))) =
          Term.Boolean false
        have hne : ¬ (1 : Int) = (W : Int) + 1 := by
          clear haBound hbBound haEval hbEval A B
          omega
        simp [native_teq, native_nat_to_int, hne]
      have hCond2 :
          __eo_eq (Term.Numeral (native_nat_to_int (W + 1)))
            (Term.Numeral 2) =
            Term.Boolean false := by
        change Term.Boolean
            (native_teq (Term.Numeral 2)
              (Term.Numeral (native_nat_to_int (W + 1)))) =
          Term.Boolean false
        have hne : ¬ (2 : Int) = (W : Int) + 1 := by
          clear haBound hbBound haEval hbEval A B
          omega
        simp [native_teq, native_nat_to_int, hne]
      have hNm2 :
          __eo_add (Term.Numeral (native_nat_to_int (W + 1)))
            (Term.Numeral (-2 : native_Int)) =
          Term.Numeral (native_nat_to_int (W - 1)) := by
        change
          Term.Numeral (native_zplus (native_nat_to_int (W + 1)) (-2)) =
          Term.Numeral (native_nat_to_int (W - 1))
        congr
        have hEq :
            (W : Int) + 1 + (-2 : Int) = ((W - 1 : Nat) : Int) := by
          clear haBound hbBound haEval hbEval A B
          omega
        simpa [native_zplus, native_nat_to_int] using hEq
      have hTop :
          __eo_add (Term.Numeral (native_nat_to_int (W + 1)))
            (Term.Numeral (-1 : native_Int)) =
          Term.Numeral (native_nat_to_int W) := by
        change
          Term.Numeral (native_zplus (native_nat_to_int (W + 1)) (-1)) =
          Term.Numeral (native_nat_to_int W)
        congr
        have hEq : (W : Int) + 1 + (-1 : Int) = (W : Int) := by
          clear haBound hbBound haEval hbEval A B
          omega
        simpa [native_zplus, native_nat_to_int] using hEq
      have hIndices := smulo_indices_eq W hWge2
      dsimp [bvSmuloExpanded]
      rw [hWidth, hNm2, hTop, hCond1, hCond2]
      rw [hIndices]
      simp [__eo_ite, native_ite, native_teq]
      simpa [smuloGeneralBranch, smuloScanTerm, smuloSignedMagTerm,
        smuloProdTopDiffTerm, smuloProductTerm, smuloSignExtendOneTerm,
        native_nat_to_int] using
        eval_smuloGeneralBranch M a b W A B hWge2 haTy hbTy haEval hbEval
          haBound hbBound hNilXorA hNilXorB hNilMul

private theorem bvSmuloExpanded_width_pos
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNe : bvSmuloExpanded a b ≠ Term.Stuck) :
    1 ≤ w := by
  by_cases hw0 : w = 0
  · subst w
    exfalso
    apply hNe
    dsimp [bvSmuloExpanded]
    rw [haTy]
    simp [__bv_bitwidth, __eo_eq, __eo_add, __eo_is_neg, __eo_requires,
      __eo_ite, __eo_mk_apply, __bv_smulo_elim_rec, native_ite,
      native_teq, native_not, SmtEval.native_not, native_zplus,
      native_zlt, native_nat_to_int, smulo_rec_list_stuck_eq]
  · omega

private theorem eo_mk_apply_arg_stuck (f : Term) :
    __eo_mk_apply f Term.Stuck = Term.Stuck := by
  cases f <;> rfl

private theorem eo_mk_apply_fun_stuck (x : Term) :
    __eo_mk_apply Term.Stuck x = Term.Stuck := by
  rfl

private theorem nil_bvxor_a_ne_of_bvSmuloExpanded_ne
    (a b : Term) (W : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hNe : bvSmuloExpanded a b ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof a) ≠ Term.Stuck := by
  by_cases hW0 : W = 0
  · subst W
    rw [haTy]
    native_decide
  by_cases hW1 : W = 1
  · subst W
    rw [haTy]
    native_decide
  have hWge2 : 2 ≤ W := by omega
  intro hNil
  apply hNe
  have hWidth :
      __bv_bitwidth (__eo_typeof a) =
        Term.Numeral (native_nat_to_int (W + 1)) := by
    rw [haTy]
    rfl
  have hCond1 :
      __eo_eq (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral 1) =
        Term.Boolean false := by
    change Term.Boolean
        (native_teq (Term.Numeral 1)
          (Term.Numeral (native_nat_to_int (W + 1)))) =
      Term.Boolean false
    have hne : ¬ (1 : Int) = (W : Int) + 1 := by omega
    simp [native_teq, native_nat_to_int, hne]
  have hCond2 :
      __eo_eq (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral 2) =
        Term.Boolean false := by
    change Term.Boolean
        (native_teq (Term.Numeral 2)
          (Term.Numeral (native_nat_to_int (W + 1)))) =
      Term.Boolean false
    have hne : ¬ (2 : Int) = (W : Int) + 1 := by omega
    simp [native_teq, native_nat_to_int, hne]
  have hNm2 :
      __eo_add (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral (-2 : native_Int)) =
      Term.Numeral (native_nat_to_int (W - 1)) := by
    change
      Term.Numeral (native_zplus (native_nat_to_int (W + 1)) (-2)) =
      Term.Numeral (native_nat_to_int (W - 1))
    congr
    have hEq :
        (W : Int) + 1 + (-2 : Int) = ((W - 1 : Nat) : Int) := by
      omega
    simpa [native_zplus, native_nat_to_int] using hEq
  have hTop :
      __eo_add (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral (-1 : native_Int)) =
      Term.Numeral (native_nat_to_int W) := by
    change
      Term.Numeral (native_zplus (native_nat_to_int (W + 1)) (-1)) =
      Term.Numeral (native_nat_to_int W)
    congr
    have hEq : (W : Int) + 1 + (-1 : Int) = (W : Int) := by
      omega
    simpa [native_zplus, native_nat_to_int] using hEq
  have hIndices := smulo_indices_eq W hWge2
  dsimp [bvSmuloExpanded]
  rw [hWidth, hNm2, hTop, hCond1, hCond2, hIndices, hNil]
  simp [__eo_ite, native_ite, native_teq,
    eo_mk_apply_arg_stuck, eo_mk_apply_fun_stuck,
    __bv_smulo_elim_rec, smulo_rec_list_stuck_eq, smulo_rec_res_stuck_eq]

private theorem nil_bvxor_b_ne_of_bvSmuloExpanded_ne
    (a b : Term) (W : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hNe : bvSmuloExpanded a b ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof b) ≠ Term.Stuck := by
  by_cases hW0 : W = 0
  · subst W
    rw [hbTy]
    native_decide
  by_cases hW1 : W = 1
  · subst W
    rw [hbTy]
    native_decide
  have hWge2 : 2 ≤ W := by omega
  intro hNil
  apply hNe
  have hWidth :
      __bv_bitwidth (__eo_typeof a) =
        Term.Numeral (native_nat_to_int (W + 1)) := by
    rw [haTy]
    rfl
  have hCond1 :
      __eo_eq (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral 1) =
        Term.Boolean false := by
    change Term.Boolean
        (native_teq (Term.Numeral 1)
          (Term.Numeral (native_nat_to_int (W + 1)))) =
      Term.Boolean false
    have hne : ¬ (1 : Int) = (W : Int) + 1 := by omega
    simp [native_teq, native_nat_to_int, hne]
  have hCond2 :
      __eo_eq (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral 2) =
        Term.Boolean false := by
    change Term.Boolean
        (native_teq (Term.Numeral 2)
          (Term.Numeral (native_nat_to_int (W + 1)))) =
      Term.Boolean false
    have hne : ¬ (2 : Int) = (W : Int) + 1 := by omega
    simp [native_teq, native_nat_to_int, hne]
  have hNm2 :
      __eo_add (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral (-2 : native_Int)) =
      Term.Numeral (native_nat_to_int (W - 1)) := by
    change
      Term.Numeral (native_zplus (native_nat_to_int (W + 1)) (-2)) =
      Term.Numeral (native_nat_to_int (W - 1))
    congr
    have hEq :
        (W : Int) + 1 + (-2 : Int) = ((W - 1 : Nat) : Int) := by
      omega
    simpa [native_zplus, native_nat_to_int] using hEq
  have hTop :
      __eo_add (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral (-1 : native_Int)) =
      Term.Numeral (native_nat_to_int W) := by
    change
      Term.Numeral (native_zplus (native_nat_to_int (W + 1)) (-1)) =
      Term.Numeral (native_nat_to_int W)
    congr
    have hEq : (W : Int) + 1 + (-1 : Int) = (W : Int) := by
      omega
    simpa [native_zplus, native_nat_to_int] using hEq
  have hIndices := smulo_indices_eq W hWge2
  dsimp [bvSmuloExpanded]
  rw [hWidth, hNm2, hTop, hCond1, hCond2, hIndices, hNil]
  simp [__eo_ite, native_ite, native_teq,
    eo_mk_apply_arg_stuck, eo_mk_apply_fun_stuck,
    __bv_smulo_elim_rec, smulo_rec_list_stuck_eq, smulo_rec_res_stuck_eq]

private theorem nil_bvmul_ne_of_bvSmuloExpanded_ne
    (a b : Term) (W : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (W + 1))))
    (hNe : bvSmuloExpanded a b ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvmul)
      (__eo_typeof (smuloSignExtendOneTerm a)) ≠ Term.Stuck := by
  by_cases hW0 : W = 0
  · subst W
    have hExtTy :
        __eo_typeof (smuloSignExtendOneTerm a) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int 2)) := by
      simpa [native_nat_to_int] using typeof_sign_extend_one_of_bv a 0 haTy
    rw [hExtTy]
    native_decide
  by_cases hW1 : W = 1
  · subst W
    have hExtTy :
        __eo_typeof (smuloSignExtendOneTerm a) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int 3)) := by
      simpa [native_nat_to_int] using typeof_sign_extend_one_of_bv a 1 haTy
    rw [hExtTy]
    native_decide
  have hWge2 : 2 ≤ W := by omega
  intro hNil
  apply hNe
  have hNil' :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof
          (Term.Apply
            (Term.UOp1 UserOp1.sign_extend (Term.Numeral 1)) a)) =
        Term.Stuck := by
    simpa [smuloSignExtendOneTerm] using hNil
  have hWidth :
      __bv_bitwidth (__eo_typeof a) =
        Term.Numeral (native_nat_to_int (W + 1)) := by
    rw [haTy]
    rfl
  have hCond1 :
      __eo_eq (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral 1) =
        Term.Boolean false := by
    change Term.Boolean
        (native_teq (Term.Numeral 1)
          (Term.Numeral (native_nat_to_int (W + 1)))) =
      Term.Boolean false
    have hne : ¬ (1 : Int) = (W : Int) + 1 := by omega
    simp [native_teq, native_nat_to_int, hne]
  have hCond2 :
      __eo_eq (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral 2) =
        Term.Boolean false := by
    change Term.Boolean
        (native_teq (Term.Numeral 2)
          (Term.Numeral (native_nat_to_int (W + 1)))) =
      Term.Boolean false
    have hne : ¬ (2 : Int) = (W : Int) + 1 := by omega
    simp [native_teq, native_nat_to_int, hne]
  have hNm2 :
      __eo_add (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral (-2 : native_Int)) =
      Term.Numeral (native_nat_to_int (W - 1)) := by
    change
      Term.Numeral (native_zplus (native_nat_to_int (W + 1)) (-2)) =
      Term.Numeral (native_nat_to_int (W - 1))
    congr
    have hEq :
        (W : Int) + 1 + (-2 : Int) = ((W - 1 : Nat) : Int) := by
      omega
    simpa [native_zplus, native_nat_to_int] using hEq
  have hTop :
      __eo_add (Term.Numeral (native_nat_to_int (W + 1)))
        (Term.Numeral (-1 : native_Int)) =
      Term.Numeral (native_nat_to_int W) := by
    change
      Term.Numeral (native_zplus (native_nat_to_int (W + 1)) (-1)) =
      Term.Numeral (native_nat_to_int W)
    congr
    have hEq : (W : Int) + 1 + (-1 : Int) = (W : Int) := by
      omega
    simpa [native_zplus, native_nat_to_int] using hEq
  have hIndices := smulo_indices_eq W hWge2
  dsimp [bvSmuloExpanded]
  rw [hWidth, hNm2, hTop, hCond1, hCond2, hIndices, hNil']
  simp [__eo_ite, native_ite, native_teq,
    eo_mk_apply_arg_stuck, eo_mk_apply_fun_stuck,
    __bv_smulo_elim_rec, smulo_rec_list_stuck_eq, smulo_rec_res_stuck_eq]

private theorem eval_bv_smulo_expanded
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hNN : term_has_non_none_type
      (SmtTerm.bvsmulo (__eo_to_smt a) (__eo_to_smt b)))
    (hExpandedNe : bvSmuloExpanded a b ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (bvSmuloExpanded a b)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) := by
  rcases bvsmulo_typeof_args_of_non_none hNN with
    ⟨w, haSmtTy, hbSmtTy⟩
  have haEoTy := eo_bitvec_type_of_smt_type a w haSmtTy
  have hbEoTy := eo_bitvec_type_of_smt_type b w hbSmtTy
  rcases bitvec_eval_nat_payload M hM a w haSmtTy with
    ⟨av, haEval, haBound⟩
  rcases bitvec_eval_nat_payload M hM b w hbSmtTy with
    ⟨bv, hbEval, hbBound⟩
  have hw : 1 ≤ w := bvSmuloExpanded_width_pos a b w haEoTy hExpandedNe
  cases w with
  | zero =>
      cases hw
  | succ W =>
      have hNilXorA :
          __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof a) ≠ Term.Stuck :=
        nil_bvxor_a_ne_of_bvSmuloExpanded_ne a b W
          (by simpa [Nat.succ_eq_add_one] using haEoTy)
          hExpandedNe
      have hNilXorB :
          __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof b) ≠ Term.Stuck :=
        nil_bvxor_b_ne_of_bvSmuloExpanded_ne a b W
          (by simpa [Nat.succ_eq_add_one] using haEoTy)
          (by simpa [Nat.succ_eq_add_one] using hbEoTy)
          hExpandedNe
      have hNilMul :
          __eo_nil (Term.UOp UserOp.bvmul)
            (__eo_typeof (smuloSignExtendOneTerm a)) ≠ Term.Stuck :=
        nil_bvmul_ne_of_bvSmuloExpanded_ne a b W
          (by simpa [Nat.succ_eq_add_one] using haEoTy)
          hExpandedNe
      simpa [Nat.succ_eq_add_one] using
        eval_bv_smulo_expanded_width_succ M a b W av bv
          (by simpa [Nat.succ_eq_add_one] using haEoTy)
          (by simpa [Nat.succ_eq_add_one] using hbEoTy)
          (by simpa [Nat.succ_eq_add_one] using haEval)
          (by simpa [Nat.succ_eq_add_one] using hbEval)
          (by simpa [Nat.succ_eq_add_one] using haBound)
          (by simpa [Nat.succ_eq_add_one] using hbBound)
          hNilXorA hNilXorB hNilMul

public theorem cmd_step_bv_smulo_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_smulo_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_smulo_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_smulo_elim args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.bv_smulo_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                  cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_bv_smulo_elim A)
              change __eo_typeof (__eo_prog_bv_smulo_elim A) = Term.Bool
                at hResultTy
              have hProgNe' : __eo_prog_bv_smulo_elim A ≠ Term.Stuck := by
                exact hProgNe
              rcases bv_smulo_elim_shape_of_ne_stuck A hProgNe' with
                ⟨a, b, rhs, hShape⟩
              subst A
              let lhs := Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b
              let expanded := bvSmuloExpanded a b
              let orig := Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
              have hReqNe :
                  __eo_requires expanded rhs orig ≠ Term.Stuck := by
                simpa [__eo_prog_bv_smulo_elim, expanded, orig, lhs,
                  bvSmuloExpanded] using hProgNe'
              have hExpandedEq : expanded = rhs :=
                support_eo_requires_cond_eq_of_non_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                eo_requires_left_ne_stuck_of_ne_stuck hReqNe
              have hRhsNe : rhs ≠ Term.Stuck := by
                rw [← hExpandedEq]
                exact hExpandedNe
              have hProgEq :
                  __eo_prog_bv_smulo_elim
                      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) =
                    orig := by
                rw [__eo_prog_bv_smulo_elim.eq_1]
                change __eo_requires expanded rhs orig = orig
                simp [__eo_requires, hExpandedEq, hRhsNe, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hOrigTy : __eo_typeof orig = Term.Bool := by
                simpa [hProgEq, orig, lhs] using hResultTy
              have hOrigBool : RuleProofs.eo_has_bool_type orig :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  orig hATrans hOrigTy
              rcases
                  RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    lhs rhs hOrigBool with
                ⟨_hSameTy, hLhsNN⟩
              have hBvsmuloNN :
                  term_has_non_none_type
                    (SmtTerm.bvsmulo (__eo_to_smt a) (__eo_to_smt b)) := by
                unfold term_has_non_none_type
                exact hLhsNN
              have hExpandedEval :
                  __smtx_model_eval M (__eo_to_smt expanded) =
                    __smtx_model_eval M (__eo_to_smt lhs) := by
                simpa [expanded, lhs] using
                  eval_bv_smulo_expanded M hM a b hBvsmuloNN hExpandedNe
              have hRelExpanded :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt expanded))
                    (__smtx_model_eval M (__eo_to_smt lhs)) := by
                rw [hExpandedEval]
                exact RuleProofs.smt_value_rel_refl _
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt lhs))
                    (__smtx_model_eval M (__eo_to_smt rhs)) := by
                rw [← hExpandedEq]
                exact RuleProofs.smt_value_rel_symm _ _ hRelExpanded
              have hFact :
                  eo_interprets M (__eo_prog_bv_smulo_elim orig) true := by
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel
                  M lhs rhs hOrigBool hRel
              exact
                { facts_of_true := by
                    intro _premisesTrue
                    simpa [orig] using hFact
                  has_smt_translation := by
                    rw [hProgEq]
                    exact
                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                        orig hOrigBool }
