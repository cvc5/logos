module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

/-!
Foundation lemmas for `bv_bitwise_slicing` soundness.

The rule rewrites a bitwise term `(f c a)` (f ∈ {bvand, bvor, bvxor}, `c` a constant
operand) into a concatenation of per-slice bitwise ops.  The key fact is that a bitwise
op distributes over any contiguous split of the bit range; everything below is the
machinery for that, lifted from `BitVec`/`Int` down to the `Nat` bit level.
-/

-- For a width-`w` bitvector, reducing its signed `toInt` mod `2^w` recovers `toNat`.
private theorem bv_toInt_emod (w : Nat) (x : BitVec w) :
    x.toInt % (2^w : Int) = (x.toNat : Int) := by
  have hc : ((2:Int)^w) = ((2^w : Nat):Int) := by norm_cast
  rw [hc, BitVec.toInt_eq_toNat_bmod, Int.bmod_emod]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast x.isLt)

-- `ofInt` of a canonical (in-range, nonneg) integer keeps the same `toNat`.
private theorem ofInt_toNat_canonical (w : Nat) (c : Int) (h0 : 0 ≤ c) (h1 : c < 2^w) :
    (BitVec.ofInt w c).toNat = c.toNat := by
  rw [BitVec.toNat_ofInt]; congr 1
  exact Int.emod_eq_of_lt h0 (by exact_mod_cast h1)

private theorem natpow2_eq (w : Nat) : native_int_pow2 (↑w : Int) = (2:Int)^w := by
  have hwnn : ¬ ((↑w:Int) < 0) := by omega
  unfold native_int_pow2 native_zexp_total
  rw [if_neg hwnn, Int.toNat_natCast]

private theorem int_canon_bounds {n : Int} {W : Nat}
    (h : native_zeq n (native_mod_total n (native_int_pow2 (↑W:Int))) = true) :
    0 ≤ n ∧ n < 2^W := by
  simp only [native_zeq, decide_eq_true_eq, native_mod_total, natpow2_eq] at h
  have hpos : (0:Int) < 2^W := by exact_mod_cast Nat.two_pow_pos W
  refine ⟨?_, ?_⟩
  · rw [h]; exact Int.emod_nonneg n (by omega)
  · rw [h]; exact Int.emod_lt_of_pos n hpos

-- A non-none term of type `BitVec W` evaluates to a canonical width-W binary value.
private theorem bv_term_eval_canonical (M : SmtModel) (hM : model_wf M) (t : SmtTerm)
    (W : Nat) (hnn : term_has_non_none_type t) (hty : __smtx_typeof t = SmtType.BitVec ↑W) :
    ∃ n : Int, __smtx_model_eval M t = SmtValue.Binary ↑W n ∧ 0 ≤ n ∧ n < 2^W := by
  have hpres := type_preservation M hM t hnn
  rw [hty] at hpres
  obtain ⟨n, hn⟩ := bitvec_value_canonical hpres
  rw [hn] at hpres
  obtain ⟨h0, h1⟩ := int_canon_bounds (bitvec_payload_canonical hpres)
  exact ⟨n, hn, h0, h1⟩

-- A bitwise Nat op commutes with division by `2^k` (selecting the high bits).
private theorem op_div2pow {f : Nat → Nat → Nat} {g : Bool → Bool → Bool}
    (hf : ∀ x y i, (f x y).testBit i = g (x.testBit i) (y.testBit i))
    (c a k : Nat) : (f c a) / 2^k = f (c / 2^k) (a / 2^k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, hf, hf, Nat.testBit_div_two_pow,
      Nat.testBit_div_two_pow]

-- A bitwise Nat op commutes with mod `2^k` (selecting the low bits).
private theorem op_mod2pow {f : Nat → Nat → Nat} {g : Bool → Bool → Bool}
    (hf : ∀ x y i, (f x y).testBit i = g (x.testBit i) (y.testBit i))
    (hff : g false false = false)
    (c a k : Nat) : (f c a) % 2^k = f (c % 2^k) (a % 2^k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, hf, hf, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow]
  cases hd : decide (i < k) <;> simp [hff]

-- The model-level bitwise-op payloads, expressed as plain `Nat` bit operations.
private theorem bvand_payload (w : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^w) (ha0 : 0 ≤ an) (ha1 : an < 2^w) :
    native_mod_total (native_binary_and (↑w) cn an) (native_int_pow2 (↑w))
      = ((cn.toNat &&& an.toNat : Nat) : Int) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    rw [show ((2:Int)^0) = 1 from rfl] at hc1 ha1
    have hcn : cn = 0 := by omega
    have han : an = 0 := by omega
    subst cn; subst an; decide
  · have hne : native_zeq (↑w:Int) 0 = false := by simp [native_zeq]; omega
    have hand : native_binary_and (↑w) cn an
        = (BitVec.ofInt w cn &&& BitVec.ofInt w an).toInt := by
      simp only [native_binary_and, native_piand]; rw [hne, Int.toNat_natCast]; rfl
    have e1 : native_mod_total (native_binary_and (↑w) cn an) (native_int_pow2 ↑w)
        = (BitVec.ofInt w cn &&& BitVec.ofInt w an).toInt % (2:Int)^w := by
      rw [hand]; simp only [native_mod_total]; rw [natpow2_eq]
    rw [e1, bv_toInt_emod, BitVec.toNat_and,
        ofInt_toNat_canonical w cn hc0 hc1, ofInt_toNat_canonical w an ha0 ha1]

private theorem bvor_payload (w : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^w) (ha0 : 0 ≤ an) (ha1 : an < 2^w) :
    native_mod_total (native_binary_or (↑w) cn an) (native_int_pow2 (↑w))
      = ((cn.toNat ||| an.toNat : Nat) : Int) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    rw [show ((2:Int)^0) = 1 from rfl] at hc1 ha1
    have hcn : cn = 0 := by omega
    have han : an = 0 := by omega
    subst cn; subst an; decide
  · have hne : native_zeq (↑w:Int) 0 = false := by simp [native_zeq]; omega
    have hand : native_binary_or (↑w) cn an
        = (BitVec.ofInt w cn ||| BitVec.ofInt w an).toInt := by
      simp only [native_binary_or, impl_native_pior]; rw [hne, Int.toNat_natCast]; rfl
    have e1 : native_mod_total (native_binary_or (↑w) cn an) (native_int_pow2 ↑w)
        = (BitVec.ofInt w cn ||| BitVec.ofInt w an).toInt % (2:Int)^w := by
      rw [hand]; simp only [native_mod_total]; rw [natpow2_eq]
    rw [e1, bv_toInt_emod, BitVec.toNat_or,
        ofInt_toNat_canonical w cn hc0 hc1, ofInt_toNat_canonical w an ha0 ha1]

private theorem bvxor_payload (w : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^w) (ha0 : 0 ≤ an) (ha1 : an < 2^w) :
    native_mod_total (native_binary_xor (↑w) cn an) (native_int_pow2 (↑w))
      = ((cn.toNat ^^^ an.toNat : Nat) : Int) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    rw [show ((2:Int)^0) = 1 from rfl] at hc1 ha1
    have hcn : cn = 0 := by omega
    have han : an = 0 := by omega
    subst cn; subst an; decide
  · have hne : native_zeq (↑w:Int) 0 = false := by simp [native_zeq]; omega
    have hand : native_binary_xor (↑w) cn an
        = (BitVec.ofInt w cn ^^^ BitVec.ofInt w an).toInt := by
      simp only [native_binary_xor, impl_native_pixor]; rw [hne, Int.toNat_natCast]; rfl
    have e1 : native_mod_total (native_binary_xor (↑w) cn an) (native_int_pow2 ↑w)
        = (BitVec.ofInt w cn ^^^ BitVec.ofInt w an).toInt % (2:Int)^w := by
      rw [hand]; simp only [native_mod_total]; rw [natpow2_eq]
    rw [e1, bv_toInt_emod, BitVec.toNat_xor,
        ofInt_toNat_canonical w cn hc0 hc1, ofInt_toNat_canonical w an ha0 ha1]

/- ===== Value-level eval lemmas ===== -/

private theorem eval_num (M : SmtModel) (n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) = SmtValue.Numeral n := by
  show __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
  simp only [__smtx_model_eval]

private theorem eval_bin (M : SmtModel) (w n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Binary w n)) = SmtValue.Binary w n := by
  show __smtx_model_eval M (SmtTerm.Binary w n) = SmtValue.Binary w n
  simp only [__smtx_model_eval]

-- A term whose `to_z` is `Numeral n` and which evaluates to a width-W binary has payload `n`.
private theorem to_z_numeral_eval (M : SmtModel) (y : Term) (W : Nat) (vy n : Int)
    (hz : __eo_to_z y = Term.Numeral n)
    (hev : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary ↑W vy) : vy = n := by
  cases y <;>
    first
    | (rename_i w' n'; rw [eval_bin] at hev; injection hev with _ h2;
       rw [show __eo_to_z (Term.Binary w' n') = Term.Numeral n' from rfl] at hz;
       injection hz with h3; rw [← h2, h3])
    | (rw [eval_num] at hev; simp only [reduceCtorEq] at hev)
    | (rename_i r; rw [show __eo_to_smt (Term.Rational r) = SmtTerm.Rational r from rfl] at hev;
       simp only [__smtx_model_eval, reduceCtorEq] at hev)
    | (rename_i s; rw [show __eo_to_smt (Term.String s) = SmtTerm.String s from rfl] at hev;
       simp only [__smtx_model_eval, reduceCtorEq] at hev)
    | (simp only [__eo_to_z, reduceCtorEq] at hz)

-- The bvor/bvxor nil evaluates to 0.
private theorem nilval_bvor (M : SmtModel) (y : Term) (W : Nat) (vy : Int)
    (hnil : __eo_is_list_nil (Term.UOp UserOp.bvor) y = Term.Boolean true)
    (hev : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary ↑W vy) : vy = 0 := by
  have hz : __eo_to_z y = Term.Numeral 0 := by
    cases y <;> simp_all [__eo_is_list_nil, __eo_is_list_nil_bvor, __eo_is_eq, __eo_to_z,
      native_and, native_not, native_teq, reduceCtorEq]
    -- v4.33 leaves the `String` case as a `decide`-wrapped equality whose
    -- `Decidable` instance no longer matches; decode it directly.
    exact (of_decide_eq_true hnil.2).symm
  exact to_z_numeral_eval M y W vy 0 hz hev

private theorem nilval_bvxor (M : SmtModel) (y : Term) (W : Nat) (vy : Int)
    (hnil : __eo_is_list_nil (Term.UOp UserOp.bvxor) y = Term.Boolean true)
    (hev : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary ↑W vy) : vy = 0 := by
  have hz : __eo_to_z y = Term.Numeral 0 := by
    cases y <;> simp_all [__eo_is_list_nil, __eo_is_list_nil_bvxor, __eo_is_eq, __eo_to_z,
      native_and, native_not, native_teq, reduceCtorEq]
    -- v4.33 leaves the `String` case as a `decide`-wrapped equality whose
    -- `Decidable` instance no longer matches; decode it directly.
    exact (of_decide_eq_true hnil.2).symm
  exact to_z_numeral_eval M y W vy 0 hz hev


-- The bvand nil evaluates to all-ones (2^W - 1), using operand canonicity.
private theorem nilval_bvand (M : SmtModel) (y : Term) (W : Nat) (vy : Int)
    (hnil : __eo_is_list_nil (Term.UOp UserOp.bvand) y = Term.Boolean true)
    (hev : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary ↑W vy)
    (h0 : 0 ≤ vy) (h1 : vy < (2:Int)^W) : vy = (2:Int)^W - 1 := by
  have hp : (0:Int) < (2:Int)^W := by exact_mod_cast Nat.two_pow_pos W
  cases y
  case Binary w' n' =>
    rw [eval_bin] at hev; injection hev with hw hn; subst w'; subst n'
    have ht := hnil
    simp only [show __eo_is_list_nil (Term.UOp UserOp.bvand) (Term.Binary ↑W vy)
        = __eo_is_list_nil_bvand (Term.Binary ↑W vy) from rfl,
      __eo_is_list_nil_bvand, __eo_is_eq, __eo_not, __eo_to_z,
      native_and, native_not, native_teq] at ht
    simp only [Term.Boolean.injEq, Term.Numeral.injEq, decide_eq_true_eq, reduceCtorEq,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_false_iff, true_and] at ht
    have hval : native_mod_total (native_binary_not (↑W) vy) (native_int_pow2 (↑W))
              = ((2:Int)^W - vy - 1) % (2:Int)^W := by
      show native_binary_not (↑W) vy % native_int_pow2 (↑W) = ((2:Int)^W - vy - 1) % (2:Int)^W
      rw [show native_binary_not (↑W) vy = native_int_pow2 (↑W) + -(vy+1) from rfl, natpow2_eq,
        show (2:Int)^W + -(vy+1) = (2:Int)^W - vy - 1 from by omega]
    rw [hval, Int.emod_eq_of_lt (a := (2:Int)^W - vy - 1) (b := (2:Int)^W) (by omega) (by omega)] at ht
    have ht' : (0:Int) = (2:Int)^W - vy - 1 := ht
    omega
  all_goals exfalso; revert hnil <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_bvand, __eo_is_eq, __eo_not, __eo_to_z,
      native_and, native_not, native_teq]

private theorem eval_extract (M : SmtModel) (X : Term) (hi lo w xn : Int)
    (hX : __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w xn) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral hi)
          (Term.Numeral lo)) X))
      = __smtx_model_eval_extract (SmtValue.Numeral hi) (SmtValue.Numeral lo)
          (SmtValue.Binary w xn) := by
  have ht : __eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral hi)
        (Term.Numeral lo)) X)
      = SmtTerm.extract (SmtTerm.Numeral hi) (SmtTerm.Numeral lo) (__eo_to_smt X) := rfl
  rw [ht]; simp only [__smtx_model_eval]; rw [hX]

private theorem eval_concat (M : SmtModel) (X Y : Term) (w1 n1 w2 n2 : Int)
    (hX : __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w1 n1)
    (hY : __smtx_model_eval M (__eo_to_smt Y) = SmtValue.Binary w2 n2) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) X) Y))
      = __smtx_model_eval_concat (SmtValue.Binary w1 n1) (SmtValue.Binary w2 n2) := by
  have ht : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) X) Y)
      = SmtTerm.concat (__eo_to_smt X) (__eo_to_smt Y) := rfl
  rw [ht]; simp only [__smtx_model_eval]; rw [hX, hY]

private theorem eval_bvand (M : SmtModel) (X Y : Term) (w1 n1 w2 n2 : Int)
    (hX : __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w1 n1)
    (hY : __smtx_model_eval M (__eo_to_smt Y) = SmtValue.Binary w2 n2) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) X) Y))
      = __smtx_model_eval_bvand (SmtValue.Binary w1 n1) (SmtValue.Binary w2 n2) := by
  have ht : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) X) Y)
      = SmtTerm.bvand (__eo_to_smt X) (__eo_to_smt Y) := rfl
  rw [ht]; simp only [__smtx_model_eval]; rw [hX, hY]

/- ===== Arithmetic computations on values ===== -/

private theorem nat_split_mod (D k m : Nat) (hkm : k ≤ m) :
    D % 2^m = ((D / 2^k) % 2^(m-k)) * 2^k + D % 2^k := by
  have hpow : (2:Nat)^m = 2^k * 2^(m-k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hpow, Nat.mod_mul, Nat.add_comm, Nat.mul_comm]

-- extract value, payload/width as casts of Nat ops.
private theorem extract_valN (W : Nat) (Xn : Int) (hi lo : Nat)
    (hX0 : 0 ≤ Xn) (hlo : lo ≤ hi + 1) :
    __smtx_model_eval_extract (SmtValue.Numeral ↑hi) (SmtValue.Numeral ↑lo)
        (SmtValue.Binary ↑W Xn)
      = SmtValue.Binary ↑(hi + 1 - lo) ↑((Xn.toNat / 2^lo) % 2^(hi + 1 - lo)) := by
  obtain ⟨N, rfl⟩ : ∃ N : Nat, Xn = (↑N : Int) := ⟨Xn.toNat, (Int.toNat_of_nonneg hX0).symm⟩
  simp only [__smtx_model_eval_extract, native_zplus, native_zneg,
    native_mod_total, native_binary_extract, native_div_total, Int.toNat_natCast]
  have hw : (↑hi + 1 + -↑lo : Int) = ↑(hi + 1 - lo) := by omega
  rw [hw, natpow2_eq lo, natpow2_eq (hi + 1 - lo),
      show ((2:Int)^lo) = ((2^lo:Nat):Int) from by norm_cast,
      show ((2:Int)^(hi+1-lo)) = ((2^(hi+1-lo):Nat):Int) from by norm_cast]
  norm_cast

private theorem bvand_valN (W : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W) (ha0 : 0 ≤ an) (ha1 : an < 2^W) :
    __smtx_model_eval_bvand (SmtValue.Binary ↑W cn) (SmtValue.Binary ↑W an)
      = SmtValue.Binary ↑W ↑(cn.toNat &&& an.toNat) := by
  simp only [__smtx_model_eval_bvand]
  rw [bvand_payload W cn an hc0 hc1 ha0 ha1]


private theorem eval_bvor (M : SmtModel) (X Y : Term) (w1 n1 w2 n2 : Int)
    (hX : __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w1 n1)
    (hY : __smtx_model_eval M (__eo_to_smt Y) = SmtValue.Binary w2 n2) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) X) Y))
      = __smtx_model_eval_bvor (SmtValue.Binary w1 n1) (SmtValue.Binary w2 n2) := by
  have ht : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) X) Y)
      = SmtTerm.bvor (__eo_to_smt X) (__eo_to_smt Y) := rfl
  rw [ht]; simp only [__smtx_model_eval]; rw [hX, hY]

private theorem eval_bvxor (M : SmtModel) (X Y : Term) (w1 n1 w2 n2 : Int)
    (hX : __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w1 n1)
    (hY : __smtx_model_eval M (__eo_to_smt Y) = SmtValue.Binary w2 n2) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) X) Y))
      = __smtx_model_eval_bvxor (SmtValue.Binary w1 n1) (SmtValue.Binary w2 n2) := by
  have ht : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) X) Y)
      = SmtTerm.bvxor (__eo_to_smt X) (__eo_to_smt Y) := rfl
  rw [ht]; simp only [__smtx_model_eval]; rw [hX, hY]

private theorem bvor_valN (W : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W) (ha0 : 0 ≤ an) (ha1 : an < 2^W) :
    __smtx_model_eval_bvor (SmtValue.Binary ↑W cn) (SmtValue.Binary ↑W an)
      = SmtValue.Binary ↑W ↑(cn.toNat ||| an.toNat) := by
  simp only [__smtx_model_eval_bvor]
  rw [bvor_payload W cn an hc0 hc1 ha0 ha1]

private theorem bvxor_valN (W : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W) (ha0 : 0 ≤ an) (ha1 : an < 2^W) :
    __smtx_model_eval_bvxor (SmtValue.Binary ↑W cn) (SmtValue.Binary ↑W an)
      = SmtValue.Binary ↑W ↑(cn.toNat ^^^ an.toNat) := by
  simp only [__smtx_model_eval_bvxor]
  rw [bvxor_payload W cn an hc0 hc1 ha0 ha1]
private theorem concat_valN (w1 p1 w2 p2 : Nat) :
    __smtx_model_eval_concat (SmtValue.Binary ↑w1 ↑p1) (SmtValue.Binary ↑w2 ↑p2)
      = SmtValue.Binary ↑(w1 + w2) ↑((p1 * 2^w2 + p2) % 2^(w1 + w2)) := by
  simp only [__smtx_model_eval_concat, native_zplus, native_mod_total,
    native_binary_concat, native_zmult]
  have hw : (↑w1 + ↑w2 : Int) = ↑(w1 + w2) := by norm_cast
  rw [hw, natpow2_eq w2, natpow2_eq (w1 + w2),
      show ((2:Int)^w2) = ((2^w2:Nat):Int) from by norm_cast,
      show ((2:Int)^(w1+w2)) = ((2^(w1+w2):Nat):Int) from by norm_cast]
  norm_cast

private theorem natCast_mod_lt (x m : Nat) : ((x % 2^m : Nat) : Int) < (2:Int)^m := by
  have h : x % 2^m < 2^m := Nat.mod_lt _ (Nat.two_pow_pos m)
  exact_mod_cast h

private theorem toNat_lt_pow_of_canonical {n : Int} {W : Nat}
    (h0 : 0 ≤ n) (h1 : n < (2:Int)^W) : n.toNat < 2^W := by
  have hpow : ((2^W : Nat) : Int) = (2:Int)^W := by norm_cast
  have hcast : ((n.toNat : Nat) : Int) < ((2^W : Nat) : Int) := by
    rw [hpow, Int.toNat_of_nonneg h0]
    exact h1
  exact_mod_cast hcast

-- AND with the all-ones mask of width m is the identity on m-bit values.
private theorem bvand_nil (m : Nat) (pa : Int) (h0 : 0 ≤ pa) (h1 : pa < 2^m) :
    __smtx_model_eval_bvand (SmtValue.Binary ↑m pa) (SmtValue.Binary ↑m ↑(2^m - 1))
      = SmtValue.Binary ↑m pa := by
  have hpos : (1:Int) ≤ (2:Int)^m := by
    have : (1:Nat) ≤ 2^m := Nat.one_le_two_pow
    exact_mod_cast this
  have h2 : (2:Int)^m = ((2^m : Nat) : Int) := by norm_cast
  rw [bvand_valN m pa _ h0 h1 (by omega) (by omega)]
  congr 1
  have htoNat : ((2:Int)^m - 1).toNat = 2^m - 1 := by rw [h2]; omega
  rw [htoNat]
  have hpaN : pa.toNat < 2^m := by omega
  have hx : pa.toNat &&& (2^m - 1) = pa.toNat := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < m
    · simp [hi]
    · have hge : 2^m ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (by omega : pa.toNat < 2^i)]
      simp
  rw [hx, Int.toNat_of_nonneg h0]


private theorem requires_tt (X : Term) :
    __eo_requires (Term.Boolean true) (Term.Boolean true) X = X := by
  unfold __eo_requires
  simp only [native_teq, native_ite, native_not, decide_true, reduceIte, reduceCtorEq,
    Bool.not_false, decide_false]

-- Shared: the slice `typeof` reduces to a `BitVec` of the slice width.
private theorem typeof_extract_slice (W : Nat) (cn : Int) (hi lo : Nat)
    (hhiW : hi < W) (hlo : lo ≤ hi) :
    __eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
      (Term.Numeral ↑lo)) (Term.Binary ↑W cn))
      = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (↑hi - ↑lo + 1)) := by
  have hg1 : __eo_gt (Term.Numeral ↑lo) (Term.Numeral (-1)) = Term.Boolean true := by
    show Term.Boolean (native_zlt (-1) (↑lo)) = Term.Boolean true
    rw [show native_zlt (-1) (↑lo) = true from by
      unfold native_zlt; exact decide_eq_true (show ((-1):Int) < ↑lo by omega)]
  have hg2 : __eo_gt (Term.Numeral ↑W) (Term.Numeral ↑hi) = Term.Boolean true := by
    show Term.Boolean (native_zlt (↑hi) (↑W)) = Term.Boolean true
    congr 1; show native_zlt (↑hi) (↑W) = true
    unfold native_zlt; exact decide_eq_true (by exact_mod_cast hhiW)
  have hg3 :
      __eo_gt
          (__eo_add (__eo_add (Term.Numeral ↑hi) (__eo_neg (Term.Numeral ↑lo)))
            (Term.Numeral 1))
          (Term.Numeral 0) =
        Term.Boolean true := by
    show Term.Boolean
        (native_zlt 0 (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1)) =
      Term.Boolean true
    rw [show native_zlt 0
          (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1) = true from by
      unfold native_zlt
      exact decide_eq_true (show (0 : Int) < ↑hi - ↑lo + 1 by omega)]
  rw [show __eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn))
        = __eo_typeof_extract (__eo_typeof (Term.Numeral ↑hi)) (Term.Numeral ↑hi)
            (__eo_typeof (Term.Numeral ↑lo)) (Term.Numeral ↑lo)
            (__eo_typeof (Term.Binary ↑W cn)) from rfl,
      show __eo_typeof (Term.Numeral ↑hi) = Term.UOp UserOp.Int from rfl,
      show __eo_typeof (Term.Numeral ↑lo) = Term.UOp UserOp.Int from rfl,
      show __eo_typeof (Term.Binary ↑W cn)
        = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral ↑W) from rfl]
  show __eo_mk_apply (Term.UOp UserOp.BitVec)
      (__eo_requires (__eo_gt (Term.Numeral ↑lo) (Term.Numeral (-1)))
        (Term.Boolean true)
        (__eo_requires (__eo_gt (Term.Numeral ↑W) (Term.Numeral ↑hi)) (Term.Boolean true)
          (__eo_requires
            (__eo_gt
              (__eo_add (__eo_add (Term.Numeral ↑hi) (__eo_neg (Term.Numeral ↑lo)))
                (Term.Numeral 1))
              (Term.Numeral 0)) (Term.Boolean true)
            (__eo_add (__eo_add (Term.Numeral ↑hi) (__eo_neg (Term.Numeral ↑lo)))
              (Term.Numeral 1))))) = _
  rw [hg1, hg2, hg3, requires_tt, requires_tt, requires_tt]
  show (Term.UOp UserOp.BitVec).Apply
      (Term.Numeral (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1)) = _
  congr 2

private theorem extract_slice_lower_le_of_nil_ne (f : Term) (W : Nat) (cn : Int)
    (hi lo : Nat) (hhiW : hi < W)
    (hNil : __eo_nil f
        (__eo_typeof (Term.Apply
          (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo))
          (Term.Binary ↑W cn))) ≠ Term.Stuck) :
    lo ≤ hi := by
  apply Nat.le_of_not_gt
  intro hlo
  apply hNil
  have hg1 : __eo_gt (Term.Numeral ↑lo) (Term.Numeral (-1)) =
      Term.Boolean true := by
    show Term.Boolean (native_zlt (-1) (↑lo)) = Term.Boolean true
    rw [show native_zlt (-1) (↑lo) = true from by
      unfold native_zlt
      exact decide_eq_true (show ((-1) : Int) < ↑lo by omega)]
  have hg2 : __eo_gt (Term.Numeral ↑W) (Term.Numeral ↑hi) =
      Term.Boolean true := by
    show Term.Boolean (native_zlt (↑hi) (↑W)) = Term.Boolean true
    congr 1
    unfold native_zlt
    exact decide_eq_true (by exact_mod_cast hhiW)
  have hg3 :
      __eo_gt
          (__eo_add (__eo_add (Term.Numeral ↑hi) (__eo_neg (Term.Numeral ↑lo)))
            (Term.Numeral 1))
          (Term.Numeral 0) =
        Term.Boolean false := by
    show Term.Boolean
        (native_zlt 0 (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1)) =
      Term.Boolean false
    have hwidth :
        native_zplus (native_zplus (↑hi : Int) (native_zneg (↑lo : Int))) 1 ≤
          0 := by
      change (↑hi : Int) + -(↑lo : Int) + 1 ≤ 0
      omega
    rw [show native_zlt 0
        (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1) = false from by
      unfold native_zlt
      exact decide_eq_false (Int.not_lt_of_ge hwidth)]
  rw [show __eo_typeof (Term.Apply
          (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo))
          (Term.Binary ↑W cn)) =
        __eo_typeof_extract (__eo_typeof (Term.Numeral ↑hi)) (Term.Numeral ↑hi)
          (__eo_typeof (Term.Numeral ↑lo)) (Term.Numeral ↑lo)
          (__eo_typeof (Term.Binary ↑W cn)) from rfl,
      show __eo_typeof (Term.Numeral ↑hi) = Term.UOp UserOp.Int from rfl,
      show __eo_typeof (Term.Numeral ↑lo) = Term.UOp UserOp.Int from rfl,
      show __eo_typeof (Term.Binary ↑W cn) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral ↑W) from rfl]
  simp [__eo_typeof_extract, hg1, hg2, hg3, __eo_requires, __eo_mk_apply,
    native_ite, native_teq, native_not, SmtEval.native_not]
  rfl

-- Shared: `to_bin M 0` reduces to the zero literal of width M.
private theorem to_bin_zero (M : Int) (h0 : 0 ≤ M) (h32 : M ≤ 4294967296) :
    __eo_to_bin (Term.Numeral M) (Term.Numeral 0) = Term.Binary M 0 := by
  show native_ite (native_zleq M 4294967296) (__eo_mk_binary M 0) Term.Stuck = _
  rw [show native_zleq M 4294967296 = true from by unfold native_zleq; exact decide_eq_true h32]
  show __eo_mk_binary M 0 = _
  show native_ite (native_zleq 0 M)
      (Term.Binary M (native_mod_total 0 (native_int_pow2 M))) Term.Stuck = _
  rw [show native_zleq 0 M = true from by unfold native_zleq; exact decide_eq_true h0]
  show Term.Binary M (native_mod_total 0 (native_int_pow2 M)) = Term.Binary M 0
  congr 1

-- The nil operand for the `bvand` slice [hi:lo] of the constant `c` (width W) reduces
-- to the all-ones literal of the slice width (needs the slice width ≤ 2^32 so `to_bin`
-- does not get stuck).
private theorem nil_term_bvand (W : Nat) (cn : Int) (hi lo : Nat)
    (hhiW : hi < W) (hlo : lo ≤ hi)
    (hMle : ((hi + 1 - lo : Nat) : Int) ≤ 4294967296) :
    __eo_nil (Term.UOp UserOp.bvand)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))
      = Term.Binary ↑(hi + 1 - lo) ((2:Int)^(hi + 1 - lo) - 1) := by
  have hMeq : (↑hi - ↑lo + 1 : Int) = ↑(hi + 1 - lo) := by omega
  have hg1 : __eo_gt (Term.Numeral ↑lo) (Term.Numeral (-1)) = Term.Boolean true := by
    show Term.Boolean (native_zlt (-1) (↑lo)) = Term.Boolean true
    rw [show native_zlt (-1) (↑lo) = true from by
      unfold native_zlt; exact decide_eq_true (show ((-1):Int) < ↑lo by omega)]
  have hg2 : __eo_gt (Term.Numeral ↑W) (Term.Numeral ↑hi) = Term.Boolean true := by
    show Term.Boolean (native_zlt (↑hi) (↑W)) = Term.Boolean true
    congr 1; show native_zlt (↑hi) (↑W) = true
    unfold native_zlt; exact decide_eq_true (by exact_mod_cast hhiW)
  have hg3 :
      __eo_gt
          (__eo_add (__eo_add (Term.Numeral ↑hi) (__eo_neg (Term.Numeral ↑lo)))
            (Term.Numeral 1))
          (Term.Numeral 0) =
        Term.Boolean true := by
    show Term.Boolean
        (native_zlt 0 (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1)) =
      Term.Boolean true
    rw [show native_zlt 0
          (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1) = true from by
      unfold native_zlt
      exact decide_eq_true (show (0 : Int) < ↑hi - ↑lo + 1 by omega)]
  have htype : __eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
        (Term.Numeral ↑lo)) (Term.Binary ↑W cn))
      = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (↑hi - ↑lo + 1)) := by
    rw [show __eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
            (Term.Numeral ↑lo)) (Term.Binary ↑W cn))
          = __eo_typeof_extract (__eo_typeof (Term.Numeral ↑hi)) (Term.Numeral ↑hi)
              (__eo_typeof (Term.Numeral ↑lo)) (Term.Numeral ↑lo)
              (__eo_typeof (Term.Binary ↑W cn)) from rfl,
        show __eo_typeof (Term.Numeral ↑hi) = Term.UOp UserOp.Int from rfl,
        show __eo_typeof (Term.Numeral ↑lo) = Term.UOp UserOp.Int from rfl,
        show __eo_typeof (Term.Binary ↑W cn)
          = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral ↑W) from rfl]
    show __eo_mk_apply (Term.UOp UserOp.BitVec)
        (__eo_requires (__eo_gt (Term.Numeral ↑lo) (Term.Numeral (-1)))
          (Term.Boolean true)
          (__eo_requires (__eo_gt (Term.Numeral ↑W) (Term.Numeral ↑hi)) (Term.Boolean true)
            (__eo_requires
              (__eo_gt
                (__eo_add (__eo_add (Term.Numeral ↑hi) (__eo_neg (Term.Numeral ↑lo)))
                  (Term.Numeral 1))
                (Term.Numeral 0)) (Term.Boolean true)
              (__eo_add (__eo_add (Term.Numeral ↑hi) (__eo_neg (Term.Numeral ↑lo)))
                (Term.Numeral 1))))) = _
    rw [hg1, hg2, hg3, requires_tt, requires_tt, requires_tt]
    show (Term.UOp UserOp.BitVec).Apply
        (Term.Numeral (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1)) = _
    congr 2
  rw [htype]
  show __eo_not (__eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0)) = _
  have htobin : __eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0)
      = Term.Binary (↑hi - ↑lo + 1) 0 := by
    show native_ite (native_zleq (↑hi - ↑lo + 1) 4294967296)
        (__eo_mk_binary (↑hi - ↑lo + 1) 0) Term.Stuck = _
    rw [show native_zleq (↑hi - ↑lo + 1) 4294967296 = true from by
      unfold native_zleq; exact decide_eq_true (by rw [hMeq]; exact hMle)]
    show __eo_mk_binary (↑hi - ↑lo + 1) 0 = _
    show native_ite (native_zleq 0 (↑hi - ↑lo + 1))
        (Term.Binary (↑hi - ↑lo + 1) (native_mod_total 0 (native_int_pow2 (↑hi - ↑lo + 1)))) Term.Stuck = _
    rw [show native_zleq 0 (↑hi - ↑lo + 1) = true from by
      unfold native_zleq; exact decide_eq_true (by rw [hMeq]; exact_mod_cast Nat.zero_le _)]
    show Term.Binary (↑hi - ↑lo + 1) (native_mod_total 0 (native_int_pow2 (↑hi - ↑lo + 1)))
        = Term.Binary (↑hi - ↑lo + 1) 0
    congr 1
  rw [htobin]
  show Term.Binary (↑hi - ↑lo + 1)
      (native_mod_total (native_binary_not (↑hi - ↑lo + 1) 0)
        (native_int_pow2 (↑hi - ↑lo + 1))) = _
  rw [hMeq]
  congr 1
  simp only [native_binary_not, native_mod_total, native_zplus, native_zneg]
  rw [natpow2_eq (hi + 1 - lo)]
  have hge : (1:Int) ≤ (2:Int)^(hi+1-lo) := by
    have : (1:Nat) ≤ 2^(hi+1-lo) := Nat.one_le_two_pow
    exact_mod_cast this
  rw [show ((2:Int)^(hi+1-lo) + -(0+1)) = (2:Int)^(hi+1-lo) - 1 from by omega]
  exact Int.emod_eq_of_lt (by omega) (by omega)

private theorem nil_term_bvor (W : Nat) (cn : Int) (hi lo : Nat)
    (hhiW : hi < W) (hlo : lo ≤ hi)
    (hMle : ((hi + 1 - lo : Nat) : Int) ≤ 4294967296) :
    __eo_nil (Term.UOp UserOp.bvor)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))
      = Term.Binary ↑(hi + 1 - lo) 0 := by
  have hMeq : (↑hi - ↑lo + 1 : Int) = ↑(hi + 1 - lo) := by omega
  rw [typeof_extract_slice W cn hi lo hhiW hlo]
  show __eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0) = _
  rw [to_bin_zero _ (by omega) (by rw [hMeq]; exact hMle), hMeq]

private theorem nil_term_bvxor (W : Nat) (cn : Int) (hi lo : Nat)
    (hhiW : hi < W) (hlo : lo ≤ hi)
    (hMle : ((hi + 1 - lo : Nat) : Int) ≤ 4294967296) :
    __eo_nil (Term.UOp UserOp.bvxor)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))
      = Term.Binary ↑(hi + 1 - lo) 0 := by
  have hMeq : (↑hi - ↑lo + 1 : Int) = ↑(hi + 1 - lo) := by omega
  rw [typeof_extract_slice W cn hi lo hhiW hlo]
  show __eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0) = _
  rw [to_bin_zero _ (by omega) (by rw [hMeq]; exact hMle), hMeq]

private theorem eo_not_arg_ne_stuck_of_ne {x : Term}
    (h : __eo_not x ≠ Term.Stuck) : x ≠ Term.Stuck := by
  intro hx
  subst x
  exact h rfl

private theorem to_bin_zero_bound_of_ne (m : Int)
    (h : __eo_to_bin (Term.Numeral m) (Term.Numeral 0) ≠ Term.Stuck) :
    m ≤ 4294967296 := by
  by_cases hm : m ≤ 4294967296
  · exact hm
  · exfalso
    apply h
    show native_ite (native_zleq m 4294967296) (__eo_mk_binary m 0) Term.Stuck = Term.Stuck
    rw [show native_zleq m 4294967296 = false from by
      unfold native_zleq
      exact decide_eq_false hm]
    rfl

private theorem nil_bound_bvand (W : Nat) (cn : Int) (hi lo : Nat)
    (hhiW : hi < W) (_hlo : lo ≤ hi)
    (h : __eo_nil (Term.UOp UserOp.bvand)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn))) ≠ Term.Stuck) :
    ((hi + 1 - lo : Nat) : Int) ≤ 4294967296 := by
  have hMeq : (↑hi - ↑lo + 1 : Int) = ↑(hi + 1 - lo) := by omega
  have hNil :
      __eo_not (__eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0))
        ≠ Term.Stuck := by
    simpa [__eo_nil, __eo_nil_bvand, typeof_extract_slice W cn hi lo hhiW _hlo] using h
  have hToBin :=
    eo_not_arg_ne_stuck_of_ne hNil
  have hBound := to_bin_zero_bound_of_ne (↑hi - ↑lo + 1) hToBin
  rwa [hMeq] at hBound

private theorem nil_bound_bvor (W : Nat) (cn : Int) (hi lo : Nat)
    (hhiW : hi < W) (_hlo : lo ≤ hi)
    (h : __eo_nil (Term.UOp UserOp.bvor)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn))) ≠ Term.Stuck) :
    ((hi + 1 - lo : Nat) : Int) ≤ 4294967296 := by
  have hMeq : (↑hi - ↑lo + 1 : Int) = ↑(hi + 1 - lo) := by omega
  have hToBin :
      __eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0) ≠ Term.Stuck := by
    simpa [__eo_nil, __eo_nil_bvor, typeof_extract_slice W cn hi lo hhiW _hlo] using h
  have hBound := to_bin_zero_bound_of_ne (↑hi - ↑lo + 1) hToBin
  rwa [hMeq] at hBound

private theorem nil_bound_bvxor (W : Nat) (cn : Int) (hi lo : Nat)
    (hhiW : hi < W) (_hlo : lo ≤ hi)
    (h : __eo_nil (Term.UOp UserOp.bvxor)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn))) ≠ Term.Stuck) :
    ((hi + 1 - lo : Nat) : Int) ≤ 4294967296 := by
  have hMeq : (↑hi - ↑lo + 1 : Int) = ↑(hi + 1 - lo) := by omega
  have hToBin :
      __eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0) ≠ Term.Stuck := by
    simpa [__eo_nil, __eo_nil_bvxor, typeof_extract_slice W cn hi lo hhiW _hlo] using h
  have hBound := to_bin_zero_bound_of_ne (↑hi - ↑lo + 1) hToBin
  rwa [hMeq] at hBound

private theorem bvor_nil (m : Nat) (pa : Int) (h0 : 0 ≤ pa) (h1 : pa < 2^m) :
    __smtx_model_eval_bvor (SmtValue.Binary ↑m pa) (SmtValue.Binary ↑m 0)
      = SmtValue.Binary ↑m pa := by
  have h2 : (0:Int) < (2:Int)^m := by
    have : (0:Nat) < 2^m := Nat.two_pow_pos m
    exact_mod_cast this
  rw [bvor_valN m pa 0 h0 h1 (by omega) h2]
  congr 1
  rw [show (0:Int).toNat = 0 from rfl, Nat.or_zero, Int.toNat_of_nonneg h0]

private theorem bvxor_nil (m : Nat) (pa : Int) (h0 : 0 ≤ pa) (h1 : pa < 2^m) :
    __smtx_model_eval_bvxor (SmtValue.Binary ↑m pa) (SmtValue.Binary ↑m 0)
      = SmtValue.Binary ↑m pa := by
  have h2 : (0:Int) < (2:Int)^m := by
    have : (0:Nat) < 2^m := Nat.two_pow_pos m
    exact_mod_cast this
  rw [bvxor_valN m pa 0 h0 h1 (by omega) h2]
  congr 1
  rw [show (0:Int).toNat = 0 from rfl, Nat.xor_zero, Int.toNat_of_nonneg h0]

/-- Algebraic interface shared by the three bitwise operators (`bvand`/`bvor`/`bvxor`),
so the slicing recursion is proved once and instantiated three times. -/
structure BvOpSpec where
  f : Term
  opval : SmtValue → SmtValue → SmtValue
  opnat : Nat → Nat → Nat
  gop : Bool → Bool → Bool
  nilpay : Nat → Int
  hfne : f ≠ Term.Stuck
  hcomm : ∀ x y, opnat x y = opnat y x
  hassoc : ∀ x y z, opnat (opnat x y) z = opnat x (opnat y z)
  htb : ∀ x y i, (opnat x y).testBit i = gop (x.testBit i) (y.testBit i)
  hgff : gop false false = false
  heval : ∀ (M : SmtModel) (X Y : Term) (w1 n1 w2 n2 : Int),
    __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w1 n1 →
    __smtx_model_eval M (__eo_to_smt Y) = SmtValue.Binary w2 n2 →
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply f X) Y))
      = opval (SmtValue.Binary w1 n1) (SmtValue.Binary w2 n2)
  htypeof : ∀ (X Y : Term),
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f X) Y))
      = __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt X)) (__smtx_typeof (__eo_to_smt Y))
  hvalN : ∀ (W : Nat) (cn an : Int), 0 ≤ cn → cn < 2^W → 0 ≤ an → an < 2^W →
    opval (SmtValue.Binary ↑W cn) (SmtValue.Binary ↑W an)
      = SmtValue.Binary ↑W ↑(opnat cn.toNat an.toNat)
  hnilterm : ∀ (W : Nat) (cn : Int) (hi lo : Nat), hi < W → lo ≤ hi →
    ((hi + 1 - lo : Nat) : Int) ≤ 4294967296 →
    __eo_nil f (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
      (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))
      = Term.Binary ↑(hi + 1 - lo) (nilpay (hi + 1 - lo))
  hnilbound : ∀ (W : Nat) (cn : Int) (hi lo : Nat), hi < W → lo ≤ hi →
    __eo_nil f (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
      (Term.Numeral ↑lo)) (Term.Binary ↑W cn))) ≠ Term.Stuck →
    ((hi + 1 - lo : Nat) : Int) ≤ 4294967296
  hnilid : ∀ (m : Nat) (pa : Int), 0 ≤ pa → pa < 2^m →
    opval (SmtValue.Binary ↑m pa) (SmtValue.Binary ↑m (nilpay m)) = SmtValue.Binary ↑m pa
  hnilval : ∀ (M : SmtModel) (y : Term) (W : Nat) (vy : Int),
    __eo_is_list_nil f y = Term.Boolean true →
    __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary ↑W vy →
    0 ≤ vy → vy < 2^W → vy = nilpay W
  hnilbool : ∀ (y : Term), y ≠ Term.Stuck → ∃ b, __eo_is_list_nil f y = Term.Boolean b

private def bvOpAnd : BvOpSpec where
  f := Term.UOp UserOp.bvand
  opval := __smtx_model_eval_bvand
  opnat := fun x y => x &&& y
  gop := fun a b => a && b
  hfne := by intro h; cases h
  nilpay := fun m => (2:Int)^m - 1
  hcomm := Nat.and_comm
  hassoc := Nat.and_assoc
  htb := Nat.testBit_and
  hgff := by decide
  heval := eval_bvand
  htypeof := fun X Y => by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) X) Y)
          = SmtTerm.bvand (__eo_to_smt X) (__eo_to_smt Y) from rfl, __smtx_typeof.eq_40]
  hvalN := bvand_valN
  hnilterm := nil_term_bvand
  hnilbound := nil_bound_bvand
  hnilid := bvand_nil
  hnilval := nilval_bvand
  hnilbool := fun y hy => by cases y <;> first | exact ⟨_, rfl⟩ | exact absurd rfl hy

private def bvOpOr : BvOpSpec where
  f := Term.UOp UserOp.bvor
  opval := __smtx_model_eval_bvor
  opnat := fun x y => x ||| y
  gop := fun a b => a || b
  hfne := by intro h; cases h
  nilpay := fun _ => 0
  hcomm := Nat.or_comm
  hassoc := Nat.or_assoc
  htb := Nat.testBit_or
  hgff := by decide
  heval := eval_bvor
  htypeof := fun X Y => by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) X) Y)
          = SmtTerm.bvor (__eo_to_smt X) (__eo_to_smt Y) from rfl, __smtx_typeof.eq_41]
  hvalN := bvor_valN
  hnilterm := nil_term_bvor
  hnilbound := nil_bound_bvor
  hnilid := bvor_nil
  hnilval := fun M y W vy hnil hev _ _ => nilval_bvor M y W vy hnil hev
  hnilbool := fun y hy => by cases y <;> first | exact ⟨_, rfl⟩ | exact absurd rfl hy

private def bvOpXor : BvOpSpec where
  f := Term.UOp UserOp.bvxor
  opval := __smtx_model_eval_bvxor
  opnat := fun x y => x ^^^ y
  gop := fun a b => xor a b
  hfne := by intro h; cases h
  nilpay := fun _ => 0
  hcomm := Nat.xor_comm
  hassoc := Nat.xor_assoc
  htb := Nat.testBit_xor
  hgff := by decide
  heval := eval_bvxor
  htypeof := fun X Y => by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) X) Y)
          = SmtTerm.bvxor (__eo_to_smt X) (__eo_to_smt Y) from rfl, __smtx_typeof.eq_44]
  hvalN := bvxor_valN
  hnilterm := nil_term_bvxor
  hnilbound := nil_bound_bvxor
  hnilid := bvxor_nil
  hnilval := fun M y W vy hnil hev _ _ => nilval_bvxor M y W vy hnil hev
  hnilbool := fun y hy => by cases y <;> first | exact ⟨_, rfl⟩ | exact absurd rfl hy

private theorem slice_op (op : BvOpSpec) (W : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an) (hi lo : Nat) (hlo : lo ≤ hi + 1) :
    op.opval
        (__smtx_model_eval_extract (SmtValue.Numeral ↑hi) (SmtValue.Numeral ↑lo)
          (SmtValue.Binary ↑W cn))
        (__smtx_model_eval_extract (SmtValue.Numeral ↑hi) (SmtValue.Numeral ↑lo)
          (SmtValue.Binary ↑W an))
      = SmtValue.Binary ↑(hi + 1 - lo)
          ↑(((op.opnat cn.toNat an.toNat) / 2^lo) % 2^(hi + 1 - lo)) := by
  rw [extract_valN W cn hi lo hc0 hlo, extract_valN W an hi lo ha0 hlo,
      op.hvalN (hi + 1 - lo) _ _ (Int.natCast_nonneg _) (natCast_mod_lt _ _)
        (Int.natCast_nonneg _) (natCast_mod_lt _ _)]
  congr 2
  rw [Int.toNat_natCast, Int.toNat_natCast,
      ← op_mod2pow op.htb op.hgff, ← op_div2pow op.htb]

private theorem concat_split_op (op : BvOpSpec) (W : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an) (s k : Nat) (hk1 : 1 ≤ k) (hks : k ≤ s + 1) :
    op.opval
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s) (SmtValue.Numeral (0:Int))
          (SmtValue.Binary ↑W cn))
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s) (SmtValue.Numeral (0:Int))
          (SmtValue.Binary ↑W an))
      = __smtx_model_eval_concat
          (op.opval
            (__smtx_model_eval_extract (SmtValue.Numeral ↑s) (SmtValue.Numeral ↑k)
              (SmtValue.Binary ↑W cn))
            (__smtx_model_eval_extract (SmtValue.Numeral ↑s) (SmtValue.Numeral ↑k)
              (SmtValue.Binary ↑W an)))
          (op.opval
            (__smtx_model_eval_extract (SmtValue.Numeral ↑(k-1)) (SmtValue.Numeral (0:Int))
              (SmtValue.Binary ↑W cn))
            (__smtx_model_eval_extract (SmtValue.Numeral ↑(k-1)) (SmtValue.Numeral (0:Int))
              (SmtValue.Binary ↑W an))) := by
  have e0 : ((0:Int)) = ((0:Nat):Int) := by norm_cast
  rw [e0, slice_op op W cn an hc0 ha0 s 0 (by omega),
      slice_op op W cn an hc0 ha0 s k (by omega),
      slice_op op W cn an hc0 ha0 (k-1) 0 (by omega)]
  simp only [Nat.sub_zero, Nat.pow_zero, Nat.div_one]
  rw [Nat.sub_add_cancel hk1, concat_valN (s + 1 - k) _ k _, Nat.sub_add_cancel hks]
  congr 1
  norm_cast
  rw [← nat_split_mod (op.opnat cn.toNat an.toNat) k (s + 1) hks, Nat.mod_mod]

/-! Public value-level interface used by the concat-pullup family.  Keeping the
    interface at `SmtValue` avoids exposing the internal `BvOpSpec` machinery. -/

public theorem bvand_concat_slice_split_value
    (W : Nat) (cn an : Int) (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (s k : Nat) (hk1 : 1 ≤ k) (hks : k ≤ s + 1) :
    __smtx_model_eval_bvand
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W an)) =
      __smtx_model_eval_concat
        (__smtx_model_eval_bvand
          (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (__smtx_model_eval_bvand
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) :=
  concat_split_op bvOpAnd W cn an hc0 ha0 s k hk1 hks

public theorem bvor_concat_slice_split_value
    (W : Nat) (cn an : Int) (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (s k : Nat) (hk1 : 1 ≤ k) (hks : k ≤ s + 1) :
    __smtx_model_eval_bvor
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W an)) =
      __smtx_model_eval_concat
        (__smtx_model_eval_bvor
          (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (__smtx_model_eval_bvor
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) :=
  concat_split_op bvOpOr W cn an hc0 ha0 s k hk1 hks

public theorem bvxor_concat_slice_split_value
    (W : Nat) (cn an : Int) (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (s k : Nat) (hk1 : 1 ≤ k) (hks : k ≤ s + 1) :
    __smtx_model_eval_bvxor
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W an)) =
      __smtx_model_eval_concat
        (__smtx_model_eval_bvxor
          (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (__smtx_model_eval_bvxor
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) :=
  concat_split_op bvOpXor W cn an hc0 ha0 s k hk1 hks

private theorem concat_full_split_op (op : BvOpSpec)
    (W k : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W)
    (ha0 : 0 ≤ an) (ha1 : an < 2^W)
    (hk1 : 1 ≤ k) (hkW : k ≤ W) :
    op.opval (SmtValue.Binary ↑W cn) (SmtValue.Binary ↑W an) =
      __smtx_model_eval_concat
        (op.opval
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (op.opval
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) := by
  have hW1 : 1 ≤ W := Nat.le_trans hk1 hkW
  have hWpos : 0 < W := by omega
  have hWholeC :
      __smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn) =
        SmtValue.Binary ↑W cn := by
    rw [show (0 : Int) = ((0 : Nat) : Int) by rfl,
      extract_valN W cn (W - 1) 0 hc0 (by omega)]
    have hWidth : W - 1 + 1 - 0 = W := by omega
    simp only [Nat.pow_zero, Nat.div_one, hWidth]
    congr 2
    norm_cast
    have hcn : cn.toNat < 2^W := toNat_lt_pow_of_canonical hc0 hc1
    rw [Nat.mod_eq_of_lt hcn, Int.toNat_of_nonneg hc0]
  have hWholeA :
      __smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W an) =
        SmtValue.Binary ↑W an := by
    rw [show (0 : Int) = ((0 : Nat) : Int) by rfl,
      extract_valN W an (W - 1) 0 ha0 (by omega)]
    have hWidth : W - 1 + 1 - 0 = W := by omega
    simp only [Nat.pow_zero, Nat.div_one, hWidth]
    congr 2
    norm_cast
    have han : an.toNat < 2^W := toNat_lt_pow_of_canonical ha0 ha1
    rw [Nat.mod_eq_of_lt han, Int.toNat_of_nonneg ha0]
  have hSplit := concat_split_op op W cn an hc0 ha0 (W - 1) k hk1 (by omega)
  rwa [hWholeC, hWholeA] at hSplit

public theorem bvand_concat_full_split_value
    (W k : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W)
    (ha0 : 0 ≤ an) (ha1 : an < 2^W)
    (hk1 : 1 ≤ k) (hkW : k ≤ W) :
    __smtx_model_eval_bvand (SmtValue.Binary ↑W cn)
        (SmtValue.Binary ↑W an) =
      __smtx_model_eval_concat
        (__smtx_model_eval_bvand
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (__smtx_model_eval_bvand
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) :=
  concat_full_split_op bvOpAnd W k cn an hc0 hc1 ha0 ha1 hk1 hkW

public theorem bvor_concat_full_split_value
    (W k : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W)
    (ha0 : 0 ≤ an) (ha1 : an < 2^W)
    (hk1 : 1 ≤ k) (hkW : k ≤ W) :
    __smtx_model_eval_bvor (SmtValue.Binary ↑W cn)
        (SmtValue.Binary ↑W an) =
      __smtx_model_eval_concat
        (__smtx_model_eval_bvor
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (__smtx_model_eval_bvor
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) :=
  concat_full_split_op bvOpOr W k cn an hc0 hc1 ha0 ha1 hk1 hkW

public theorem bvxor_concat_full_split_value
    (W k : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W)
    (ha0 : 0 ≤ an) (ha1 : an < 2^W)
    (hk1 : 1 ≤ k) (hkW : k ≤ W) :
    __smtx_model_eval_bvxor (SmtValue.Binary ↑W cn)
        (SmtValue.Binary ↑W an) =
      __smtx_model_eval_concat
        (__smtx_model_eval_bvxor
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (__smtx_model_eval_bvxor
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) :=
  concat_full_split_op bvOpXor W k cn an hc0 hc1 ha0 ha1 hk1 hkW

-- Closed-form split used by the induction's emit case.
private theorem closed_split (D s e : Nat) (hes : e ≤ s) :
    SmtValue.Binary ↑(s + 1) ↑(D % 2^(s + 1))
      = __smtx_model_eval_concat
          (SmtValue.Binary ↑(s - e) ↑((D / 2^(e + 1)) % 2^(s - e)))
          (SmtValue.Binary ↑(e + 1) ↑(D % 2^(e + 1))) := by
  rw [concat_valN (s - e) ((D / 2^(e + 1)) % 2^(s - e)) (e + 1) (D % 2^(e + 1))]
  congr 1
  · rw [show s + 1 = (s - e) + (e + 1) from by omega]
  · congr 1
    have hns := nat_split_mod D (e + 1) (s + 1) (by omega)
    rw [show (s + 1) - (e + 1) = s - e from by omega] at hns
    rw [show (s - e) + (e + 1) = s + 1 from by omega, ← hns, Nat.mod_mod]

private theorem concat_rempty (m p : Nat) (h : p < 2^m) :
    __smtx_model_eval_concat (SmtValue.Binary ↑m ↑p) (SmtValue.Binary 0 0)
      = SmtValue.Binary ↑m ↑p := by
  have h0 : native_int_pow2 (0:Int) = 1 := by rfl
  simp only [__smtx_model_eval_concat, native_zplus, native_mod_total,
    native_binary_concat, native_zmult]
  rw [show (↑m + (0:Int)) = ↑m from by omega, natpow2_eq m, h0]
  congr 1
  rw [show (↑p * (1:Int) + 0) = ↑p from by omega]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast h)

private theorem eo_mk_apply_ne {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_mk_apply_left_ne_stuck_of_ne {f x : Term}
    (h : __eo_mk_apply f x ≠ Term.Stuck) : f ≠ Term.Stuck := by
  intro hf
  subst f
  exact h rfl

private theorem eo_mk_apply_right_ne_stuck_of_ne {f x : Term}
    (h : __eo_mk_apply f x ≠ Term.Stuck) : x ≠ Term.Stuck := by
  intro hx
  subst x
  apply h
  cases f <;> rfl

-- bs is a `@from_bools` list of length L (ending in `Binary 0 0`).
inductive FB : Term → Nat → Prop
  | nil : FB (Term.Binary 0 0) 0
  | cons (b bs' : Term) (L : Nat) (hb : b ≠ Term.Stuck) : FB bs' L →
      FB (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) b) bs') (L + 1)

private theorem FB_ne_stuck {t : Term} {n : Nat} (h : FB t n) : t ≠ Term.Stuck := by
  cases h <;> intro hs <;> cases hs

private theorem FB_zero_eq {t : Term} (h : FB t 0) : t = Term.Binary 0 0 := by
  cases h
  rfl

-- An `Int`-typed list (the index list fed to the bit-list constructor).
inductive IL : Term → Nat → Prop
  | nil : IL (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)) 0
  | cons (i : Int) (xs : Term) (n : Nat) : IL xs n →
      IL (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral i)) xs)
        (n + 1)

private theorem IL_ne_stuck {t : Term} {n : Nat} (h : IL t n) : t ≠ Term.Stuck := by
  cases h <;> intro hs <;> cases hs

private theorem extract_bin_ne_stuck (W cn i : Int) :
    __eo_extract (Term.Binary W cn) (Term.Numeral i) (Term.Numeral i) ≠ Term.Stuck := by
  have hz : native_zleq 0 (native_zplus (native_zplus i (native_zneg i)) 1) = true := by
    have h : (0:Int) ≤ native_zplus (native_zplus i (native_zneg i)) 1 := by
      simp only [native_zplus, native_zneg]; omega
    unfold native_zleq; exact decide_eq_true h
  unfold __eo_extract
  cases hc : native_or (native_zlt i 0) (native_zlt (native_zplus i (native_zneg i)) 0)
  · simp only [native_ite, hc, Bool.false_eq_true, if_false, __eo_mk_binary, hz, if_true]
    intro h; cases h
  · simp only [native_ite, hc, if_true]; intro h; cases h

-- The bit list built from a constant `Binary W cn` over an index list `xs` is an `FB` list.
private theorem const_to_bitlist_FB (W cn : Int) :
    ∀ (xs : Term) (n : Nat), IL xs n →
      FB (__bv_const_to_bitlist_rec (Term.Binary W cn) xs) n := by
  intro xs n hIL
  induction hIL with
  | nil => exact FB.nil
  | cons i xs n hIL ih =>
      have hbit : __eo_eq (__eo_extract (Term.Binary W cn) (Term.Numeral i) (Term.Numeral i))
          (Term.Binary 1 1) ≠ Term.Stuck := by
        have hx := extract_bin_ne_stuck W cn i
        cases he : __eo_extract (Term.Binary W cn) (Term.Numeral i) (Term.Numeral i) <;>
          simp_all [__eo_eq]
      have hrecne := FB_ne_stuck ih
      show FB (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
          (__eo_eq (__eo_extract (Term.Binary W cn) (Term.Numeral i) (Term.Numeral i))
            (Term.Binary 1 1)))
          (__bv_const_to_bitlist_rec (Term.Binary W cn) xs)) (n + 1)
      rw [eo_mk_apply_ne (by intro h; cases h) hbit,
          eo_mk_apply_ne (by intro h; cases h) hrecne]
      exact FB.cons _ _ _ hbit ih

private theorem list_rev_rec_nil (acc : Term) (h : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (Term.Binary 0 0) acc = acc := by
  cases acc <;> simp_all [__eo_list_rev_rec]

private theorem list_rev_rec_cons (f x y acc : Term) (h : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc
      = __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) := by
  cases acc <;> simp_all [__eo_list_rev_rec]

private theorem list_rev_rec_FB {bs : Term} {n : Nat} (hbs : FB bs n) :
    ∀ {acc : Term} {m : Nat}, FB acc m → FB (__eo_list_rev_rec bs acc) (n + m) := by
  induction hbs with
  | nil =>
      intro acc m hacc
      rw [list_rev_rec_nil acc (FB_ne_stuck hacc)]; simpa using hacc
  | cons b bs' L hb hbs' ih =>
      intro acc m hacc
      rw [list_rev_rec_cons _ _ _ _ (FB_ne_stuck hacc)]
      have := ih (FB.cons b acc m hb hacc)
      have heq : L + (m + 1) = L + 1 + m := by omega
      rwa [heq] at this

private theorem lrr_ne_stuck (k : Nat) :
    __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0) k
      ≠ Term.Stuck := by
  induction k with
  | zero =>
      show __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (Term.UOp UserOp.Int) ≠ Term.Stuck
      intro h; cases h
  | succ k ih =>
      rw [show __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0)
            (k + 1)
          = __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0))
            (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0) k)
          from rfl, eo_mk_apply_ne (by intro h; cases h) ih]
      intro h; cases h

-- The index list `iota_rec (list_repeat cons 0 k) n` is an `IL` of length `k`.
private theorem iota_repeat_IL : ∀ (k : Nat) (n : Int),
    IL (__iota_rec (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
        (Term.Numeral 0) k) (Term.Numeral n)) k := by
  intro k
  induction k with
  | zero =>
      intro n
      show IL (__iota_rec (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.UOp UserOp.Int)) (Term.Numeral n)) 0
      exact IL.nil
  | succ k ih =>
      intro n
      rw [show __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0)
            (k + 1)
          = __eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0))
            (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0) k)
          from rfl,
          eo_mk_apply_ne (by intro h; cases h) (lrr_ne_stuck k)]
      show IL (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral n))
          (__iota_rec (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) k) (__eo_add (Term.Numeral n) (Term.Numeral 1)))) (k + 1)
      rw [show __eo_add (Term.Numeral n) (Term.Numeral 1) = Term.Numeral (n + 1) from rfl,
          eo_mk_apply_ne (by intro h; cases h) (IL_ne_stuck (ih (n + 1)))]
      exact IL.cons n _ k (ih (n + 1))

private theorem requires_refl (t X : Term) (h : t ≠ Term.Stuck) :
    __eo_requires t t X = X := by
  simp [__eo_requires, native_teq, native_ite, native_not, h]

private theorem FB_get_nil {bs : Term} {n : Nat} (h : FB bs n) :
    __eo_get_nil_rec (Term.UOp UserOp._at_from_bools) bs = Term.Binary 0 0 := by
  induction h with
  | nil =>
      show __eo_requires (Term.Boolean true) (Term.Boolean true) (Term.Binary 0 0) = Term.Binary 0 0
      exact requires_refl _ _ (by intro hh; cases hh)
  | cons b bs' L hb hbs' ih =>
      show __eo_requires (Term.UOp UserOp._at_from_bools) (Term.UOp UserOp._at_from_bools)
          (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) bs') = Term.Binary 0 0
      rw [requires_refl _ _ (by intro hh; cases hh)]; exact ih

private theorem FB_is_list {bs : Term} {n : Nat} (h : FB bs n) :
    __eo_is_list (Term.UOp UserOp._at_from_bools) bs = Term.Boolean true := by
  have hnil := FB_get_nil h
  have hne := FB_ne_stuck h
  cases bs <;>
    simp_all [__eo_is_list, __eo_is_ok, native_not, native_teq, reduceCtorEq]

-- The full bit list produced by `__bv_mk_bitwise_slicing` for a width-`W` constant is an
-- `FB` list of length `W`.
private theorem bitlist_FB (W : Nat) (cn : Int) :
    FB (__eo_list_rev (Term.UOp UserOp._at_from_bools)
        (__bv_const_to_bitlist_rec (Term.Binary ↑W cn)
          (__eo_requires (__eo_is_neg (Term.Numeral ↑W)) (Term.Boolean false)
            (__iota_rec (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) (Term.Numeral ↑W)) (Term.Numeral 0))))) W := by
  have hrep : __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0)
      (Term.Numeral ↑W)
      = __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0) W := by
    show native_ite (native_zlt (↑W) 0) Term.Stuck
        (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0)
          (native_int_to_nat ↑W)) = _
    rw [show native_zlt (↑W) 0 = false from by
          unfold native_zlt; exact decide_eq_false (show ¬((↑W:Int) < 0) by omega),
        show native_int_to_nat (↑W : Int) = W from by simp [native_int_to_nat]]
    rfl
  rw [hrep]
  have hneg : __eo_is_neg (Term.Numeral ↑W) = Term.Boolean false := by
    show Term.Boolean (native_zlt (↑W) 0) = Term.Boolean false
    rw [show native_zlt (↑W) 0 = false from by
      unfold native_zlt; exact decide_eq_false (show ¬((↑W:Int) < 0) by omega)]
  rw [hneg, requires_refl _ _ (by intro h; cases h)]
  have hcbl := const_to_bitlist_FB ↑W cn _ W (iota_repeat_IL W 0)
  show FB (__eo_requires (__eo_is_list (Term.UOp UserOp._at_from_bools) _) (Term.Boolean true)
      (__eo_list_rev_rec _ (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) _))) W
  rw [FB_is_list hcbl, FB_get_nil hcbl, requires_refl _ _ (by intro h; cases h)]
  simpa using list_rev_rec_FB hcbl FB.nil

private theorem ne_stuck_of_eval_bin (M : SmtModel) (t : Term) (w n : Int)
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary w n) : t ≠ Term.Stuck := by
  intro hs; subst hs
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl,
      show __smtx_model_eval M SmtTerm.None = SmtValue.NotValue from by
        simp only [__smtx_model_eval]] at h
  cases h

private theorem eo_ite_true (X Y : Term) : __eo_ite (Term.Boolean true) X Y = X := by
  simp [__eo_ite, native_teq, native_ite]
private theorem eo_ite_false (X Y : Term) : __eo_ite (Term.Boolean false) X Y = Y := by
  simp [__eo_ite, native_teq, native_ite]
private theorem eo_eq_ne {b bn : Term} (hb : b ≠ Term.Stuck) (hbn : bn ≠ Term.Stuck) :
    __eo_eq b bn = Term.Boolean (native_teq bn b) := by
  cases b <;> cases bn <;> simp [__eo_eq] at hb hbn ⊢

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_requires_left_ne_stuck_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x ≠ Term.Stuck := by
  intro hReq hx
  have hStuck : __eo_requires x y z = Term.Stuck := by
    subst x
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]
  exact hReq hStuck

private theorem eo_requires_payload_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck → z ≠ Term.Stuck := by
  intro hReq hz; apply hReq; subst z
  simp [__eo_requires, native_ite, native_teq, native_not]

private theorem gnr_cons (f g x y : Term) (hf : f ≠ Term.Stuck) :
    __eo_get_nil_rec f (Term.Apply (Term.Apply g x) y)
      = __eo_requires f g (__eo_get_nil_rec f y) := by
  generalize hz : __eo_get_nil_rec f y = z
  unfold __eo_get_nil_rec; split <;> simp_all

private theorem gnr_stuck (f : Term) : __eo_get_nil_rec f Term.Stuck = Term.Stuck := by
  unfold __eo_get_nil_rec; split <;> simp_all

private theorem islist_isok (f x : Term) (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_is_list f x = __eo_is_ok (__eo_get_nil_rec f x) := by
  unfold __eo_is_list; split <;> simp_all

-- In a homogeneous op-list, the head operator is `op.f` and the tail is again a list.
private theorem is_list_cons_inv_gen (f g x y : Term) (hfne : f ≠ Term.Stuck)
    (h : __eo_is_list f (Term.Apply (Term.Apply g x) y) = Term.Boolean true) :
    g = f ∧ __eo_is_list f y = Term.Boolean true := by
  rw [islist_isok f _ hfne (by intro hh; cases hh), gnr_cons f g x y hfne] at h
  have hZ : __eo_requires f g (__eo_get_nil_rec f y) ≠ Term.Stuck := by
    intro hs; rw [hs] at h; simp [__eo_is_ok, native_not, native_teq] at h
  have hgy : __eo_get_nil_rec f y ≠ Term.Stuck := eo_requires_payload_ne_stuck hZ
  have hyne : y ≠ Term.Stuck := by rintro rfl; exact hgy (gnr_stuck f)
  refine ⟨(eo_requires_arg_eq_of_ne_stuck hZ).symm, ?_⟩
  rw [islist_isok f y hfne hyne, __eo_is_ok]
  simp [native_not, native_teq, hgy]

private theorem is_list_cons_inv (op : BvOpSpec) (g x y : Term)
    (h : __eo_is_list op.f (Term.Apply (Term.Apply g x) y) = Term.Boolean true) :
    g = op.f ∧ __eo_is_list op.f y = Term.Boolean true :=
  is_list_cons_inv_gen op.f g x y op.hfne h

private def BvEvalCanonical (M : SmtModel) (t : Term) : Prop :=
  ∃ (w : Nat) (n : Int),
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary ↑w n ∧
      0 ≤ n ∧ n < (2:Int)^w

private def BvConcatListCanonical (M : SmtModel) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) xs =>
      BvEvalCanonical M x ∧ BvConcatListCanonical M xs
  | t => BvEvalCanonical M t

private theorem concat_is_list_nil_bool (y : Term) (hy : y ≠ Term.Stuck) :
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.concat) y = Term.Boolean b := by
  cases y with
  | Stuck => exact (hy rfl).elim
  | Binary w n =>
    by_cases hw : w = 0
    · by_cases hn : n = 0
      · subst w; subst n; exact ⟨true, rfl⟩
      · exact ⟨false, by simp [__eo_is_list_nil, hn]⟩
    · exact ⟨false, by simp [__eo_is_list_nil, hw]⟩
  | _ => exact ⟨false, rfl⟩

private theorem concat_nil_eval_binary_zero_of_is_list_nil_true (M : SmtModel) (y : Term)
    (h : __eo_is_list_nil (Term.UOp UserOp.concat) y = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary 0 0 := by
  cases y with
  | Binary w n =>
      have hEq : w = 0 ∧ n = 0 := by
        by_cases hw : w = 0
        · by_cases hn : n = 0
          · exact ⟨hw, hn⟩
          · simp [__eo_is_list_nil, hn] at h
        · simp [__eo_is_list_nil, hw] at h
      rcases hEq with ⟨rfl, rfl⟩
      exact eval_bin M 0 0
  | _ =>
      simp_all [__eo_is_list_nil, reduceCtorEq]

private theorem bvconcat_right_empty_rel_of_canonical (M : SmtModel) (x nil : Term)
    (hx : BvEvalCanonical M x)
    (hnil : __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases hx with ⟨w, n, hxEval, hn0, hn1⟩
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [eval_concat M x nil ↑w n 0 0 hxEval hnil]
  have hnCast : ((n.toNat : Nat) : Int) = n :=
    Int.toNat_of_nonneg hn0
  have hpow : ((2^w : Nat) : Int) = (2:Int)^w := by norm_cast
  have hNatLt : n.toNat < 2^w := by
    have hNatLtInt : ((n.toNat : Nat) : Int) < ((2^w : Nat) : Int) := by
      rw [hpow, hnCast]
      exact hn1
    exact_mod_cast hNatLtInt
  rw [← hnCast]
  rw [concat_rempty w n.toNat hNatLt]
  rw [hnCast, hxEval]
  simp [__smtx_model_eval_eq, native_veq]

private theorem bvconcat_singleton_elim_rel_eval (M : SmtModel) (c : Term) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    BvConcatListCanonical M c ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hCan
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          obtain ⟨hg, hTailList⟩ :=
            is_list_cons_inv_gen (Term.UOp UserOp.concat) g head tail
              (by intro h; cases h) hList
          subst g
          have hHeadCan : BvEvalCanonical M head := hCan.1
          have hTailCan : BvConcatListCanonical M tail := hCan.2
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases concat_is_list_nil_bool tail hTailNe with ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite, native_teq]
          cases b
          · exact RuleProofs.smt_value_rel_refl
              (__smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) head) tail)))
          · exact RuleProofs.smt_value_rel_symm _ _
              (bvconcat_right_empty_rel_of_canonical M head tail hHeadCan
                (concat_nil_eval_binary_zero_of_is_list_nil_true M tail hNil))
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

-- Shape of a non-stuck `bv_bitwise_slicing` program: it must be an equality.
private theorem bv_bitwise_slicing_shape_of_ne_stuck (A : Term) :
    __eo_prog_bv_bitwise_slicing A ≠ Term.Stuck ->
    ∃ lhs rhs, A = Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs := by
  intro h
  by_cases hShape :
      ∃ lhs rhs, A = Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
  · exact hShape
  · have hStuck : __eo_prog_bv_bitwise_slicing A = Term.Stuck := by
      rw [__eo_prog_bv_bitwise_slicing.eq_2]
      intro lhs rhs hEq
      exact hShape ⟨lhs, rhs, hEq⟩
    exact False.elim (h hStuck)

-- Shape of a non-stuck `__bv_mk_bitwise_slicing`: its argument is a binary application.
private theorem slice_eval_op (op : BvOpSpec) (M : SmtModel) (W : Nat) (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (hi lo : Nat) (hhiW : hi < W) (hlo : lo ≤ hi)
    (hMle : ((hi + 1 - lo : Nat) : Int) ≤ 4294967296) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (op.f)
          (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo))
            (Term.Binary ↑W cn)))
          (Term.Apply (Term.Apply (op.f)
            (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo)) a))
            (__eo_nil (op.f)
              (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
                (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))))))
      = SmtValue.Binary ↑(hi + 1 - lo)
          ↑(((op.opnat cn.toNat an.toNat) / 2^lo) % 2^(hi + 1 - lo)) := by
  have hCext : __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo))
        (Term.Binary ↑W cn)))
      = SmtValue.Binary ↑(hi + 1 - lo) ↑((cn.toNat / 2^lo) % 2^(hi + 1 - lo)) := by
    rw [eval_extract M (Term.Binary ↑W cn) ↑hi ↑lo ↑W cn (eval_bin M ↑W cn),
        extract_valN W cn hi lo hc0 (by omega)]
  have hAext : __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo)) a))
      = SmtValue.Binary ↑(hi + 1 - lo) ↑((an.toNat / 2^lo) % 2^(hi + 1 - lo)) := by
    rw [eval_extract M a ↑hi ↑lo ↑W an ha, extract_valN W an hi lo ha0 (by omega)]
  have hNil : __smtx_model_eval M (__eo_to_smt (__eo_nil (op.f)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))))
      = SmtValue.Binary ↑(hi + 1 - lo) (op.nilpay (hi + 1 - lo)) := by
    rw [op.hnilterm W cn hi lo hhiW hlo hMle]; exact eval_bin M _ _
  have hInner : __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (op.f)
        (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo)) a))
        (__eo_nil (op.f)
          (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
            (Term.Numeral ↑lo)) (Term.Binary ↑W cn))))))
      = SmtValue.Binary ↑(hi + 1 - lo) ↑((an.toNat / 2^lo) % 2^(hi + 1 - lo)) := by
    rw [op.heval M _ _ _ _ _ _ hAext hNil]
    exact op.hnilid (hi + 1 - lo) _ (Int.natCast_nonneg _) (natCast_mod_lt _ _)
  rw [op.heval M _ _ _ _ _ _ hCext hInner,
      op.hvalN (hi + 1 - lo) _ _ (Int.natCast_nonneg _) (natCast_mod_lt _ _)
        (Int.natCast_nonneg _) (natCast_mod_lt _ _)]
  congr 2
  rw [Int.toNat_natCast, Int.toNat_natCast,
      ← op_mod2pow op.htb op.hgff, ← op_div2pow op.htb]

-- Closed-form split used by the induction's emit case.

private theorem base_eval_op (op : BvOpSpec) (M : SmtModel) (W : Nat) (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (s : Nat) (hsW : s < W)
    (hMle : ((s + 1 - 0 : Nat) : Int) ≤ 4294967296) :
    __smtx_model_eval M (__eo_to_smt
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat)
        (__eo_mk_apply ((op.f).Apply
            ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply (Term.Binary ↑W cn)))
          (__eo_mk_apply ((op.f).Apply
              ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply a))
            (__eo_nil (op.f)
              (__eo_typeof ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply
                (Term.Binary ↑W cn)))))))
        (Term.Binary 0 0)))
      = SmtValue.Binary ↑(s + 1) ↑((op.opnat cn.toNat an.toNat) % 2^(s + 1)) := by
  rw [show Term.Numeral (0:Int) = Term.Numeral ((0:Nat):Int) from by simp]
  have hNILne : __eo_nil (op.f)
      (__eo_typeof ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ((0:Nat):Int))).Apply
        (Term.Binary ↑W cn))) ≠ Term.Stuck := by
    rw [op.hnilterm W cn s 0 hsW (by omega) hMle]; intro h; cases h
  rw [eo_mk_apply_ne (by intro h; cases h) hNILne,
      eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h),
      eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h),
      eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)]
  rw [eval_concat M _ (Term.Binary 0 0) _ _ _ _
        (slice_eval_op op M W cn a an hc0 ha0 ha s 0 hsW (by omega) hMle) (eval_bin M 0 0),
      concat_rempty (s + 1 - 0) (((op.opnat cn.toNat an.toNat) / 2^0) % 2^(s + 1 - 0))
        (Nat.mod_lt _ (Nat.two_pow_pos _))]
  simp only [Nat.sub_zero, Nat.pow_zero, Nat.div_one]

private theorem emit_eval_op (op : BvOpSpec) (M : SmtModel) (W : Nat) (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (hane : a ≠ Term.Stuck)
    (s L' : Nat) (hL's : L' < s) (hsW : s < W)
    (hMle : ((s + 1 - (L' + 1) : Nat) : Int) ≤ 4294967296)
    (rest : Term)
    (hrest : __smtx_model_eval M (__eo_to_smt rest)
      = SmtValue.Binary ↑(L' + 1) ↑((op.opnat cn.toNat an.toNat) % 2^(L' + 1)))
    (hrestne : rest ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat)
        (__eo_mk_apply (__eo_mk_apply (op.f)
            (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
              (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) (Term.Binary ↑W cn)))
          (__eo_mk_apply (__eo_mk_apply (op.f)
              (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) a))
            (__eo_nil (op.f)
              (__eo_typeof (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) (Term.Binary ↑W cn)))))))
        rest))
      = SmtValue.Binary ↑(s + 1) ↑((op.opnat cn.toNat an.toNat) % 2^(s + 1)) := by
  have hbr : (↑L' : Int) + 1 = ↑(L' + 1) := by omega
  rw [show __eo_add (Term.Numeral ↑L') (Term.Numeral 1) = Term.Numeral ↑(L' + 1) from by
        show Term.Numeral ((↑L' : Int) + 1) = Term.Numeral ↑(L' + 1)
        rw [hbr]]
  have eA : __eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)
      = Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  have eB : __eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a = Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a :=
    eo_mk_apply_ne (by intro h; cases h) hane
  simp only [eA, eB]
  have hNILne : __eo_nil (op.f)
      (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))) ≠ Term.Stuck := by
    rw [op.hnilterm W cn s (L' + 1) hsW (by omega) hMle]; intro h; cases h
  have eC : __eo_mk_apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))
      = Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)) :=
    eo_mk_apply_ne op.hfne (by intro h; cases h)
  have eD : __eo_mk_apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a)
      = Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a) :=
    eo_mk_apply_ne op.hfne (by intro h; cases h)
  simp only [eC, eD]
  have eE : __eo_mk_apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
        (__eo_nil (op.f) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))))
      = Term.Apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
        (__eo_nil (op.f) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))) :=
    eo_mk_apply_ne (by intro h; cases h) hNILne
  simp only [eE]
  have eF : __eo_mk_apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))
        (Term.Apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
          (__eo_nil (op.f) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))))
      = Term.Apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))
        (Term.Apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
          (__eo_nil (op.f) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))))) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  simp only [eF]
  have eG : __eo_mk_apply (Term.UOp UserOp.concat)
        (Term.Apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))
          (Term.Apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
            (__eo_nil (op.f) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))))))
      = Term.Apply (Term.UOp UserOp.concat)
        (Term.Apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))
          (Term.Apply (Term.Apply (op.f) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
            (__eo_nil (op.f) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))))) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  rw [eG, eo_mk_apply_ne (by intro h; cases h) hrestne]
  rw [eval_concat M _ rest _ _ _ _
        (slice_eval_op op M W cn a an hc0 ha0 ha s (L' + 1) hsW (by omega) hMle) hrest]
  rw [show s + 1 - (L' + 1) = s - L' from by omega]
  exact (closed_split (op.opnat cn.toNat an.toNat) s L'
    (Nat.le_of_lt hL's)).symm

private theorem binary_zero_concat_canonical (M : SmtModel) :
    BvConcatListCanonical M (Term.Binary 0 0) := by
  exact ⟨0, 0, eval_bin M 0 0, by omega, by omega⟩

private theorem base_concat_canonical_op (op : BvOpSpec) (M : SmtModel) (W : Nat)
    (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (s : Nat) (hsW : s < W)
    (hMle : ((s + 1 - 0 : Nat) : Int) ≤ 4294967296) :
    BvConcatListCanonical M
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat)
        (__eo_mk_apply ((op.f).Apply
            ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply
              (Term.Binary ↑W cn)))
          (__eo_mk_apply ((op.f).Apply
              ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply a))
            (__eo_nil (op.f)
              (__eo_typeof ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply
                (Term.Binary ↑W cn)))))))
        (Term.Binary 0 0)) := by
  rw [show Term.Numeral (0:Int) = Term.Numeral ((0:Nat):Int) from by simp]
  have hNILne : __eo_nil (op.f)
      (__eo_typeof ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
        (Term.Numeral ((0:Nat):Int))).Apply (Term.Binary ↑W cn))) ≠ Term.Stuck := by
    rw [op.hnilterm W cn s 0 hsW (by omega) hMle]
    intro h; cases h
  rw [eo_mk_apply_ne (by intro h; cases h) hNILne,
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h),
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h),
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)]
  refine ⟨?_, binary_zero_concat_canonical M⟩
  let p : Nat := ((op.opnat cn.toNat an.toNat) / 2^0) % 2^(s + 1 - 0)
  exact ⟨s + 1 - 0, (p : Int),
    by
      dsimp [p]
      exact slice_eval_op op M W cn a an hc0 ha0 ha s 0 hsW (by omega) hMle,
    Int.natCast_nonneg _,
    by
      dsimp [p]
      exact natCast_mod_lt _ _⟩

private theorem emit_concat_canonical_op (op : BvOpSpec) (M : SmtModel) (W : Nat)
    (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (hane : a ≠ Term.Stuck)
    (s L' : Nat) (hL's : L' < s) (hsW : s < W)
    (hMle : ((s + 1 - (L' + 1) : Nat) : Int) ≤ 4294967296)
    (rest : Term) (hrestCan : BvConcatListCanonical M rest)
    (hrestne : rest ≠ Term.Stuck) :
    BvConcatListCanonical M
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat)
        (__eo_mk_apply (__eo_mk_apply (op.f)
            (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
              (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) (Term.Binary ↑W cn)))
          (__eo_mk_apply (__eo_mk_apply (op.f)
              (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) a))
            (__eo_nil (op.f)
              (__eo_typeof (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) (Term.Binary ↑W cn)))))))
        rest) := by
  have hbr : (↑L' : Int) + 1 = ↑(L' + 1) := by omega
  rw [show __eo_add (Term.Numeral ↑L') (Term.Numeral 1) =
      Term.Numeral ↑(L' + 1) from by
        show Term.Numeral ((↑L' : Int) + 1) = Term.Numeral ↑(L' + 1)
        rw [hbr]]
  have eA : __eo_mk_apply
      (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
      (Term.Binary ↑W cn)
      = Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
        (Term.Binary ↑W cn) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  have eB : __eo_mk_apply
      (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a
      = Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a :=
    eo_mk_apply_ne (by intro h; cases h) hane
  simp only [eA, eB]
  have hNILne : __eo_nil (op.f)
      (__eo_typeof (Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
        (Term.Binary ↑W cn))) ≠ Term.Stuck := by
    rw [op.hnilterm W cn s (L' + 1) hsW (by omega) hMle]
    intro h; cases h
  have eC : __eo_mk_apply (op.f)
      (Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
        (Term.Binary ↑W cn))
      = Term.Apply (op.f)
        (Term.Apply
          (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
          (Term.Binary ↑W cn)) :=
    eo_mk_apply_ne op.hfne (by intro h; cases h)
  have eD : __eo_mk_apply (op.f)
      (Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a)
      = Term.Apply (op.f)
        (Term.Apply
          (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a) :=
    eo_mk_apply_ne op.hfne (by intro h; cases h)
  simp only [eC, eD]
  have eE : __eo_mk_apply
        (Term.Apply (op.f)
          (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
        (__eo_nil (op.f) (__eo_typeof (Term.Apply
          (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
          (Term.Binary ↑W cn))))
      = Term.Apply
        (Term.Apply (op.f)
          (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
        (__eo_nil (op.f) (__eo_typeof (Term.Apply
          (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
          (Term.Binary ↑W cn)))) :=
    eo_mk_apply_ne (by intro h; cases h) hNILne
  simp only [eE]
  have eF : __eo_mk_apply
        (Term.Apply (op.f)
          (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
            (Term.Binary ↑W cn)))
        (Term.Apply
          (Term.Apply (op.f)
            (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
          (__eo_nil (op.f) (__eo_typeof (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
            (Term.Binary ↑W cn)))))
      = Term.Apply
        (Term.Apply (op.f)
          (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
            (Term.Binary ↑W cn)))
        (Term.Apply
          (Term.Apply (op.f)
            (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
          (__eo_nil (op.f) (__eo_typeof (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
            (Term.Binary ↑W cn))))) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  simp only [eF]
  have eG : __eo_mk_apply (Term.UOp UserOp.concat)
        (Term.Apply
          (Term.Apply (op.f)
            (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
              (Term.Binary ↑W cn)))
          (Term.Apply
            (Term.Apply (op.f)
              (Term.Apply
                (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                  (Term.Numeral ↑(L' + 1))) a))
            (__eo_nil (op.f) (__eo_typeof (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                (Term.Numeral ↑(L' + 1)))
              (Term.Binary ↑W cn))))))
      = Term.Apply (Term.UOp UserOp.concat)
        (Term.Apply
          (Term.Apply (op.f)
            (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1)))
              (Term.Binary ↑W cn)))
          (Term.Apply
            (Term.Apply (op.f)
              (Term.Apply
                (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                  (Term.Numeral ↑(L' + 1))) a))
            (__eo_nil (op.f) (__eo_typeof (Term.Apply
              (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                (Term.Numeral ↑(L' + 1)))
              (Term.Binary ↑W cn)))))) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  rw [eG, eo_mk_apply_ne (by intro h; cases h) hrestne]
  refine ⟨?_, hrestCan⟩
  let p : Nat := ((op.opnat cn.toNat an.toNat) / 2^(L' + 1)) %
    2^(s + 1 - (L' + 1))
  exact ⟨s + 1 - (L' + 1), (p : Int),
    by
      dsimp [p]
      exact slice_eval_op op M W cn a an hc0 ha0 ha s (L' + 1) hsW (by omega) hMle,
    Int.natCast_nonneg _,
    by
      dsimp [p]
      exact natCast_mod_lt _ _⟩

private theorem rec_inv_can_op_of_ne (op : BvOpSpec) (M : SmtModel) (W : Nat)
    (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (hane : a ≠ Term.Stuck) :
    ∀ (L : Nat) (bs : Term), FB bs L → ∀ (bn : Term), bn ≠ Term.Stuck →
    ∀ (s : Nat), L ≤ s + 1 → s < W →
      __bv_mk_bitwise_slicing_rec (op.f)
        (Term.Binary ↑W cn) a bs bn (Term.Numeral ↑s) (Term.Numeral ((↑L : Int) - 1))
          ≠ Term.Stuck →
      __smtx_model_eval M (__eo_to_smt (__bv_mk_bitwise_slicing_rec (op.f)
        (Term.Binary ↑W cn) a bs bn (Term.Numeral ↑s) (Term.Numeral ((↑L : Int) - 1))))
        = SmtValue.Binary ↑(s + 1) ↑((op.opnat cn.toNat an.toNat) % 2^(s + 1)) ∧
      BvConcatListCanonical M (__bv_mk_bitwise_slicing_rec (op.f)
        (Term.Binary ↑W cn) a bs bn (Term.Numeral ↑s) (Term.Numeral ((↑L : Int) - 1))) := by
  intro L bs hFB
  induction hFB with
  | nil =>
      intro bn hbn s hLs hsW hThisNe
      rw [__bv_mk_bitwise_slicing_rec.eq_7 (op.f) (Term.Binary ↑W cn) a
        bn (Term.Numeral ↑s) (Term.Numeral ((↑(0:Nat) : Int) - 1))
        op.hfne (by intro h; cases h) hane hbn (by intro h; cases h)
        (by intro h; cases h)] at hThisNe ⊢
      have hMle : ((s + 1 - 0 : Nat) : Int) ≤ 4294967296 := by
        have hConcatLeft := eo_mk_apply_left_ne_stuck_of_ne hThisNe
        have hSlice := eo_mk_apply_right_ne_stuck_of_ne hConcatLeft
        have hInner := eo_mk_apply_right_ne_stuck_of_ne hSlice
        have hNilNe := eo_mk_apply_right_ne_stuck_of_ne hInner
        exact op.hnilbound W cn s 0 hsW (by omega) hNilNe
      constructor
      · exact base_eval_op op M W cn a an hc0 ha0 ha s hsW hMle
      · exact base_concat_canonical_op op M W cn a an hc0 ha0 ha s hsW hMle
  | cons b bs' L' hb hFB' ih =>
      intro bn hbn s hLs hsW hThisNe
      rw [show ((↑(L' + 1) : Int) - 1) = ↑L' from by push_cast; omega] at hThisNe ⊢
      rw [__bv_mk_bitwise_slicing_rec.eq_8 (op.f) (Term.Binary ↑W cn) a bn
        (Term.Numeral ↑s) (Term.Numeral ↑L') b bs'
        op.hfne (by intro h; cases h) hane hbn (by intro h; cases h)
        (by intro h; cases h)] at hThisNe ⊢
      rw [show __eo_add (Term.Numeral ↑L') (Term.Numeral (-1)) =
          Term.Numeral ((↑L' : Int) - 1) from rfl, eo_eq_ne hb hbn] at hThisNe ⊢
      cases hbb : native_teq bn b
      · rw [hbb] at hThisNe
        rw [eo_ite_false] at hThisNe ⊢
        have hbr : (↑L' : Int) + 1 = ↑(L' + 1) := by omega
        rw [show __eo_add (Term.Numeral ↑L') (Term.Numeral 1) =
            Term.Numeral ↑(L' + 1) from by
              show Term.Numeral ((↑L' : Int) + 1) = Term.Numeral ↑(L' + 1)
              rw [hbr]] at hThisNe ⊢
        have hrestNe :
            __bv_mk_bitwise_slicing_rec op.f (Term.Binary ↑W cn) a bs' b
              (Term.Numeral ↑L') (Term.Numeral ((↑L' : Int) - 1)) ≠ Term.Stuck :=
          eo_mk_apply_right_ne_stuck_of_ne hThisNe
        rcases ih b hb L' (by omega) (by omega) hrestNe with
          ⟨hrestEval, hrestCan⟩
        have hConcatLeft := eo_mk_apply_left_ne_stuck_of_ne hThisNe
        have hSlice := eo_mk_apply_right_ne_stuck_of_ne hConcatLeft
        have hInner := eo_mk_apply_right_ne_stuck_of_ne hSlice
        have hNilNe := eo_mk_apply_right_ne_stuck_of_ne hInner
        have hLo : L' + 1 ≤ s :=
          extract_slice_lower_le_of_nil_ne op.f W cn s (L' + 1) hsW hNilNe
        have hMle : ((s + 1 - (L' + 1) : Nat) : Int) ≤ 4294967296 :=
          op.hnilbound W cn s (L' + 1) hsW hLo hNilNe
        constructor
        · exact emit_eval_op op M W cn a an hc0 ha0 ha hane s L' (by omega) hsW
            hMle _ hrestEval hrestNe
        · exact emit_concat_canonical_op op M W cn a an hc0 ha0 ha hane s L'
            (by omega) hsW hMle _ hrestCan hrestNe
      · rw [hbb] at hThisNe
        rw [eo_ite_true] at hThisNe ⊢
        exact ih b hb s (by omega) hsW hThisNe


private theorem opnat_lt (op : BvOpSpec) (W a b : Nat) (ha : a < 2^W) (hb : b < 2^W) :
    op.opnat a b < 2^W := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hpow : 2^W ≤ 2^i := Nat.pow_le_pow_right (by omega) hi
  rw [op.htb, Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]
  exact op.hgff

private theorem zero_width_rec_stuck_op (op : BvOpSpec)
    (a bn : Term) (hane : a ≠ Term.Stuck) (hbn : bn ≠ Term.Stuck) :
    __bv_mk_bitwise_slicing_rec op.f (Term.Binary 0 0) a
        (Term.Binary 0 0) bn (Term.Numeral (-1)) (Term.Numeral (-1)) =
      Term.Stuck := by
  rw [__bv_mk_bitwise_slicing_rec.eq_7 op.f (Term.Binary 0 0) a
    bn (Term.Numeral (-1)) (Term.Numeral (-1))
    op.hfne (by intro h; cases h) hane hbn (by intro h; cases h)
    (by intro h; cases h)]
  have hType :
      __eo_typeof
          (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral (-1)) (Term.Numeral 0))
            (Term.Binary 0 0)) =
        Term.Stuck := by
    native_decide
  simp [hType, __eo_nil, __eo_mk_apply]

private theorem is_bin_eq {a : Term} (h : __eo_is_bin a = Term.Boolean true) :
    ∃ w n, a = Term.Binary w n := by
  cases a <;>
    simp_all [__eo_is_bin, __eo_is_bin_internal, native_and, native_not, native_teq, reduceCtorEq]

private theorem is_bin_binary (w n : Int) : __eo_is_bin (Term.Binary w n) = Term.Boolean true := by
  simp [__eo_is_bin, __eo_is_bin_internal, native_and, native_not, native_teq, reduceCtorEq]

private theorem eq_binary_false (a : Term) (w n : Int) (hne : a ≠ Term.Stuck)
    (h : __eo_is_bin a = Term.Boolean false) :
    __eo_eq a (Term.Binary w n) = Term.Boolean false := by
  cases a <;>
    simp_all [__eo_eq, __eo_is_bin, __eo_is_bin_internal, native_and, native_not, native_teq,
      reduceCtorEq]

-- A constant-bearing right-spine of an op-list whose operand evals are canonical width-W.
inductive Spine (op : BvOpSpec) (M : SmtModel) (W : Nat) : Term → Prop
  | head (a1 b : Term) (cn vb : Int) (hcn0 : 0 ≤ cn) (hcn1 : cn < 2^W)
      (hev : __smtx_model_eval M (__eo_to_smt a1) = SmtValue.Binary ↑W cn)
      (hbin : __eo_is_bin a1 = Term.Boolean true)
      (hty : __smtx_typeof (__eo_to_smt b) = SmtType.BitVec ↑W)
      (hlist : __eo_is_list op.f b = Term.Boolean true)
      (hvb0 : 0 ≤ vb) (hvb1 : vb < 2^W)
      (hbev : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Binary ↑W vb) :
      Spine op M W (Term.Apply (Term.Apply op.f a1) b)
  | tail (a1 b : Term) (va : Int) (hva0 : 0 ≤ va) (hva1 : va < 2^W)
      (hev : __smtx_model_eval M (__eo_to_smt a1) = SmtValue.Binary ↑W va)
      (hty : __smtx_typeof (__eo_to_smt a1) = SmtType.BitVec ↑W)
      (hbin : __eo_is_bin a1 = Term.Boolean false)
      (hsp : Spine op M W b) :
      Spine op M W (Term.Apply (Term.Apply op.f a1) b)

private theorem is_list_cons_self (op : BvOpSpec) (x y : Term)
    (hy : __eo_is_list op.f y = Term.Boolean true) :
    __eo_is_list op.f (Term.Apply (Term.Apply op.f x) y) = Term.Boolean true := by
  have hyne : y ≠ Term.Stuck := by
    intro h; subst y
    cases hf : op.f <;> simp [__eo_is_list, hf] at hy
  have hyok : __eo_is_ok (__eo_get_nil_rec op.f y) = Term.Boolean true := by
    rw [← islist_isok op.f y op.hfne hyne]
    exact hy
  rw [islist_isok op.f _ op.hfne (by intro h; cases h), gnr_cons op.f op.f x y op.hfne]
  rw [requires_refl op.f _ op.hfne]
  exact hyok

private theorem fold_eval (op : BvOpSpec) (M : SmtModel) (W : Nat) :
    ∀ lhs, Spine op M W lhs → ∃ (cn vle : Int),
      __bv_get_first_const_child lhs = Term.Binary ↑W cn ∧ 0 ≤ cn ∧ cn < 2^W ∧
      __eo_is_list op.f (__eo_list_erase_rec lhs (Term.Binary ↑W cn)) = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt (__eo_list_erase_rec lhs (Term.Binary ↑W cn))) =
        SmtType.BitVec ↑W ∧
      __smtx_model_eval M (__eo_to_smt (__eo_list_erase_rec lhs (Term.Binary ↑W cn)))
        = SmtValue.Binary ↑W vle ∧ 0 ≤ vle ∧ vle < 2^W ∧
      __smtx_model_eval M (__eo_to_smt lhs)
        = op.opval (SmtValue.Binary ↑W cn) (SmtValue.Binary ↑W vle) := by
  intro lhs hsp
  have hpc : ((2^W : Nat) : Int) = (2:Int)^W := by norm_cast
  induction hsp with
  | head a1 b cn vb hcn0 hcn1 hev hbin htyb hlistb hvb0 hvb1 hbev =>
      obtain ⟨w', n', rfl⟩ := is_bin_eq hbin
      rw [eval_bin] at hev
      injection hev with hw hn; subst w'; subst n'
      refine ⟨cn, vb, ?_, hcn0, hcn1, ?_, ?_, ?_, hvb0, hvb1, ?_⟩
      · show __eo_ite (__eo_is_bin (Term.Binary ↑W cn)) (Term.Binary ↑W cn)
            (__bv_get_first_const_child b) = Term.Binary ↑W cn
        rw [is_bin_binary, eo_ite_true]
      · show __eo_is_list op.f (__eo_ite (__eo_eq (Term.Binary ↑W cn)
            (Term.Binary ↑W cn)) b (__eo_mk_apply (Term.Apply op.f (Term.Binary ↑W cn))
            (__eo_list_erase_rec b (Term.Binary ↑W cn)))) = Term.Boolean true
        rw [show __eo_eq (Term.Binary ↑W cn) (Term.Binary ↑W cn) = Term.Boolean true from by
              simp [__eo_eq, native_teq], eo_ite_true]
        exact hlistb
      · show __smtx_typeof (__eo_to_smt (__eo_ite (__eo_eq (Term.Binary ↑W cn)
            (Term.Binary ↑W cn)) b (__eo_mk_apply (Term.Apply op.f (Term.Binary ↑W cn))
            (__eo_list_erase_rec b (Term.Binary ↑W cn))))) = SmtType.BitVec ↑W
        rw [show __eo_eq (Term.Binary ↑W cn) (Term.Binary ↑W cn) = Term.Boolean true from by
              simp [__eo_eq, native_teq], eo_ite_true]
        exact htyb
      · show __smtx_model_eval M (__eo_to_smt (__eo_ite (__eo_eq (Term.Binary ↑W cn)
            (Term.Binary ↑W cn)) b (__eo_mk_apply (Term.Apply op.f (Term.Binary ↑W cn))
            (__eo_list_erase_rec b (Term.Binary ↑W cn))))) = _
        rw [show __eo_eq (Term.Binary ↑W cn) (Term.Binary ↑W cn) = Term.Boolean true from by
              simp [__eo_eq, native_teq], eo_ite_true]
        exact hbev
      · exact op.heval M (Term.Binary ↑W cn) b ↑W cn ↑W vb (eval_bin M ↑W cn) hbev
  | tail a1 b va hva0 hva1 hev htya hbin hsp ih =>
      obtain ⟨cnb, vleb, hgfcb, hcnb0, hcnb1, hlistle, htyle, hleb, hvleb0, hvleb1, hevb⟩ := ih
      have hvan : va.toNat < 2^W := by omega
      have hcnbn : cnb.toNat < 2^W := by omega
      have hvlebn : vleb.toNat < 2^W := by omega
      have ha1ne : a1 ≠ Term.Stuck := ne_stuck_of_eval_bin M a1 ↑W va hev
      refine ⟨cnb, ↑(op.opnat va.toNat vleb.toNat), ?_, hcnb0, hcnb1, ?_, ?_, ?_, Int.natCast_nonneg _,
        by exact_mod_cast opnat_lt op W va.toNat vleb.toNat hvan hvlebn, ?_⟩
      · show __eo_ite (__eo_is_bin a1) a1 (__bv_get_first_const_child b) = Term.Binary ↑W cnb
        rw [hbin, eo_ite_false]; exact hgfcb
      · show __eo_is_list op.f (__eo_ite (__eo_eq a1 (Term.Binary ↑W cnb)) b
            (__eo_mk_apply (Term.Apply op.f a1)
              (__eo_list_erase_rec b (Term.Binary ↑W cnb)))) = Term.Boolean true
        rw [eq_binary_false a1 ↑W cnb ha1ne hbin, eo_ite_false,
          eo_mk_apply_ne (by intro h; cases h) (ne_stuck_of_eval_bin M _ ↑W vleb hleb)]
        exact is_list_cons_self op a1 _ hlistle
      · show __smtx_typeof (__eo_to_smt (__eo_ite (__eo_eq a1 (Term.Binary ↑W cnb)) b
            (__eo_mk_apply (Term.Apply op.f a1)
              (__eo_list_erase_rec b (Term.Binary ↑W cnb))))) = SmtType.BitVec ↑W
        rw [eq_binary_false a1 ↑W cnb ha1ne hbin, eo_ite_false,
          eo_mk_apply_ne (by intro h; cases h) (ne_stuck_of_eval_bin M _ ↑W vleb hleb)]
        rw [op.htypeof a1 _, htya, htyle]
        simp [__smtx_typeof_bv_op_2, native_nateq, Smtm.native_nateq, native_ite]
      · show __smtx_model_eval M (__eo_to_smt (__eo_ite (__eo_eq a1 (Term.Binary ↑W cnb)) b
            (__eo_mk_apply (Term.Apply op.f a1)
              (__eo_list_erase_rec b (Term.Binary ↑W cnb))))) = _
        rw [eq_binary_false a1 ↑W cnb ha1ne hbin, eo_ite_false,
            eo_mk_apply_ne (by intro h; cases h) (ne_stuck_of_eval_bin M _ ↑W vleb hleb),
            op.heval M a1 _ ↑W va ↑W vleb hev hleb,
            op.hvalN W va vleb hva0 hva1 hvleb0 hvleb1]
      · have hevb' : __smtx_model_eval M (__eo_to_smt b)
            = SmtValue.Binary ↑W ↑(op.opnat cnb.toNat vleb.toNat) := by
          rw [hevb, op.hvalN W cnb vleb hcnb0 hcnb1 hvleb0 hvleb1]
        rw [op.heval M a1 b ↑W va ↑W _ hev hevb',
            op.hvalN W va _ hva0 hva1 (Int.natCast_nonneg _)
              (by exact_mod_cast opnat_lt op W cnb.toNat vleb.toNat hcnbn hvlebn),
            op.hvalN W cnb _ hcnb0 hcnb1 (Int.natCast_nonneg _)
              (by exact_mod_cast opnat_lt op W va.toNat vleb.toNat hvan hvlebn)]
        congr 2
        rw [Int.toNat_natCast, Int.toNat_natCast, ← op.hassoc, op.hcomm va.toNat, op.hassoc]

private theorem gfc_ne_stuck_shape {lhs : Term} (h : __bv_get_first_const_child lhs ≠ Term.Stuck) :
    ∃ g a1 b, lhs = Term.Apply (Term.Apply g a1) b := by
  cases lhs with
  | Apply lhs1 b =>
    cases lhs1 with
    | Apply g a1 => exact ⟨g, a1, b, rfl⟩
    | _ => exact (h rfl).elim
  | _ => exact (h rfl).elim

private theorem mk_spine_fuel (op : BvOpSpec) (M : SmtModel) (hM : model_wf M) (W : Nat) :
    ∀ (n : Nat) (lhs : Term), sizeOf lhs ≤ n →
      term_has_non_none_type (__eo_to_smt lhs) →
      __smtx_typeof (__eo_to_smt lhs) = SmtType.BitVec ↑W →
      __eo_is_list op.f lhs = Term.Boolean true →
      __bv_get_first_const_child lhs ≠ Term.Stuck →
      Spine op M W lhs := by
  intro n
  induction n with
  | zero =>
      intro lhs hsz _ _ _ hgfc
      obtain ⟨g, a1, b, rfl⟩ := gfc_ne_stuck_shape hgfc
      simp only [Term.Apply.sizeOf_spec] at hsz; omega
  | succ n ih =>
      intro lhs hsz hnn hty hlist hgfc
      obtain ⟨g, a1, b, rfl⟩ := gfc_ne_stuck_shape hgfc
      obtain ⟨hgeq, hlist2⟩ := is_list_cons_inv op g a1 b hlist
      subst hgeq
      obtain ⟨w, hta1, hta2⟩ := bv_binop_args_of_non_none
        (op := fun _ _ => __eo_to_smt (Term.Apply (Term.Apply op.f a1) b))
        (t1 := __eo_to_smt a1) (t2 := __eo_to_smt b) (op.htypeof a1 b) hnn
      have hbv := op.htypeof a1 b
      rw [hta1, hta2, hty] at hbv
      have hwW : w = (↑W : native_Nat) := by
        simp only [__smtx_typeof_bv_op_2, native_nateq, native_ite] at hbv
        exact (SmtType.BitVec.inj hbv).symm
      rw [hwW] at hta1 hta2
      have hnn1 : term_has_non_none_type (__eo_to_smt a1) := by
        rw [term_has_non_none_type, hta1]; exact fun h => by cases h
      have hnn2 : term_has_non_none_type (__eo_to_smt b) := by
        rw [term_has_non_none_type, hta2]; exact fun h => by cases h
      obtain ⟨ca, heva, hca0, hca1⟩ := bv_term_eval_canonical M hM (__eo_to_smt a1) W hnn1 hta1
      obtain ⟨cb, hevb, hcb0, hcb1⟩ := bv_term_eval_canonical M hM (__eo_to_smt b) W hnn2 hta2
      have hisbin : __eo_is_bin a1 = Term.Boolean
          (native_and (native_not (native_teq a1 Term.Stuck))
            (native_teq (__eo_is_bin_internal a1) (Term.Boolean true))) := rfl
      by_cases hb : (native_and (native_not (native_teq a1 Term.Stuck))
          (native_teq (__eo_is_bin_internal a1) (Term.Boolean true))) = true
      · exact Spine.head a1 b ca cb hca0 hca1 heva (by rw [hisbin, hb]) hta2 hlist2
          hcb0 hcb1 hevb
      · have hbf : __eo_is_bin a1 = Term.Boolean false := by
          rw [hisbin]; simp only [Bool.not_eq_true] at hb; rw [hb]
        have hgfc2 : __bv_get_first_const_child b ≠ Term.Stuck := by
          have he : __bv_get_first_const_child (Term.Apply (Term.Apply op.f a1) b)
              = __bv_get_first_const_child b := by
            show __eo_ite (__eo_is_bin a1) a1 (__bv_get_first_const_child b) = _
            rw [hbf, eo_ite_false]
          rw [he] at hgfc; exact hgfc
        have hszb : sizeOf b ≤ n := by
          simp only [Term.Apply.sizeOf_spec] at hsz; omega
        exact Spine.tail a1 b ca hca0 hca1 heva hta1 hbf
          (ih b hszb hnn2 hta2 hlist2 hgfc2)

private theorem mk_spine (op : BvOpSpec) (M : SmtModel) (hM : model_wf M) (W : Nat)
    (lhs : Term) (hnn : term_has_non_none_type (__eo_to_smt lhs))
    (hty : __smtx_typeof (__eo_to_smt lhs) = SmtType.BitVec ↑W)
    (hlist : __eo_is_list op.f lhs = Term.Boolean true)
    (hgfc : __bv_get_first_const_child lhs ≠ Term.Stuck) :
    Spine op M W lhs :=
  mk_spine_fuel op M hM W (sizeOf lhs) lhs (Nat.le_refl _) hnn hty hlist hgfc


-- singleton_elim preserves the evaluated value on a width-W op-list.
private theorem sing_elim_eval (op : BvOpSpec) (M : SmtModel) (hM : model_wf M) (W : Nat)
    (Z : Term) (hnn : term_has_non_none_type (__eo_to_smt Z))
    (hty : __smtx_typeof (__eo_to_smt Z) = SmtType.BitVec ↑W)
    (hlist : __eo_is_list op.f Z = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt (__eo_list_singleton_elim op.f Z))
      = __smtx_model_eval M (__eo_to_smt Z) := by
  have hcollapse : __eo_list_singleton_elim op.f Z = __eo_list_singleton_elim_2 Z := by
    show __eo_requires (__eo_is_list op.f Z) (Term.Boolean true) (__eo_list_singleton_elim_2 Z)
      = __eo_list_singleton_elim_2 Z
    rw [hlist]; exact requires_refl (Term.Boolean true) _ (by intro h; cases h)
  rw [hcollapse]
  cases Z <;> try rfl
  rename_i Z1 rest
  cases Z1 <;> try rfl
  rename_i g x
  obtain ⟨hgeq, _⟩ := is_list_cons_inv op g x rest hlist
  subst hgeq
  obtain ⟨w, htx, htrest⟩ := bv_binop_args_of_non_none
    (op := fun _ _ => __eo_to_smt (Term.Apply (Term.Apply op.f x) rest))
    (t1 := __eo_to_smt x) (t2 := __eo_to_smt rest) (op.htypeof x rest) hnn
  have hbv := op.htypeof x rest
  rw [htx, htrest, hty] at hbv
  have hwW : w = (↑W : native_Nat) := by
    simp only [__smtx_typeof_bv_op_2, native_nateq, native_ite] at hbv
    exact (SmtType.BitVec.inj hbv).symm
  rw [hwW] at htx htrest
  obtain ⟨vx, hevx, hvx0, hvx1⟩ := bv_term_eval_canonical M hM (__eo_to_smt x) W
    (by rw [term_has_non_none_type, htx]; exact fun h => by cases h) htx
  obtain ⟨vy, hevy, hvy0, hvy1⟩ := bv_term_eval_canonical M hM (__eo_to_smt rest) W
    (by rw [term_has_non_none_type, htrest]; exact fun h => by cases h) htrest
  have hevZ : __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply op.f x) rest))
      = op.opval (SmtValue.Binary ↑W vx) (SmtValue.Binary ↑W vy) :=
    op.heval M x rest ↑W vx ↑W vy hevx hevy
  have hrestne : rest ≠ Term.Stuck := ne_stuck_of_eval_bin M rest ↑W vy hevy
  obtain ⟨b, hb⟩ := op.hnilbool rest hrestne
  show __smtx_model_eval M (__eo_to_smt (__eo_ite (__eo_is_list_nil op.f rest) x
      (Term.Apply (Term.Apply op.f x) rest))) = _
  cases b
  · rw [hb, eo_ite_false]
  · rw [hb, eo_ite_true, hevx, hevZ]
    have hvyn : vy = op.nilpay W := op.hnilval M rest W vy hb hevy hvy0 hvy1
    rw [hvyn, op.hnilid W vx hvx0 hvx1]

private theorem mk_bitwise_shape (lhs : Term)
    (h : __bv_mk_bitwise_slicing lhs ≠ Term.Stuck) :
    ∃ f a1 a2, lhs = Term.Apply (Term.Apply f a1) a2 := by
  by_cases hsh : ∃ f a1 a2, lhs = Term.Apply (Term.Apply f a1) a2
  · exact hsh
  · exfalso; apply h
    rw [__bv_mk_bitwise_slicing.eq_2]
    intro f a1 a2 hEq; exact hsh ⟨f, a1, a2, hEq⟩

private theorem list_singleton_elim_arg_ne_stuck {f a : Term}
    (h : __eo_list_singleton_elim f a ≠ Term.Stuck) : a ≠ Term.Stuck := by
  intro ha
  subst a
  apply h
  cases f <;>
    simp [__eo_list_singleton_elim, __eo_is_list, __eo_requires, native_ite,
      native_teq]

private theorem rec_const_arg_ne_stuck {f c a bs bn start stop : Term}
    (h : __bv_mk_bitwise_slicing_rec f c a bs bn start stop ≠ Term.Stuck) :
    c ≠ Term.Stuck := by
  intro hc
  subst c
  have hStuck :
      __bv_mk_bitwise_slicing_rec f Term.Stuck a bs bn start stop = Term.Stuck := by
    by_cases hf : f = Term.Stuck
    · subst f
      rw [__bv_mk_bitwise_slicing_rec.eq_1]
    · rw [__bv_mk_bitwise_slicing_rec.eq_2 f a bs bn start stop hf]
  exact h hStuck

private theorem rec_payload_arg_ne_stuck {f c a bs bn start stop : Term}
    (h : __bv_mk_bitwise_slicing_rec f c a bs bn start stop ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro ha
  subst a
  have hStuck :
      __bv_mk_bitwise_slicing_rec f c Term.Stuck bs bn start stop = Term.Stuck := by
    by_cases hf : f = Term.Stuck
    · subst f
      rw [__bv_mk_bitwise_slicing_rec.eq_1]
    · by_cases hc : c = Term.Stuck
      · subst c
        rw [__bv_mk_bitwise_slicing_rec.eq_2 f Term.Stuck bs bn start stop hf]
      · rw [__bv_mk_bitwise_slicing_rec.eq_3 f c bs bn start stop hf hc]
  exact h hStuck

private theorem rec_bn_arg_ne_stuck {f c a bs bn start stop : Term}
    (h : __bv_mk_bitwise_slicing_rec f c a bs bn start stop ≠ Term.Stuck) :
    bn ≠ Term.Stuck := by
  intro hbn
  subst bn
  have hStuck :
      __bv_mk_bitwise_slicing_rec f c a bs Term.Stuck start stop = Term.Stuck := by
    by_cases hf : f = Term.Stuck
    · subst f
      rw [__bv_mk_bitwise_slicing_rec.eq_1]
    · by_cases hc : c = Term.Stuck
      · subst c
        rw [__bv_mk_bitwise_slicing_rec.eq_2 f a bs Term.Stuck start stop hf]
      · by_cases ha : a = Term.Stuck
        · subst a
          rw [__bv_mk_bitwise_slicing_rec.eq_3 f c bs Term.Stuck start stop hf hc]
        · rw [__bv_mk_bitwise_slicing_rec.eq_4 f c a bs start stop hf hc ha]
  exact h hStuck

private theorem bitwise_guard_true_cases (f : Term) :
    __eo_or (__eo_or (__eo_eq f (Term.UOp UserOp.bvand))
      (__eo_eq f (Term.UOp UserOp.bvor))) (__eo_eq f (Term.UOp UserOp.bvxor)) =
        Term.Boolean true ->
    f = Term.UOp UserOp.bvand ∨
      f = Term.UOp UserOp.bvor ∨
      f = Term.UOp UserOp.bvxor := by
  intro h
  by_cases hAnd : f = Term.UOp UserOp.bvand
  · exact Or.inl hAnd
  by_cases hOr : f = Term.UOp UserOp.bvor
  · exact Or.inr (Or.inl hOr)
  by_cases hXor : f = Term.UOp UserOp.bvxor
  · exact Or.inr (Or.inr hXor)
  exfalso
  cases f with
  | UOp u =>
      cases u <;>
        first
        | exact hAnd rfl
        | exact hOr rfl
        | exact hXor rfl
        | simp [__eo_eq, __eo_or, native_teq, native_or, SmtEval.native_or] at h
  | _ =>
      simp [__eo_eq, __eo_or, native_teq, native_or, SmtEval.native_or] at h

private theorem bv_bitwise_slicing_eval_rel_op (op : BvOpSpec)
    (M : SmtModel) (hM : model_wf M) (a1 a2 : Term)
    (hExpandedNe :
      __bv_mk_bitwise_slicing (Term.Apply (Term.Apply op.f a1) a2) ≠ Term.Stuck)
    (hRepNN : term_has_non_none_type
      (__eo_to_smt (Term.Apply (Term.Apply op.f a1) a2))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitwise_slicing (Term.Apply (Term.Apply op.f a1) a2))))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply op.f a1) a2))) := by
  let lhs := Term.Apply (Term.Apply op.f a1) a2
  let c := __bv_get_first_const_child lhs
  let width := __eo_len c
  let start := __eo_add width (Term.Numeral (-1 : native_Int))
  let erased := __eo_list_singleton_elim op.f (__eo_list_erase op.f lhs c)
  let bs := __eo_list_rev (Term.UOp UserOp._at_from_bools)
    (__bv_const_to_bitlist_rec c
      (__eo_requires (__eo_is_neg width) (Term.Boolean false)
        (__iota_rec
          (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) width)
          (Term.Numeral 0))))
  let bn := __eo_eq (__eo_extract c start start) (Term.Binary 1 1)
  let body := __bv_mk_bitwise_slicing_rec op.f c erased bs bn start start
  let guard := __eo_or (__eo_or (__eo_eq op.f (Term.UOp UserOp.bvand))
    (__eo_eq op.f (Term.UOp UserOp.bvor))) (__eo_eq op.f (Term.UOp UserOp.bvxor))
  have hOuterNe :
      __eo_list_singleton_elim (Term.UOp UserOp.concat)
        (__eo_requires guard (Term.Boolean true) body) ≠ Term.Stuck := by
    simpa [lhs, c, width, start, erased, bs, bn, body, guard, __bv_mk_bitwise_slicing]
      using hExpandedNe
  have hReqNe : __eo_requires guard (Term.Boolean true) body ≠ Term.Stuck :=
    list_singleton_elim_arg_ne_stuck hOuterNe
  have hGuardTrue : guard = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReqNe
  have hReqEq : __eo_requires guard (Term.Boolean true) body = body := by
    rw [hGuardTrue]
    exact requires_refl (Term.Boolean true) body (by intro h; cases h)
  have hRecNe : body ≠ Term.Stuck :=
    eo_requires_payload_ne_stuck hReqNe
  have hConstNe : c ≠ Term.Stuck :=
    rec_const_arg_ne_stuck hRecNe
  have hErasedNe : erased ≠ Term.Stuck :=
    rec_payload_arg_ne_stuck hRecNe
  have hBnNe : bn ≠ Term.Stuck :=
    rec_bn_arg_ne_stuck hRecNe
  have hEraseRawNe : __eo_list_erase op.f lhs c ≠ Term.Stuck :=
    list_singleton_elim_arg_ne_stuck hErasedNe
  have hList : __eo_is_list op.f lhs = Term.Boolean true := by
    have hEraseReq :
        __eo_requires (__eo_is_list op.f lhs) (Term.Boolean true)
          (__eo_list_erase_rec lhs c) ≠ Term.Stuck := by
      simpa [__eo_list_erase, lhs, c] using hEraseRawNe
    exact eo_requires_arg_eq_of_ne_stuck hEraseReq
  obtain ⟨W, hty1, hty2⟩ := bv_binop_args_of_non_none
    (op := fun _ _ => __eo_to_smt lhs)
    (t1 := __eo_to_smt a1) (t2 := __eo_to_smt a2)
    (op.htypeof a1 a2) hRepNN
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.BitVec ↑W := by
    dsimp [lhs]
    rw [op.htypeof a1 a2, hty1, hty2]
    simp [__smtx_typeof_bv_op_2, native_nateq, Smtm.native_nateq, native_ite]
  have hSp := mk_spine op M hM W lhs hRepNN hLhsTy hList hConstNe
  rcases fold_eval op M W lhs hSp with
    ⟨cn, vle, hGfc, hc0, hc1, hEraseListRec, hEraseTyRec, hEraseEvalRec,
      hvle0, hvle1, hLhsEval⟩
  have hcEq : c = Term.Binary ↑W cn := by
    simpa [c] using hGfc
  have hWidth : width = Term.Numeral ↑W := by
    dsimp [width]
    rw [hcEq]
    rfl
  have hEraseEq :
      __eo_list_erase op.f lhs c =
        __eo_list_erase_rec lhs (Term.Binary ↑W cn) := by
    change __eo_requires (__eo_is_list op.f lhs) (Term.Boolean true)
        (__eo_list_erase_rec lhs c) = __eo_list_erase_rec lhs (Term.Binary ↑W cn)
    rw [hList]
    rw [requires_refl (Term.Boolean true) _ (by intro h; cases h), hcEq]
  have hErasedEval :
      __smtx_model_eval M (__eo_to_smt erased) = SmtValue.Binary ↑W vle := by
    have hEraseNN : term_has_non_none_type
        (__eo_to_smt (__eo_list_erase_rec lhs (Term.Binary ↑W cn))) := by
      rw [term_has_non_none_type, hEraseTyRec]
      intro h; cases h
    have hSing := sing_elim_eval op M hM W
      (__eo_list_erase_rec lhs (Term.Binary ↑W cn)) hEraseNN hEraseTyRec hEraseListRec
    dsimp [erased]
    rw [hEraseEq, hSing, hEraseEvalRec]
  have hErasedNe' : erased ≠ Term.Stuck :=
    ne_stuck_of_eval_bin M erased ↑W vle hErasedEval
  have hBsFB : FB bs W := by
    simpa [bs, hcEq, hWidth] using bitlist_FB W cn
  have hRecPair :
      __smtx_model_eval M (__eo_to_smt body) =
          SmtValue.Binary ↑W ↑((op.opnat cn.toNat vle.toNat) % 2^W) ∧
        BvConcatListCanonical M body := by
    by_cases hW0 : W = 0
    · subst W
      have hcnZero : cn = 0 := by
        have hc1' : cn < 1 := by simpa using hc1
        omega
      subst cn
      have hvleZero : vle = 0 := by
        have hvle1' : vle < 1 := by simpa using hvle1
        omega
      subst vle
      have hBsNil : bs = Term.Binary 0 0 := by
        exact FB_zero_eq hBsFB
      have hStartNeg : start = Term.Numeral (-1) := by
        dsimp [start]
        rw [hWidth]
        rfl
      exfalso
      apply hRecNe
      simpa [body, hcEq, hBsNil, hStartNeg] using
        zero_width_rec_stuck_op op erased bn hErasedNe' hBnNe
    · have hWpos : 0 < W := Nat.pos_of_ne_zero hW0
      have hOneLe : 1 ≤ W := Nat.succ_le_of_lt hWpos
      have hWsubInt : ((↑W : Int) - 1) = (↑(W - 1) : Int) := by
        rw [← Nat.sub_add_cancel hOneLe]
        push_cast
        omega
      have hWsubNat : W - 1 + 1 = W :=
        Nat.sub_add_cancel hOneLe
      have hStart : start = Term.Numeral (↑(W - 1) : Int) := by
        dsimp [start]
        rw [hWidth]
        change Term.Numeral ((↑W : Int) + (-1)) = Term.Numeral (↑(W - 1) : Int)
        exact congrArg Term.Numeral (by exact hWsubInt)
      have hThisNe :
          __bv_mk_bitwise_slicing_rec op.f (Term.Binary ↑W cn) erased bs bn
            (Term.Numeral ↑(W - 1)) (Term.Numeral ((↑W : Int) - 1)) ≠
              Term.Stuck := by
        simpa [body, hcEq, hStart, hWsubInt] using hRecNe
      have hPair := rec_inv_can_op_of_ne op M W cn erased vle hc0 hvle0 hErasedEval
        hErasedNe' W bs hBsFB bn hBnNe (W - 1) (by omega) (by omega) hThisNe
      simpa [body, hcEq, hStart, hWsubInt, hWsubNat] using hPair
  have hRecEval :
      __smtx_model_eval M (__eo_to_smt body) =
        SmtValue.Binary ↑W ↑((op.opnat cn.toNat vle.toNat) % 2^W) :=
    hRecPair.1
  have hRecCan : BvConcatListCanonical M body :=
    hRecPair.2
  have hOuterList : __eo_is_list (Term.UOp UserOp.concat) body = Term.Boolean true := by
    have hOuterReq :
        __eo_requires (__eo_is_list (Term.UOp UserOp.concat)
          (__eo_requires guard (Term.Boolean true) body))
          (Term.Boolean true)
          (__eo_list_singleton_elim_2
            (__eo_requires guard (Term.Boolean true) body)) ≠ Term.Stuck := by
      simpa [__eo_list_singleton_elim] using hOuterNe
    have hListReq :=
      eo_requires_arg_eq_of_ne_stuck hOuterReq
    simpa [hReqEq] using hListReq
  have hOuterRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.concat) body)))
        (__smtx_model_eval M (__eo_to_smt body)) :=
    bvconcat_singleton_elim_rel_eval M body hOuterList hRecCan
  have hLhsClosed :
      __smtx_model_eval M (__eo_to_smt lhs) =
        SmtValue.Binary ↑W ↑(op.opnat cn.toNat vle.toNat) := by
    rw [hLhsEval, op.hvalN W cn vle hc0 hc1 hvle0 hvle1]
  have hOpNatLt : op.opnat cn.toNat vle.toNat < 2^W := by
    have hcnNat : cn.toNat < 2^W :=
      toNat_lt_pow_of_canonical hc0 hc1
    have hvleNat : vle.toNat < 2^W :=
      toNat_lt_pow_of_canonical hvle0 hvle1
    exact opnat_lt op W cn.toNat vle.toNat hcnNat hvleNat
  have hRecClosed :
      __smtx_model_eval M (__eo_to_smt body) =
        SmtValue.Binary ↑W ↑(op.opnat cn.toNat vle.toNat) := by
    rw [hRecEval, Nat.mod_eq_of_lt hOpNatLt]
  have hExpandedEq :
      __bv_mk_bitwise_slicing (Term.Apply (Term.Apply op.f a1) a2) =
        __eo_list_singleton_elim (Term.UOp UserOp.concat) body := by
    simp [lhs, c, width, start, erased, bs, bn, body, guard, __bv_mk_bitwise_slicing,
      hReqEq]
  rw [hExpandedEq]
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M
      (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.concat) body)))
    (__smtx_model_eval M (__eo_to_smt body))
    (__smtx_model_eval M (__eo_to_smt lhs))
    hOuterRel
    (by rw [hRecClosed, hLhsClosed]; exact RuleProofs.smt_value_rel_refl _)

/-- The soundness core of the wrapper: the sliced form `__bv_mk_bitwise_slicing lhs`
evaluates to the same bitvector value as `lhs`. -/
private theorem bv_bitwise_slicing_eval_rel (M : SmtModel) (hM : model_wf M)
    (lhs : Term)
    (hExpandedNe : __bv_mk_bitwise_slicing lhs ≠ Term.Stuck)
    (hRepNN : term_has_non_none_type (__eo_to_smt lhs)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__bv_mk_bitwise_slicing lhs)))
      (__smtx_model_eval M (__eo_to_smt lhs)) := by
  rcases mk_bitwise_shape lhs hExpandedNe with ⟨f, a1, a2, hShape⟩
  subst lhs
  let body :=
    __bv_mk_bitwise_slicing_rec f
      (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))
      (__eo_list_singleton_elim f
        (__eo_list_erase f (Term.Apply (Term.Apply f a1) a2)
          (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))))
      (__eo_list_rev (Term.UOp UserOp._at_from_bools)
        (__bv_const_to_bitlist_rec
          (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))
          (__eo_requires (__eo_is_neg (__eo_len
              (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))))
            (Term.Boolean false)
            (__iota_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0)
                (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))))
              (Term.Numeral 0)))))
      (__eo_eq
        (__eo_extract (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))
          (__eo_add (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2)))
            (Term.Numeral (-1 : native_Int)))
          (__eo_add (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2)))
            (Term.Numeral (-1 : native_Int))))
        (Term.Binary 1 1))
      (__eo_add (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2)))
        (Term.Numeral (-1 : native_Int)))
      (__eo_add (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2)))
        (Term.Numeral (-1 : native_Int)))
  let guard := __eo_or (__eo_or (__eo_eq f (Term.UOp UserOp.bvand))
    (__eo_eq f (Term.UOp UserOp.bvor))) (__eo_eq f (Term.UOp UserOp.bvxor))
  have hReqNe : __eo_requires guard (Term.Boolean true) body ≠ Term.Stuck := by
    apply list_singleton_elim_arg_ne_stuck
    simpa [body, guard, __bv_mk_bitwise_slicing] using hExpandedNe
  have hGuardTrue : guard = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReqNe
  rcases bitwise_guard_true_cases f hGuardTrue with hAnd | hRest
  · subst f
    exact bv_bitwise_slicing_eval_rel_op bvOpAnd M hM a1 a2 hExpandedNe hRepNN
  · rcases hRest with hOr | hXor
    · subst f
      exact bv_bitwise_slicing_eval_rel_op bvOpOr M hM a1 a2 hExpandedNe hRepNN
    · subst f
      exact bv_bitwise_slicing_eval_rel_op bvOpXor M hM a1 a2 hExpandedNe hRepNN

public theorem cmd_step_bv_bitwise_slicing_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_bitwise_slicing args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_bitwise_slicing args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_bitwise_slicing args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.bv_bitwise_slicing args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons A2 argsRest =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons n rest =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                  cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_bv_bitwise_slicing A)
              change __eo_typeof (__eo_prog_bv_bitwise_slicing A) = Term.Bool
                at hResultTy
              have hProgNe' : __eo_prog_bv_bitwise_slicing A ≠ Term.Stuck := by
                exact hProgNe
              rcases bv_bitwise_slicing_shape_of_ne_stuck A hProgNe' with
                ⟨lhs, rhs, hShape⟩
              subst A
              let expanded := __bv_mk_bitwise_slicing lhs
              let orig :=
                Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
              have hReqNe :
                  __eo_requires expanded rhs orig ≠ Term.Stuck := by
                simpa [__eo_prog_bv_bitwise_slicing, expanded, orig] using
                  hProgNe'
              have hExpandedEq : expanded = rhs :=
                eo_requires_arg_eq_of_ne_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                eo_requires_left_ne_stuck_of_ne_stuck hReqNe
              have hRhsNe : rhs ≠ Term.Stuck := by
                rw [← hExpandedEq]; exact hExpandedNe
              have hProgEq :
                  __eo_prog_bv_bitwise_slicing
                      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) =
                    orig := by
                rw [__eo_prog_bv_bitwise_slicing.eq_1]
                change __eo_requires expanded rhs orig = orig
                simp [__eo_requires, hExpandedEq, hRhsNe, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hOrigTy : __eo_typeof orig = Term.Bool := by
                simpa [hProgEq, orig] using hResultTy
              have hOrigBool : RuleProofs.eo_has_bool_type orig :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  orig hATrans hOrigTy
              rcases
                  RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    lhs rhs hOrigBool with
                ⟨_hSameTy, hRepNN⟩
              have hRelExpanded :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt expanded))
                    (__smtx_model_eval M (__eo_to_smt lhs)) := by
                simpa [expanded] using
                  bv_bitwise_slicing_eval_rel M hM lhs hExpandedNe hRepNN
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt lhs))
                    (__smtx_model_eval M (__eo_to_smt rhs)) := by
                rw [← hExpandedEq]
                exact RuleProofs.smt_value_rel_symm _ _ hRelExpanded
              have hFact :
                  eo_interprets M (__eo_prog_bv_bitwise_slicing orig) true := by
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
