module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvExtractTerm (x hi lo : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract hi lo) x

def bvExtractNotLhs (x hi lo : Term) : Term :=
  bvExtractTerm (Term.Apply (Term.UOp UserOp.bvnot) x) hi lo

def bvExtractNotRhs (x hi lo : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) (bvExtractTerm x hi lo)

def bvExtractNotTerm (x hi lo : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvExtractNotLhs x hi lo))
    (bvExtractNotRhs x hi lo)

theorem eo_typeof_extract_arg_bitvec_of_ne_stuck
    {A hi B lo C : Term}
    (h : __eo_typeof_extract A hi B lo C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_extract at h
  split at h <;> simp at h ⊢

theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) := by
  intro hXTrans hXType
  have hSmtType :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x) rfl
        hXTrans hXType
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;>
      simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals exact False.elim (hXTrans hSmtType)

private theorem eo_typeof_extract_body_of_ne_stuck
    {hi lo w : Term}
    (h : __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
        (Term.Apply (Term.UOp UserOp.BitVec) w) ≠ Term.Stuck) :
    __eo_typeof hi = Term.UOp UserOp.Int ∧
      __eo_typeof lo = Term.UOp UserOp.Int ∧
      __eo_mk_apply (Term.UOp UserOp.BitVec)
          (__eo_requires (__eo_gt lo (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true)
            (__eo_requires (__eo_gt w hi) (Term.Boolean true)
              (__eo_requires
                (__eo_gt
                  (__eo_add (__eo_add hi (__eo_neg lo)) (Term.Numeral 1))
                  (Term.Numeral 0))
                (Term.Boolean true)
                (__eo_add (__eo_add hi (__eo_neg lo))
                  (Term.Numeral 1))))) ≠
        Term.Stuck := by
  unfold __eo_typeof_extract at h
  split at h <;> simp_all

private theorem numeral_nonneg_of_gt_neg_one
    (t : Term)
    (h : __eo_gt t (Term.Numeral (-1 : native_Int)) = Term.Boolean true) :
    ∃ n : native_Int, t = Term.Numeral n ∧ native_zleq 0 n = true := by
  cases t <;> simp [__eo_gt] at h
  case Numeral n =>
    have hn : (-1 : Int) < n := by simpa [SmtEval.native_zlt] using h
    have hn0 : (0 : Int) ≤ n := by simpa using Int.add_one_le_iff.mpr hn
    exact ⟨n, rfl, by simpa [SmtEval.native_zleq] using hn0⟩

theorem bv_extract_context_of_non_stuck
    (x hi lo : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractTerm x hi lo) ≠ Term.Stuck ->
    ∃ w h l,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      hi = Term.Numeral h ∧ lo = Term.Numeral l ∧
      native_zleq 0 w = true ∧ native_zleq 0 l = true ∧
      native_zlt h w = true ∧
      native_zlt 0 (native_zplus (native_zplus h 1) (native_zneg l)) = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hExtractNe
  change __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
      (__eo_typeof x) ≠ Term.Stuck at hExtractNe
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck hExtractNe with
    ⟨wTerm, hXTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x wTerm hXTrans hXTy with
    ⟨w, hWTerm, hw0, hXSmtTy⟩
  subst wTerm
  have hExtractNe' :
      __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
          (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) ≠
        Term.Stuck := by
    simpa [hXTy] using hExtractNe
  rcases eo_typeof_extract_body_of_ne_stuck hExtractNe' with
    ⟨hHiTy, hLoTy, hApplyNe⟩
  let widthTerm := __eo_add (__eo_add hi (__eo_neg lo)) (Term.Numeral 1)
  let inner :=
    __eo_requires (__eo_gt (Term.Numeral w) hi) (Term.Boolean true)
      (__eo_requires (__eo_gt widthTerm (Term.Numeral 0))
        (Term.Boolean true) widthTerm)
  have hBodyNe :
      __eo_requires (__eo_gt lo (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) inner ≠
        Term.Stuck := by
    intro hBody
    apply hApplyNe
    simp [widthTerm, inner, hBody, __eo_mk_apply]
  have hLoGuard :
      __eo_gt lo (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hBodyNe
  rcases numeral_nonneg_of_gt_neg_one lo hLoGuard with ⟨l, hLo, hl0⟩
  subst lo
  have hOuterReduce :
      __eo_requires
          (__eo_gt (Term.Numeral l) (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) inner = inner := by
    simp [__eo_requires, hLoGuard, native_ite, native_teq, native_not]
  have hInnerNe : inner ≠ Term.Stuck := by
    simpa [hOuterReduce] using hBodyNe
  have hHiGuard :
      __eo_gt (Term.Numeral w) hi = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hInnerNe
  cases hi <;> simp [__eo_gt] at hHiGuard
  case Numeral h =>
    have hhw : native_zlt h w = true := by simpa [__eo_gt] using hHiGuard
    have hHiGuardNeStuck :
        __eo_gt (Term.Numeral w) (Term.Numeral h) ≠ Term.Stuck := by
      simp [__eo_gt]
    have hInnerReduce :
        inner =
          __eo_requires (__eo_gt widthTerm (Term.Numeral 0))
            (Term.Boolean true) widthTerm := by
      simp [inner, __eo_requires, __eo_gt, hhw, hHiGuardNeStuck, native_ite,
        native_teq, native_not]
    have hWidthNe :
        __eo_requires (__eo_gt widthTerm (Term.Numeral 0))
            (Term.Boolean true) widthTerm ≠
          Term.Stuck := by
      simpa [hInnerReduce] using hInnerNe
    have hWidthGuard :
        __eo_gt widthTerm (Term.Numeral 0) =
          Term.Boolean true :=
      support_eo_requires_cond_eq_of_non_stuck hWidthNe
    have hWidthEval :
        widthTerm =
          Term.Numeral (native_zplus (native_zplus h 1) (native_zneg l)) := by
      simp [widthTerm, __eo_add, __eo_neg, SmtEval.native_zplus,
        SmtEval.native_zneg, Int.add_assoc, Int.add_comm, Int.add_left_comm]
    have hWidthPos :
        native_zlt 0 (native_zplus (native_zplus h 1) (native_zneg l)) = true := by
      rw [hWidthEval] at hWidthGuard
      simpa [__eo_gt] using hWidthGuard
    exact ⟨w, h, l, hXTy, rfl, rfl, hw0, hl0, hhw,
      hWidthPos, hXSmtTy⟩

theorem natpow2_eq (w : Nat) :
    native_int_pow2 (↑w : Int) = (2 : Int) ^ w := by
  have hwnn : ¬ ((↑w : Int) < 0) := by omega
  unfold native_int_pow2 native_zexp_total
  rw [if_neg hwnn, Int.toNat_natCast]

theorem ofInt_toNat_canonical (w : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ w) :
    (BitVec.ofInt w p).toNat = p.toNat := by
  rw [BitVec.toNat_ofInt]
  congr 1
  exact Int.emod_eq_of_lt hp0 (by exact_mod_cast hp1)

theorem bitvec_ofInt_natCast_toNat {w : Nat} (x : BitVec w) :
    BitVec.ofInt w (↑x.toNat : Int) = x := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp

private theorem bvnot_val_bitvec (W : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_model_eval_bvnot (SmtValue.Binary ↑W p) =
      SmtValue.Binary ↑W ↑(~~~(BitVec.ofInt W p)).toNat := by
  have hPowPos : (0 : Int) < (2 : Int) ^ W := by
    exact_mod_cast Nat.two_pow_pos W
  have hRawNonneg : 0 ≤ (2 : Int) ^ W - (p + 1) := by omega
  have hRawLt : (2 : Int) ^ W - (p + 1) < (2 : Int) ^ W := by omega
  have hToNat := ofInt_toNat_canonical W p hp0 hp1
  simp only [__smtx_model_eval_bvnot, native_mod_total, native_binary_not,
    native_zplus, native_zneg]
  rw [natpow2_eq W]
  rw [show (2 : Int) ^ W + -(p + 1) = (2 : Int) ^ W - (p + 1) by omega]
  rw [Int.emod_eq_of_lt hRawNonneg hRawLt]
  congr 2
  simp only [BitVec.toNat_not, hToNat]
  have hpCast : (↑p.toNat : Int) = p := Int.toNat_of_nonneg hp0
  have hPowCast : (↑(2 ^ W : Nat) : Int) = (2 : Int) ^ W := by norm_cast
  have hpNat : p.toNat < 2 ^ W := by
    have hpNatInt : (↑p.toNat : Int) < ↑(2 ^ W : Nat) := by
      rw [hpCast, hPowCast]
      exact hp1
    exact_mod_cast hpNatInt
  have hNatSub : 2 ^ W - 1 - p.toNat = 2 ^ W - (p.toNat + 1) := by
    omega
  calc
    (2 : Int) ^ W - (p + 1) =
        ↑(2 ^ W : Nat) - (↑p.toNat + 1) := by rw [hPowCast, hpCast]
    _ = ↑(2 ^ W : Nat) - ↑(p.toNat + 1) := by norm_cast
    _ = ↑(2 ^ W - (p.toNat + 1) : Nat) :=
      (Int.ofNat_sub (by omega : p.toNat + 1 ≤ 2 ^ W)).symm
    _ = ↑(2 ^ W - 1 - p.toNat : Nat) := by rw [hNatSub]

private theorem extractLsb'_not_of_le {x : BitVec w} {start len : Nat}
    (h : start + len ≤ w) :
    (~~~x).extractLsb' start len = ~~~(x.extractLsb' start len) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getElem_not hi,
    BitVec.getElem_extractLsb' hi, BitVec.getLsbD_not]
  simp [show start + i < w by omega]

private theorem extractLsb'_extractLsb'_general
    {x : BitVec w} {outerStart outerLen innerStart innerLen : Nat}
    (h : innerStart + innerLen ≤ outerLen) :
    (x.extractLsb' outerStart outerLen).extractLsb' innerStart innerLen =
      x.extractLsb' (outerStart + innerStart) innerLen := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_extractLsb' hi]
  have hInner : innerStart + i < outerLen := by omega
  rw [BitVec.getLsbD_eq_getElem hInner,
    BitVec.getElem_extractLsb' hInner, BitVec.getElem_extractLsb' hi]
  congr 1
  omega

theorem extract_val_bitvec_start_len
    (W L D : Nat) (p h l : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hl : l = ↑L) (hd : h + 1 + -l = ↑D) :
    __smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral l)
        (SmtValue.Binary ↑W p) =
      SmtValue.Binary ↑D
        ↑((BitVec.ofInt W p).extractLsb' L D).toNat := by
  obtain ⟨N, rfl⟩ : ∃ N : Nat, p = (↑N : Int) :=
    ⟨p.toNat, (Int.toNat_of_nonneg hp0).symm⟩
  simp only [__smtx_model_eval_extract, native_zplus, native_zneg,
    native_mod_total, native_binary_extract, native_div_total, Int.toNat_natCast]
  rw [hd, hl, natpow2_eq L, natpow2_eq D,
    show ((2 : Int) ^ L) = ((2 ^ L : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ D) = ((2 ^ D : Nat) : Int) by norm_cast]
  have hToNat : (BitVec.ofInt W (↑N : Int)).toNat = N := by
    simpa using ofInt_toNat_canonical W (↑N : Int) hp0 hp1
  have hNLt : N < 2 ^ W := by exact_mod_cast hp1
  congr 2
  norm_cast
  simp [BitVec.extractLsb'_toNat, hToNat, Nat.mod_eq_of_lt hNLt,
    Nat.shiftRight_eq_div_pow]

private theorem extract_not_val
    (W L D : Nat) (p h l : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hl : l = ↑L) (hd : h + 1 + -l = ↑D)
    (hFit : L + D ≤ W) :
    __smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral l)
        (__smtx_model_eval_bvnot (SmtValue.Binary ↑W p)) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral l)
          (SmtValue.Binary ↑W p)) := by
  let x := BitVec.ofInt W p
  have hNot0 : (0 : Int) ≤ (↑(~~~x).toNat : Int) := Int.natCast_nonneg _
  have hNot1 : (↑(~~~x).toNat : Int) < (2 : Int) ^ W := by
    exact_mod_cast (~~~x).isLt
  have hExt0 : (0 : Int) ≤ (↑(x.extractLsb' L D).toNat : Int) :=
    Int.natCast_nonneg _
  have hExt1 :
      (↑(x.extractLsb' L D).toNat : Int) < (2 : Int) ^ D := by
    exact_mod_cast (x.extractLsb' L D).isLt
  rw [bvnot_val_bitvec W p hp0 hp1]
  rw [extract_val_bitvec_start_len W L D _ h l hNot0 hNot1 hl hd]
  rw [extract_val_bitvec_start_len W L D p h l hp0 hp1 hl hd]
  rw [bvnot_val_bitvec D _ hExt0 hExt1]
  congr 2
  have hNotOf : BitVec.ofInt W (↑(~~~x).toNat : Int) = ~~~x := by
    exact bitvec_ofInt_natCast_toNat (~~~x)
  have hExtOf :
      BitVec.ofInt D (↑(x.extractLsb' L D).toNat : Int) =
        x.extractLsb' L D := by
    exact bitvec_ofInt_natCast_toNat (x.extractLsb' L D)
  rw [hNotOf, hExtOf]
  exact congrArg BitVec.toNat (extractLsb'_not_of_le hFit)

theorem native_int_to_nat_roundtrip
    (n : native_Int) (hn0 : native_zleq 0 n = true) :
    native_nat_to_int (native_int_to_nat n) = n := by
  have hn : (0 : Int) ≤ n := by
    simpa [SmtEval.native_zleq] using hn0
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using Int.toNat_of_nonneg hn

theorem native_zleq_of_zlt_true
    (a b : native_Int)
    (h : native_zlt a b = true) :
    native_zleq a b = true := by
  unfold native_zlt at h
  unfold native_zleq
  by_cases hlt : a < b
  · have hle : a ≤ b := Int.le_of_lt hlt
    simp [hle]
  · simp [hlt] at h

theorem eo_typeof_extract_of_context
    (x : Term) (w h l : native_Int) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    native_zleq 0 l = true ->
    native_zlt h w = true ->
    native_zlt 0
        (native_zplus (native_zplus h 1) (native_zneg l)) = true ->
    __eo_typeof
        (bvExtractTerm x (Term.Numeral h) (Term.Numeral l)) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral
          (native_zplus (native_zplus h 1) (native_zneg l))) := by
  intro hXTy hl0 hhw hd0
  have hl : (0 : Int) ≤ l := by
    simpa [SmtEval.native_zleq] using hl0
  have hlNeg : native_zlt (-1 : native_Int) l = true := by
    have : (-1 : Int) < l := by omega
    simpa [SmtEval.native_zlt] using this
  have hdNeg : native_zlt (-1 : native_Int)
      (native_zplus (native_zplus h 1) (native_zneg l)) = true := by
    have : (-1 : Int) <
        native_zplus (native_zplus h 1) (native_zneg l) := by
      have hd : (0 : Int) <
          native_zplus (native_zplus h 1) (native_zneg l) := by
        simpa [SmtEval.native_zlt] using hd0
      omega
    simpa [SmtEval.native_zlt] using this
  have hWidth :
      native_zplus (native_zplus h (native_zneg l)) 1 =
        native_zplus (native_zplus h 1) (native_zneg l) := by
    change h + (-l) + 1 = h + 1 + (-l)
    ac_rfl
  have hdNegRaw : native_zlt (-1 : native_Int)
      (native_zplus (native_zplus h (native_zneg l)) 1) = true := by
    rw [hWidth]
    exact hdNeg
  have hdPosRaw : native_zlt 0
      (native_zplus (native_zplus h (native_zneg l)) 1) = true := by
    rw [hWidth]
    exact hd0
  have hLoGuard :
      __eo_gt (Term.Numeral l) (Term.Numeral (-1 : native_Int)) =
        Term.Boolean true := by simp [__eo_gt, hlNeg]
  have hHiGuard :
      __eo_gt (Term.Numeral w) (Term.Numeral h) = Term.Boolean true := by
    simp [__eo_gt, hhw]
  have hWidthGuard :
      __eo_gt
          (Term.Numeral
            (native_zplus (native_zplus h (native_zneg l)) 1))
          (Term.Numeral 0) = Term.Boolean true := by
    simp [__eo_gt, hdPosRaw]
  change __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral h)
      (Term.UOp UserOp.Int) (Term.Numeral l) (__eo_typeof x) = _
  rw [hXTy]
  simp [__eo_typeof_extract, __eo_requires, __eo_gt, __eo_add, __eo_neg,
    __eo_mk_apply, hLoGuard, hHiGuard, hWidthGuard, hlNeg, hhw,
    hdNeg, native_ite, native_teq, native_not, SmtEval.native_zplus,
    SmtEval.native_zneg, hWidth, hdNegRaw]
  have hRaw : h + -l + 1 = h + 1 + -l := by ac_rfl
  have hRawGuard : native_zlt 0 (h + -l + 1) = true := by
    rw [hRaw]
    exact hd0
  rw [hRawGuard]
  simp [hRaw]

theorem smt_typeof_extract_of_context
    (x : Term) (w h l : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat w) ->
    native_zleq 0 w = true ->
    native_zleq 0 l = true ->
    native_zlt h w = true ->
    native_zlt 0 (native_zplus (native_zplus h 1) (native_zneg l)) = true ->
    __smtx_typeof
        (__eo_to_smt (bvExtractTerm x (Term.Numeral h) (Term.Numeral l))) =
      SmtType.BitVec
        (native_int_to_nat (native_zplus (native_zplus h 1) (native_zneg l))) := by
  intro hXTy hw0 hl0 hhw hd0
  have hRound := native_int_to_nat_roundtrip w hw0
  change __smtx_typeof
      (SmtTerm.extract (SmtTerm.Numeral h) (SmtTerm.Numeral l)
        (__eo_to_smt x)) = _
  rw [typeof_extract_eq, hXTy]
  simp [__smtx_typeof_extract, native_ite, hl0, hhw, hd0, hRound]

private theorem smt_typeof_bvnot_of_bitvec
    (x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x)) =
      SmtType.BitVec w := by
  intro hXTy
  change __smtx_typeof (SmtTerm.bvnot (__eo_to_smt x)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_1, hXTy]

theorem typed_bv_extract_not_term (x hi lo : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractNotTerm x hi lo) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvExtractNotTerm x hi lo) := by
  intro hXTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvExtractNotLhs x hi lo))
      (__eo_typeof (bvExtractNotRhs x hi lo)) = Term.Bool at hResultTy
  have hRhsNe :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hExtractNe : __eo_typeof (bvExtractTerm x hi lo) ≠ Term.Stuck := by
    intro hExt
    apply hRhsNe
    change __eo_typeof_bvnot (__eo_typeof (bvExtractTerm x hi lo)) = Term.Stuck
    rw [hExt]
    rfl
  rcases bv_extract_context_of_non_stuck x hi lo hXTrans hExtractNe with
    ⟨w, h, l, _hXTy, rfl, rfl, hw0, hl0, hhw, hd0, hXSmtTy⟩
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  have hExtTy :
      __smtx_typeof
          (__eo_to_smt (bvExtractTerm x (Term.Numeral h) (Term.Numeral l))) =
        SmtType.BitVec (native_int_to_nat d) :=
    smt_typeof_extract_of_context x w h l hXSmtTy hw0 hl0 hhw hd0
  have hNotXTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x)) =
        SmtType.BitVec (native_int_to_nat w) :=
    smt_typeof_bvnot_of_bitvec x _ hXSmtTy
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractNotLhs x (Term.Numeral h) (Term.Numeral l))) =
        SmtType.BitVec (native_int_to_nat d) := by
    exact smt_typeof_extract_of_context
      (Term.Apply (Term.UOp UserOp.bvnot) x) w h l hNotXTy hw0 hl0 hhw hd0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractNotRhs x (Term.Numeral h) (Term.Numeral l))) =
        SmtType.BitVec (native_int_to_nat d) := by
    exact smt_typeof_bvnot_of_bitvec _ _ hExtTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; simp)

theorem smt_eval_binary_of_smt_type_bitvec
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm) (w : native_Nat) :
    __smtx_typeof t = SmtType.BitVec w ->
    ∃ p, __smtx_model_eval M t = SmtValue.Binary (native_nat_to_int w) p ∧
      native_zeq p
        (native_mod_total p (native_int_pow2 (native_nat_to_int w))) = true := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.BitVec w := by
    simpa [hTy] using smt_model_eval_preserves_type_of_non_none M hM t hNN
  rcases bitvec_value_canonical hValTy with ⟨p, hEval⟩
  have hCan :
      native_zeq p
          (native_mod_total p (native_int_pow2 (native_nat_to_int w))) = true :=
    bitvec_payload_canonical (by simpa [hEval] using hValTy)
  exact ⟨p, hEval, hCan⟩

theorem eval_extract_term
    (M : SmtModel) (x : Term) (h l : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm x (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral l)
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M
      (SmtTerm.extract (SmtTerm.Numeral h) (SmtTerm.Numeral l)
        (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  simp [__smtx_model_eval]

private theorem eval_bvnot_term (M : SmtModel) (x : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x)) =
      __smtx_model_eval_bvnot (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_extract_not
    (M : SmtModel) (hM : model_wf M) (x hi lo : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractNotTerm x hi lo) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvExtractNotLhs x hi lo)) =
      __smtx_model_eval M (__eo_to_smt (bvExtractNotRhs x hi lo)) := by
  intro hXTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvExtractNotLhs x hi lo))
      (__eo_typeof (bvExtractNotRhs x hi lo)) = Term.Bool at hResultTy
  have hRhsNe :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hExtractNe : __eo_typeof (bvExtractTerm x hi lo) ≠ Term.Stuck := by
    intro hExt
    apply hRhsNe
    change __eo_typeof_bvnot (__eo_typeof (bvExtractTerm x hi lo)) = Term.Stuck
    rw [hExt]
    rfl
  rcases bv_extract_context_of_non_stuck x hi lo hXTrans hExtractNe with
    ⟨w, h, l, _hXTy, rfl, rfl, hw0, hl0, hhw, hd0, hXSmtTy⟩
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  let W := native_int_to_nat w
  let L := native_int_to_nat l
  let D := native_int_to_nat d
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hLRound : (↑L : Int) = l := by
    simpa [L, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip l hl0
  have hdNonneg : native_zleq 0 d = true :=
    native_zleq_of_zlt_true _ _ hd0
  have hDRound : (↑D : Int) = d := by
    simpa [D, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip d hdNonneg
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with ⟨p, hXEval, hCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary (↑W) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval
  have hWidth0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int, Smtm.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] using hRange.2
  have hhwInt : h < w := by simpa [SmtEval.native_zlt] using hhw
  have hwInt : (0 : Int) ≤ w := by simpa [SmtEval.native_zleq] using hw0
  have hlInt : (0 : Int) ≤ l := by simpa [SmtEval.native_zleq] using hl0
  have hdInt : (0 : Int) ≤ d := by simpa [SmtEval.native_zleq] using hdNonneg
  have hFitEq : l + d = h + 1 := by
    simp [d, SmtEval.native_zplus, SmtEval.native_zneg, Int.add_assoc,
      Int.add_comm, Int.add_left_comm]
    omega
  have hFitZ : l + d ≤ w := by
    rw [hFitEq]
    exact Int.add_one_le_iff.mpr hhwInt
  have hFitInt : (↑L : Int) + (↑D : Int) ≤ (↑W : Int) := by
    rw [hLRound, hDRound, hWRound]
    exact hFitZ
  have hFit : L + D ≤ W := by
    exact_mod_cast hFitInt
  have hdCast : h + 1 + -l = (↑D : Int) := by
    rw [hDRound]
    rfl
  unfold bvExtractNotLhs bvExtractNotRhs
  rw [eval_extract_term, eval_bvnot_term, eval_bvnot_term, eval_extract_term,
    hXEval']
  exact extract_not_val W L D p h l hp0 hp1 hLRound.symm hdCast hFit

theorem facts_bv_extract_not_term
    (M : SmtModel) (hM : model_wf M) (x hi lo : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractNotTerm x hi lo) = Term.Bool ->
    eo_interprets M (bvExtractNotTerm x hi lo) true := by
  intro hXTrans hResultTy
  have hBool := typed_bv_extract_not_term x hi lo hXTrans hResultTy
  unfold bvExtractNotTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractNotTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvExtractNotLhs x hi lo)))
      (__smtx_model_eval M (__eo_to_smt (bvExtractNotRhs x hi lo)))
    rw [eval_bv_extract_not M hM x hi lo hXTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvExtractNotProgram (x i j : Term) : Term :=
  __eo_prog_bv_extract_not x i j

private theorem bvExtractNotProgram_eq_term_of_ne_stuck
    (x i j : Term) :
    x ≠ Term.Stuck -> i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractNotProgram x i j = bvExtractNotTerm x j i := by
  intro hXNe hINe hJNe
  cases x <;> cases i <;> cases j <;>
    simp [bvExtractNotProgram, bvExtractNotTerm, bvExtractNotLhs,
      bvExtractNotRhs, bvExtractTerm, __eo_prog_bv_extract_not]
      at hXNe hINe hJNe ⊢

theorem bvExtractNotProgram_eq_term_of_type_bool
    (x i j : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    __eo_typeof (bvExtractNotProgram x i j) = Term.Bool ->
    bvExtractNotProgram x i j = bvExtractNotTerm x j i := by
  intro hXTrans hITrans hJTrans _hTy
  exact bvExtractNotProgram_eq_term_of_ne_stuck x i j
    (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
    (RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans)
    (RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans)

theorem typed_bv_extract_not_program (x i j : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    __eo_typeof (bvExtractNotProgram x i j) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvExtractNotProgram x i j) := by
  intro hXTrans hITrans hJTrans hResultTy
  have hEq := bvExtractNotProgram_eq_term_of_type_bool
    x i j hXTrans hITrans hJTrans hResultTy
  have hTermTy : __eo_typeof (bvExtractNotTerm x j i) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_extract_not_term x j i hXTrans hTermTy

theorem facts_bv_extract_not_program
    (M : SmtModel) (hM : model_wf M) (x i j : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    __eo_typeof (bvExtractNotProgram x i j) = Term.Bool ->
    eo_interprets M (bvExtractNotProgram x i j) true := by
  intro hXTrans hITrans hJTrans hResultTy
  have hEq := bvExtractNotProgram_eq_term_of_type_bool
    x i j hXTrans hITrans hJTrans hResultTy
  have hTermTy : __eo_typeof (bvExtractNotTerm x j i) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_extract_not_term M hM x j i hXTrans hTermTy

def bvExtractExtractLhs (x i j k l : Term) : Term :=
  bvExtractTerm (bvExtractTerm x j i) l k

def bvExtractExtractRhs (x ll kk : Term) : Term :=
  bvExtractTerm x ll kk

def bvExtractExtractTerm (x i j k l ll kk : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractExtractLhs x i j k l)) (bvExtractExtractRhs x ll kk)

def bvExtractExtractPrem (base offset total : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) total)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) base)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) offset) (Term.Numeral 0)))

private theorem extract_extract_val
    (W I DI K DO : Nat) (p j i l k ll kk : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hi : i = ↑I) (hDI : j + 1 + -i = ↑DI)
    (hk : k = ↑K) (hDO : l + 1 + -k = ↑DO)
    (hkk : kk = ↑(I + K)) (hRhsWidth : ll + 1 + -kk = ↑DO)
    (hFit : K + DO ≤ DI) :
    __smtx_model_eval_extract (SmtValue.Numeral l) (SmtValue.Numeral k)
        (__smtx_model_eval_extract (SmtValue.Numeral j) (SmtValue.Numeral i)
          (SmtValue.Binary ↑W p)) =
      __smtx_model_eval_extract (SmtValue.Numeral ll) (SmtValue.Numeral kk)
        (SmtValue.Binary ↑W p) := by
  let x := BitVec.ofInt W p
  let inner := x.extractLsb' I DI
  have hInner0 : (0 : Int) ≤ (↑inner.toNat : Int) := Int.natCast_nonneg _
  have hInner1 : (↑inner.toNat : Int) < (2 : Int) ^ DI := by
    exact_mod_cast inner.isLt
  rw [extract_val_bitvec_start_len W I DI p j i hp0 hp1 hi hDI]
  rw [extract_val_bitvec_start_len DI K DO (↑inner.toNat : Int) l k
    hInner0 hInner1 hk hDO]
  rw [extract_val_bitvec_start_len W (I + K) DO p ll kk
    hp0 hp1 hkk hRhsWidth]
  congr 2
  have hInnerOf : BitVec.ofInt DI (↑inner.toNat : Int) = inner :=
    bitvec_ofInt_natCast_toNat inner
  rw [hInnerOf]
  exact congrArg BitVec.toNat
    (extractLsb'_extractLsb'_general (x := x) hFit)

private theorem bv_extract_extract_prem_numeric
    (M : SmtModel) (base offset total : native_Int) :
    eo_interprets M
        (bvExtractExtractPrem (Term.Numeral base) (Term.Numeral offset)
          (Term.Numeral total)) true ->
    total = base + offset := by
  intro hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq (SmtTerm.Numeral total)
            (SmtTerm.plus (SmtTerm.Numeral base)
              (SmtTerm.plus (SmtTerm.Numeral offset) (SmtTerm.Numeral 0)))) =
        SmtValue.Boolean true at hEval
      simp [__smtx_model_eval, __smtx_model_eval_eq,
        __smtx_model_eval_plus, native_veq, SmtEval.native_zplus] at hEval
      exact hEval

theorem nonneg_int_eq_of_toNat_eq
    (a b : native_Int) :
    native_zleq 0 a = true ->
    native_zleq 0 b = true ->
    native_int_to_nat a = native_int_to_nat b ->
    a = b := by
  intro ha0 hb0 hNat
  have haRound := native_int_to_nat_roundtrip a ha0
  have hbRound := native_int_to_nat_roundtrip b hb0
  calc
    a = native_nat_to_int (native_int_to_nat a) := haRound.symm
    _ = native_nat_to_int (native_int_to_nat b) := by rw [hNat]
    _ = b := hbRound

theorem bv_extract_extract_context
    (x i j k l ll kk : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractExtractTerm x i j k l ll kk) = Term.Bool ->
    ∃ w jn inn ln kn lln kkn,
      i = Term.Numeral inn ∧ j = Term.Numeral jn ∧
      k = Term.Numeral kn ∧ l = Term.Numeral ln ∧
      ll = Term.Numeral lln ∧ kk = Term.Numeral kkn ∧
      native_zleq 0 w = true ∧ native_zleq 0 inn = true ∧
      native_zlt jn w = true ∧
      native_zlt 0 (native_zplus (native_zplus jn 1) (native_zneg inn)) = true ∧
      native_zleq 0 kn = true ∧
      native_zlt ln
        (native_zplus (native_zplus jn 1) (native_zneg inn)) = true ∧
      native_zlt 0 (native_zplus (native_zplus ln 1) (native_zneg kn)) = true ∧
      native_zleq 0 kkn = true ∧ native_zlt lln w = true ∧
      native_zlt 0 (native_zplus (native_zplus lln 1) (native_zneg kkn)) = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvExtractExtractLhs x i j k l))
      (__eo_typeof (bvExtractExtractRhs x ll kk)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hLhsNe' :
      __eo_typeof_extract (__eo_typeof l) l (__eo_typeof k) k
          (__eo_typeof (bvExtractTerm x j i)) ≠ Term.Stuck := by
    simp only [bvExtractExtractLhs, bvExtractTerm] at hLhsNe
    exact hLhsNe
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck hLhsNe' with
    ⟨innerWidth, hInnerType⟩
  have hInnerNe : __eo_typeof (bvExtractTerm x j i) ≠ Term.Stuck := by
    intro hInner
    rw [hInner] at hInnerType
    cases hInnerType
  rcases bv_extract_context_of_non_stuck x j i hXTrans hInnerNe with
    ⟨w, jn, inn, hXTy, hJ, hI, hw0, hi0, hjw, hDI0, hXSmtTy⟩
  let dInner := native_zplus (native_zplus jn 1) (native_zneg inn)
  have hInnerSmtTy :
      __smtx_typeof (__eo_to_smt (bvExtractTerm x j i)) =
        SmtType.BitVec (native_int_to_nat dInner) := by
    rw [hJ, hI]
    exact smt_typeof_extract_of_context x w jn inn
      hXSmtTy hw0 hi0 hjw hDI0
  have hInnerTrans : RuleProofs.eo_has_smt_translation (bvExtractTerm x j i) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hInnerSmtTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck (bvExtractTerm x j i) l k
      hInnerTrans hLhsNe with
    ⟨wOuter, ln, kn, _hInnerTy, hL, hK, hwOuter0, hk0, hlOuter,
      hDO0, hInnerSmtTyOuter⟩
  have hDInnerNat :
      native_int_to_nat dInner = native_int_to_nat wOuter := by
    rw [hInnerSmtTy] at hInnerSmtTyOuter
    simpa using hInnerSmtTyOuter
  have hDI0Nonneg : native_zleq 0 dInner = true :=
    native_zleq_of_zlt_true _ _ hDI0
  have hwOuterEq : wOuter = dInner :=
    nonneg_int_eq_of_toNat_eq wOuter dInner hwOuter0 hDI0Nonneg hDInnerNat.symm
  rcases bv_extract_context_of_non_stuck x ll kk hXTrans hRhsNe with
    ⟨wRhs, lln, kkn, _hXTyRhs, hLl, hKk, hwRhs0, hkk0, hllRhs,
      hDRhs0, hXSmtTyRhs⟩
  have hWidthNat : native_int_to_nat w = native_int_to_nat wRhs := by
    rw [hXSmtTy] at hXSmtTyRhs
    simpa using hXSmtTyRhs
  have hwRhsEq : wRhs = w :=
    nonneg_int_eq_of_toNat_eq wRhs w hwRhs0 hw0 hWidthNat.symm
  rw [hwOuterEq] at hlOuter
  rw [hwRhsEq] at hllRhs
  exact ⟨w, jn, inn, ln, kn, lln, kkn,
    hI, hJ, hK, hL, hLl, hKk, hw0, hi0, hjw, hDI0, hk0,
    hlOuter, hDO0, hkk0, hllRhs, hDRhs0, hXSmtTy⟩

theorem typed_bv_extract_extract_term (x i j k l ll kk : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractExtractTerm x i j k l ll kk) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvExtractExtractTerm x i j k l ll kk) := by
  intro hXTrans hResultTy
  rcases bv_extract_extract_context x i j k l ll kk hXTrans hResultTy with
    ⟨w, jn, inn, ln, kn, lln, kkn, rfl, rfl, rfl, rfl, rfl, rfl,
      hw0, hi0, hjw, hDI0, hk0, hlDI, hDO0, hkk0, hllw, hDRhs0,
      hXSmtTy⟩
  let dInner := native_zplus (native_zplus jn 1) (native_zneg inn)
  let dOuter := native_zplus (native_zplus ln 1) (native_zneg kn)
  let dRhs := native_zplus (native_zplus lln 1) (native_zneg kkn)
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral jn) (Term.Numeral inn))) =
        SmtType.BitVec (native_int_to_nat dInner) :=
    smt_typeof_extract_of_context x w jn inn
      hXSmtTy hw0 hi0 hjw hDI0
  have hDI0Nonneg : native_zleq 0 dInner = true :=
    native_zleq_of_zlt_true _ _ hDI0
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractExtractLhs x (Term.Numeral inn) (Term.Numeral jn)
              (Term.Numeral kn) (Term.Numeral ln))) =
        SmtType.BitVec (native_int_to_nat dOuter) := by
    exact smt_typeof_extract_of_context
      (bvExtractTerm x (Term.Numeral jn) (Term.Numeral inn))
      dInner ln kn hInnerTy hDI0Nonneg hk0 hlDI hDO0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractExtractRhs x (Term.Numeral lln)
              (Term.Numeral kkn))) =
        SmtType.BitVec (native_int_to_nat dRhs) := by
    exact smt_typeof_extract_of_context x w lln kkn
      hXSmtTy hw0 hkk0 hllw hDRhs0
  let lhs := bvExtractExtractLhs x (Term.Numeral inn) (Term.Numeral jn)
    (Term.Numeral kn) (Term.Numeral ln)
  let rhs := bvExtractExtractRhs x (Term.Numeral lln) (Term.Numeral kkn)
  have hLhsTrans : RuleProofs.eo_has_smt_translation lhs := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof (__eo_to_smt lhs) =
        SmtType.BitVec (native_int_to_nat dOuter) by simpa [lhs] using hLhsTy]
    intro h
    cases h
  have hRhsTrans : RuleProofs.eo_has_smt_translation rhs := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof (__eo_to_smt rhs) =
        SmtType.BitVec (native_int_to_nat dRhs) by simpa [rhs] using hRhsTy]
    intro h
    cases h
  have hEOTypeEq : __eo_typeof lhs = __eo_typeof rhs := by
    apply RuleProofs.eo_typeof_eq_bool_operands_eq
    simp only [bvExtractExtractTerm, lhs, rhs] at hResultTy
    exact hResultTy
  have hLhsBridge :
      __smtx_typeof (__eo_to_smt lhs) = __eo_to_smt_type (__eo_typeof lhs) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      lhs (__eo_typeof lhs) (__eo_to_smt lhs) rfl hLhsTrans rfl
  have hRhsBridge :
      __smtx_typeof (__eo_to_smt rhs) = __eo_to_smt_type (__eo_typeof rhs) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      rhs (__eo_typeof rhs) (__eo_to_smt rhs) rfl hRhsTrans rfl
  have hLhsTy' :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.BitVec (native_int_to_nat dOuter) := by
    simpa [lhs] using hLhsTy
  unfold bvExtractExtractTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsBridge, hRhsBridge, hEOTypeEq])
    (by rw [hLhsTy']; simp)

private theorem eval_bv_extract_extract
    (M : SmtModel) (hM : model_wf M)
    (x i j k l ll kk : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractExtractTerm x i j k l ll kk) = Term.Bool ->
    eo_interprets M (bvExtractExtractPrem i l ll) true ->
    eo_interprets M (bvExtractExtractPrem i k kk) true ->
    __smtx_model_eval M (__eo_to_smt (bvExtractExtractLhs x i j k l)) =
      __smtx_model_eval M (__eo_to_smt (bvExtractExtractRhs x ll kk)) := by
  intro hXTrans hResultTy hPremLl hPremKk
  rcases bv_extract_extract_context x i j k l ll kk hXTrans hResultTy with
    ⟨w, jn, inn, ln, kn, lln, kkn, rfl, rfl, rfl, rfl, rfl, rfl,
      hw0, hi0, hjw, hDI0, hk0, hlDI, hDO0, hkk0, hllw, hDRhs0,
      hXSmtTy⟩
  have hLlEq : lln = inn + ln :=
    bv_extract_extract_prem_numeric M inn ln lln hPremLl
  have hKkEq : kkn = inn + kn :=
    bv_extract_extract_prem_numeric M inn kn kkn hPremKk
  let dInner := native_zplus (native_zplus jn 1) (native_zneg inn)
  let dOuter := native_zplus (native_zplus ln 1) (native_zneg kn)
  let W := native_int_to_nat w
  let I := native_int_to_nat inn
  let DI := native_int_to_nat dInner
  let K := native_int_to_nat kn
  let DO := native_int_to_nat dOuter
  have hDI0Nonneg : native_zleq 0 dInner = true :=
    native_zleq_of_zlt_true _ _ hDI0
  have hDO0Nonneg : native_zleq 0 dOuter = true :=
    native_zleq_of_zlt_true _ _ hDO0
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hIRound : (↑I : Int) = inn := by
    simpa [I, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip inn hi0
  have hDIRound : (↑DI : Int) = dInner := by
    simpa [DI, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip dInner hDI0Nonneg
  have hKRound : (↑K : Int) = kn := by
    simpa [K, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip kn hk0
  have hDORound : (↑DO : Int) = dOuter := by
    simpa [DO, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip dOuter hDO0Nonneg
  have hDICast : jn + 1 + -inn = (↑DI : Int) := by
    rw [hDIRound]
    rfl
  have hDOCast : ln + 1 + -kn = (↑DO : Int) := by
    rw [hDORound]
    rfl
  have hIKCast : (↑(I + K) : Int) = (↑I : Int) + (↑K : Int) := by
    norm_cast
  have hKkCast : kkn = (↑(I + K) : Int) := by
    calc
      kkn = inn + kn := hKkEq
      _ = (↑I : Int) + (↑K : Int) := by rw [hIRound, hKRound]
      _ = (↑(I + K) : Int) := hIKCast.symm
  have hRhsWidthZ : lln + 1 + -kkn = dOuter := by
    rw [hLlEq, hKkEq]
    simp [dOuter, SmtEval.native_zplus, SmtEval.native_zneg,
      Int.neg_add, Int.add_assoc, Int.add_comm, Int.add_left_comm]
    rw [show inn + (ln + (-inn + (-kn + 1))) =
        (inn + -inn) + (ln + (-kn + 1)) by ac_rfl]
    have hCancel : inn + -inn = 0 := by
      simpa using (Int.add_neg_cancel_right (0 : Int) inn)
    rw [hCancel, Int.zero_add]
  have hRhsWidthCast : lln + 1 + -kkn = (↑DO : Int) :=
    hRhsWidthZ.trans hDORound.symm
  have hlDIInt : ln < dInner := by simpa [SmtEval.native_zlt] using hlDI
  have hOuterFitEq : kn + dOuter = ln + 1 := by
    simp [dOuter, SmtEval.native_zplus, SmtEval.native_zneg,
      Int.add_assoc, Int.add_comm, Int.add_left_comm]
    omega
  have hOuterFitZ : kn + dOuter ≤ dInner := by
    rw [hOuterFitEq]
    exact Int.add_one_le_iff.mpr hlDIInt
  have hOuterFitInt : (↑K : Int) + (↑DO : Int) ≤ (↑DI : Int) := by
    rw [hKRound, hDORound, hDIRound]
    exact hOuterFitZ
  have hOuterFit : K + DO ≤ DI := by exact_mod_cast hOuterFitInt
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with ⟨p, hXEval, hCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary (↑W) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval
  have hWidth0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int, Smtm.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] using
      hRange.2
  unfold bvExtractExtractLhs bvExtractExtractRhs
  rw [eval_extract_term M
      (bvExtractTerm x (Term.Numeral jn) (Term.Numeral inn)) ln kn,
    eval_extract_term M x jn inn, eval_extract_term M x lln kkn, hXEval']
  exact extract_extract_val W I DI K DO p jn inn ln kn lln kkn
    hp0 hp1 hIRound.symm hDICast hKRound.symm hDOCast
    hKkCast hRhsWidthCast hOuterFit

theorem facts_bv_extract_extract_term
    (M : SmtModel) (hM : model_wf M)
    (x i j k l ll kk : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractExtractTerm x i j k l ll kk) = Term.Bool ->
    eo_interprets M (bvExtractExtractPrem i l ll) true ->
    eo_interprets M (bvExtractExtractPrem i k kk) true ->
    eo_interprets M (bvExtractExtractTerm x i j k l ll kk) true := by
  intro hXTrans hResultTy hPremLl hPremKk
  have hBool := typed_bv_extract_extract_term
    x i j k l ll kk hXTrans hResultTy
  unfold bvExtractExtractTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractExtractTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvExtractExtractLhs x i j k l)))
      (__smtx_model_eval M (__eo_to_smt (bvExtractExtractRhs x ll kk)))
    rw [eval_bv_extract_extract M hM x i j k l ll kk
      hXTrans hResultTy hPremLl hPremKk]
    exact RuleProofs.smt_value_rel_refl _

def bvExtractExtractProgram
    (x i j k l ll kk : Term) (pLl pKk : Proof) : Term :=
  __eo_prog_bv_extract_extract x i j k l ll kk pLl pKk

theorem bv_extract_support_requires_guard
    {guard body : Term} :
    __eo_requires guard (Term.Boolean true) body ≠ Term.Stuck ->
    guard = Term.Boolean true := by
  intro hReq
  by_cases hGuard : guard = Term.Boolean true
  · exact hGuard
  · have hStuck :
        __eo_requires guard (Term.Boolean true) body = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hGuard]
    exact False.elim (hReq hStuck)

theorem bv_extract_support_and_true {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢

theorem bv_extract_support_eq_true {a b : Term} :
    __eo_eq a b = Term.Boolean true -> a = b := by
  intro h
  by_cases ha : a = Term.Stuck
  · subst a
    simp [__eo_eq] at h
  · by_cases hb : b = Term.Stuck
    · subst b
      simp [__eo_eq] at h
    · have hba : b = a := by
        simpa [__eo_eq, ha, hb, native_teq] using h
      exact hba.symm

private theorem bv_extract_extract_guard_refs
    {i k l ll kk iRef1 lRef llRef iRef2 kRef kkRef body : Term} :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and (__eo_eq ll llRef) (__eo_eq i iRef1))
                (__eo_eq l lRef))
              (__eo_eq kk kkRef))
            (__eo_eq i iRef2))
          (__eo_eq k kRef))
        (Term.Boolean true) body ≠ Term.Stuck ->
    llRef = ll ∧ iRef1 = i ∧ lRef = l ∧
      kkRef = kk ∧ iRef2 = i ∧ kRef = k := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hG1, hK⟩
  rcases bv_extract_support_and_true hG1 with ⟨hG2, hI2⟩
  rcases bv_extract_support_and_true hG2 with ⟨hG3, hKk⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG4, hL⟩
  rcases bv_extract_support_and_true hG4 with ⟨hLl, hI1⟩
  exact ⟨(bv_extract_support_eq_true hLl).symm,
    (bv_extract_support_eq_true hI1).symm,
    (bv_extract_support_eq_true hL).symm,
    (bv_extract_support_eq_true hKk).symm,
    (bv_extract_support_eq_true hI2).symm,
    (bv_extract_support_eq_true hK).symm⟩

private theorem bv_extract_extract_premise_shape
    (x i j k l ll kk P1 P2 : Term) :
    x ≠ Term.Stuck -> i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    k ≠ Term.Stuck -> l ≠ Term.Stuck -> ll ≠ Term.Stuck ->
    kk ≠ Term.Stuck ->
    bvExtractExtractProgram x i j k l ll kk (Proof.pf P1) (Proof.pf P2) ≠
      Term.Stuck ->
    ∃ llRef iRef1 lRef kkRef iRef2 kRef,
      P1 = bvExtractExtractPrem iRef1 lRef llRef ∧
      P2 = bvExtractExtractPrem iRef2 kRef kkRef := by
  intro hX hI hJ hK hL hLl hKk hProg
  by_cases hShape :
      ∃ llRef iRef1 lRef kkRef iRef2 kRef,
        P1 = bvExtractExtractPrem iRef1 lRef llRef ∧
        P2 = bvExtractExtractPrem iRef2 kRef kkRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_extract.eq_9 x i j k l ll kk
      (Proof.pf P1) (Proof.pf P2) hX hI hJ hK hL hLl hKk (by
        intro llRef iRef1 lRef kkRef iRef2 kRef hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨llRef, iRef1, lRef, kkRef, iRef2, kRef, rfl, rfl⟩)

private theorem bv_extract_extract_program_canonical
    (x i j k l ll kk : Term) :
    x ≠ Term.Stuck -> i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    k ≠ Term.Stuck -> l ≠ Term.Stuck -> ll ≠ Term.Stuck ->
    kk ≠ Term.Stuck ->
    bvExtractExtractProgram x i j k l ll kk
        (Proof.pf (bvExtractExtractPrem i l ll))
        (Proof.pf (bvExtractExtractPrem i k kk)) =
      bvExtractExtractTerm x i j k l ll kk := by
  intro hX hI hJ hK hL hLl hKk
  unfold bvExtractExtractProgram bvExtractExtractPrem
  rw [__eo_prog_bv_extract_extract.eq_8 x i j k l ll kk
    ll i l kk i k hX hI hJ hK hL hLl hKk]
  simp [bvExtractExtractProgram, bvExtractExtractPrem, bvExtractExtractTerm,
    bvExtractExtractLhs, bvExtractExtractRhs, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hI, hK, hL, hLl, hKk]

theorem bvExtractExtractProgram_normalize
    (x i j k l ll kk P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation l ->
    RuleProofs.eo_has_smt_translation ll ->
    RuleProofs.eo_has_smt_translation kk ->
    bvExtractExtractProgram x i j k l ll kk (Proof.pf P1) (Proof.pf P2) ≠
      Term.Stuck ->
    P1 = bvExtractExtractPrem i l ll ∧
      P2 = bvExtractExtractPrem i k kk ∧
      bvExtractExtractProgram x i j k l ll kk (Proof.pf P1) (Proof.pf P2) =
        bvExtractExtractTerm x i j k l ll kk := by
  intro hXTrans hITrans hJTrans hKTrans hLTrans hLlTrans hKkTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hK := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  have hL := RuleProofs.term_ne_stuck_of_has_smt_translation l hLTrans
  have hLl := RuleProofs.term_ne_stuck_of_has_smt_translation ll hLlTrans
  have hKk := RuleProofs.term_ne_stuck_of_has_smt_translation kk hKkTrans
  rcases bv_extract_extract_premise_shape x i j k l ll kk P1 P2
      hX hI hJ hK hL hLl hKk hProg with
    ⟨llRef, iRef1, lRef, kkRef, iRef2, kRef, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvExtractExtractProgram bvExtractExtractPrem at hReq
  rw [__eo_prog_bv_extract_extract.eq_8 x i j k l ll kk
    llRef iRef1 lRef kkRef iRef2 kRef hX hI hJ hK hL hLl hKk] at hReq
  rcases bv_extract_extract_guard_refs hReq with
    ⟨hLlRef, hIRef1, hLRef, hKkRef, hIRef2, hKRef⟩
  subst llRef
  subst iRef1
  subst lRef
  subst kkRef
  subst iRef2
  subst kRef
  have hP1Canon : P1 = bvExtractExtractPrem i l ll := hP1
  have hP2Canon : P2 = bvExtractExtractPrem i k kk := hP2
  refine ⟨hP1Canon, hP2Canon, ?_⟩
  rw [hP1Canon, hP2Canon]
  exact bv_extract_extract_program_canonical x i j k l ll kk
    hX hI hJ hK hL hLl hKk

theorem typed_bv_extract_extract_program
    (x i j k l ll kk P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation l ->
    RuleProofs.eo_has_smt_translation ll ->
    RuleProofs.eo_has_smt_translation kk ->
    __eo_typeof
        (bvExtractExtractProgram x i j k l ll kk (Proof.pf P1) (Proof.pf P2)) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractExtractProgram x i j k l ll kk (Proof.pf P1) (Proof.pf P2)) := by
  intro hXTrans hITrans hJTrans hKTrans hLTrans hLlTrans hKkTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvExtractExtractProgram_normalize x i j k l ll kk P1 P2
      hXTrans hITrans hJTrans hKTrans hLTrans hLlTrans hKkTrans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy : __eo_typeof (bvExtractExtractTerm x i j k l ll kk) =
      Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_extract_extract_term x i j k l ll kk hXTrans hTermTy

theorem facts_bv_extract_extract_program
    (M : SmtModel) (hM : model_wf M)
    (x i j k l ll kk P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation l ->
    RuleProofs.eo_has_smt_translation ll ->
    RuleProofs.eo_has_smt_translation kk ->
    __eo_typeof
        (bvExtractExtractProgram x i j k l ll kk (Proof.pf P1) (Proof.pf P2)) =
      Term.Bool ->
    eo_interprets M P1 true ->
    eo_interprets M P2 true ->
    eo_interprets M
      (bvExtractExtractProgram x i j k l ll kk (Proof.pf P1) (Proof.pf P2))
      true := by
  intro hXTrans hITrans hJTrans hKTrans hLTrans hLlTrans hKkTrans
    hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvExtractExtractProgram_normalize x i j k l ll kk P1 P2
      hXTrans hITrans hJTrans hKTrans hLTrans hLlTrans hKkTrans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy : __eo_typeof (bvExtractExtractTerm x i j k l ll kk) =
      Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hPremLl : eo_interprets M (bvExtractExtractPrem i l ll) true := by
    simpa [hP1] using hP1True
  have hPremKk : eo_interprets M (bvExtractExtractPrem i k kk) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_extract_extract_term M hM x i j k l ll kk
    hXTrans hTermTy hPremLl hPremKk
