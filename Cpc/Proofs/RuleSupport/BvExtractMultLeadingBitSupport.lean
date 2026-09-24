module

public import Cpc.Proofs.RuleSupport.BvExtractConcatSupport
import all Cpc.Proofs.RuleSupport.BvExtractConcatSupport
public import Cpc.Proofs.RuleSupport.BvMultSltMultSupport
import all Cpc.Proofs.RuleSupport.BvMultSltMultSupport

public section

open Eo
open SmtEval
open Smtm

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

def bvExtractMultLeadingZeros (i n : Nat) : Nat :=
  if i = 0 then n else n - (i.log2 + 1)

private theorem prefix_payload_bound
    {i n tail z : Nat} (hi : i < 2 ^ n) (hz : z < 2 ^ tail) :
    i * 2 ^ tail + z <
      2 ^ (n + tail - bvExtractMultLeadingZeros i n) := by
  unfold bvExtractMultLeadingZeros
  by_cases hi0 : i = 0
  · subst i
    simp
    have hSub : n + tail - n = tail := by omega
    simpa [hSub] using hz
  · rw [if_neg hi0]
    have hLogLt : i.log2 < n := (Nat.log2_lt hi0).2 hi
    have hiPow : i < 2 ^ (i.log2 + 1) := Nat.lt_log2_self
    have hSum : i * 2 ^ tail + z <
        2 ^ (i.log2 + 1) * 2 ^ tail := by
      calc
        i * 2 ^ tail + z < i * 2 ^ tail + 2 ^ tail :=
          Nat.add_lt_add_left hz _
        _ = (i + 1) * 2 ^ tail := by
          rw [Nat.add_mul]
          simp
        _ ≤ 2 ^ (i.log2 + 1) * 2 ^ tail :=
          Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hiPow)
    have hExp : n + tail - (n - (i.log2 + 1)) = i.log2 + 1 + tail := by
      omega
    rw [hExp, Nat.pow_add]
    exact hSum

theorem extract_mult_leading_bit_core
    {W WX WY xi yi xv yv low len : Nat}
    (hWX : WX ≤ W) (hWY : WY ≤ W)
    (hXi : xi < 2 ^ (W - WX)) (hYi : yi < 2 ^ (W - WY))
    (hXv : xv < 2 ^ WX) (hYv : yv < 2 ^ WY)
    (hLow :
      (2 * W -
        (bvExtractMultLeadingZeros xi (W - WX) +
          bvExtractMultLeadingZeros yi (W - WY))) ≤ low) :
    (((BitVec.ofNat W
        ((xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv))).extractLsb'
      low len).toNat) = 0 := by
  let zx := bvExtractMultLeadingZeros xi (W - WX)
  let zy := bvExtractMultLeadingZeros yi (W - WY)
  have hX : xi * 2 ^ WX + xv < 2 ^ (W - zx) := by
    have := prefix_payload_bound hXi hXv
    simpa [zx, Nat.sub_add_cancel hWX] using this
  have hY : yi * 2 ^ WY + yv < 2 ^ (W - zy) := by
    have := prefix_payload_bound hYi hYv
    simpa [zy, Nat.sub_add_cancel hWY] using this
  have hZx : zx ≤ W := by
    have : zx ≤ W - WX := by
      unfold zx bvExtractMultLeadingZeros
      split <;> omega
    exact Nat.le_trans this (Nat.sub_le W WX)
  have hZy : zy ≤ W := by
    have : zy ≤ W - WY := by
      unfold zy bvExtractMultLeadingZeros
      split <;> omega
    exact Nat.le_trans this (Nat.sub_le W WY)
  have hProd :
      (xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv) <
        2 ^ (2 * W - (zx + zy)) := by
    have hMul :
        (xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv) <
          2 ^ (W - zx) * 2 ^ (W - zy) := by
      by_cases hy0 : yi * 2 ^ WY + yv = 0
      · rw [hy0, Nat.mul_zero]
        exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      · exact Nat.lt_trans
          (Nat.mul_lt_mul_of_pos_right hX (Nat.pos_of_ne_zero hy0))
          (Nat.mul_lt_mul_of_pos_left hY (Nat.two_pow_pos _))
    have hExp : (W - zx) + (W - zy) = 2 * W - (zx + zy) := by omega
    rw [← Nat.pow_add, hExp] at hMul
    exact hMul
  have hProdLow :
      (xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv) < 2 ^ low := by
    exact Nat.lt_of_lt_of_le hProd (Nat.pow_le_pow_right (by decide) (by
      simpa [zx, zy] using hLow))
  have hModLow :
      (BitVec.ofNat W
        ((xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv))).toNat < 2 ^ low := by
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hProdLow
  simp only [BitVec.extractLsb'_toNat]
  rw [Nat.shiftRight_eq_zero _ _ hModLow]
  simp

private def extractLeadApp1 (op x : Term) : Term := Term.Apply op x
private def extractLeadApp2 (op x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y
private def extractLeadApp3 (op x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply op x) y) z

def bvExtractMultLeadingWidthPrem (xin x : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.gt)
      (extractLeadApp2 (Term.UOp UserOp.plus) xin
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (extractLeadApp1 (Term.UOp UserOp._at_bvsize) x)
          (Term.Numeral 0)))
      (Term.Numeral 64))
    (Term.Boolean true)

def bvExtractMultLeadingNonnegPrem (i : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.geq) i (Term.Numeral 0))
    (Term.Boolean true)

def bvExtractMultLeadingRangePrem (i n : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.lt) i
      (extractLeadApp1 (Term.UOp UserOp.int_pow2) n))
    (Term.Boolean true)

def bvExtractMultLeadingZerosTerm (i n : Term) : Term :=
  extractLeadApp3 (Term.UOp UserOp.ite)
    (extractLeadApp2 (Term.UOp UserOp.eq) i (Term.Numeral 0)) n
    (extractLeadApp2 (Term.UOp UserOp.neg) n
      (extractLeadApp2 (Term.UOp UserOp.plus) (Term.Numeral 1)
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (extractLeadApp1 (Term.UOp UserOp.int_log2) i)
          (Term.Numeral 0))))

def bvExtractMultLeadingLowPrem
    (low xi xin x yi yin : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.leq)
      (extractLeadApp2 (Term.UOp UserOp.neg)
        (extractLeadApp2 (Term.UOp UserOp.mult) (Term.Numeral 2)
          (extractLeadApp2 (Term.UOp UserOp.mult)
            (extractLeadApp2 (Term.UOp UserOp.plus) xin
              (extractLeadApp2 (Term.UOp UserOp.plus)
                (extractLeadApp1 (Term.UOp UserOp._at_bvsize) x)
                (Term.Numeral 0)))
            (Term.Numeral 1)))
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (bvExtractMultLeadingZerosTerm xi xin)
          (extractLeadApp2 (Term.UOp UserOp.plus)
            (bvExtractMultLeadingZerosTerm yi yin) (Term.Numeral 0))))
      low)
    (Term.Boolean true)

private def bvExtractMultLeadingZerosRefs
    (iCond nThen nSub iLog : Term) : Term :=
  extractLeadApp3 (Term.UOp UserOp.ite)
    (extractLeadApp2 (Term.UOp UserOp.eq) iCond (Term.Numeral 0)) nThen
    (extractLeadApp2 (Term.UOp UserOp.neg) nSub
      (extractLeadApp2 (Term.UOp UserOp.plus) (Term.Numeral 1)
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (extractLeadApp1 (Term.UOp UserOp.int_log2) iLog)
          (Term.Numeral 0))))

private def bvExtractMultLeadingLowPremRefs
    (low xin x xiCond xinThen xinSub xiLog yiCond yinThen yinSub yiLog : Term) :
    Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.leq)
      (extractLeadApp2 (Term.UOp UserOp.neg)
        (extractLeadApp2 (Term.UOp UserOp.mult) (Term.Numeral 2)
          (extractLeadApp2 (Term.UOp UserOp.mult)
            (extractLeadApp2 (Term.UOp UserOp.plus) xin
              (extractLeadApp2 (Term.UOp UserOp.plus)
                (extractLeadApp1 (Term.UOp UserOp._at_bvsize) x)
                (Term.Numeral 0)))
            (Term.Numeral 1)))
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (bvExtractMultLeadingZerosRefs xiCond xinThen xinSub xiLog)
          (extractLeadApp2 (Term.UOp UserOp.plus)
            (bvExtractMultLeadingZerosRefs yiCond yinThen yinSub yiLog)
            (Term.Numeral 0))))
      low)
    (Term.Boolean true)

def bvExtractMultLeadingResultWidthPrem (w high low : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq) w
    (extractLeadApp2 (Term.UOp UserOp.plus) (Term.Numeral 1)
      (extractLeadApp2 (Term.UOp UserOp.plus)
        (extractLeadApp2 (Term.UOp UserOp.neg) high low)
        (Term.Numeral 0)))

def bvExtractMultLeadingOperand (i n tail : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.concat)
    (extractLeadApp1 (Term.UOp1 UserOp1.int_to_bv n) i)
    (extractLeadApp2 (Term.UOp UserOp.concat) tail (Term.Binary 0 0))

def bvExtractMultLeadingRaw
    (high low xi xin x yi yin y w : Term) : Term :=
  let xFull := bvExtractMultLeadingOperand xi xin x
  let yFull := bvExtractMultLeadingOperand yi yin y
  let product := __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.bvmul) xFull)
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) yFull)
      (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof xFull)))
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.UOp2 UserOp2.extract high low) product))
    (extractLeadApp1 (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))

def bvExtractMultLeadingProduct
    (xi xin x yi yin y : Term) : Term :=
  let xFull := bvExtractMultLeadingOperand xi xin x
  let yFull := bvExtractMultLeadingOperand yi yin y
  extractLeadApp2 (Term.UOp UserOp.bvmul) xFull
    (extractLeadApp2 (Term.UOp UserOp.bvmul) yFull
      (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof xFull)))

def bvExtractMultLeadingDirect
    (high low xi xin x yi yin y w : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (bvExtractTerm (bvExtractMultLeadingProduct xi xin x yi yin y) high low)
    (extractLeadApp1 (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))

private theorem bvExtractMultLeadingRaw_eq_direct
    (high low xi xin x yi yin y w : Term) :
    __eo_typeof
        (bvExtractMultLeadingRaw high low xi xin x yi yin y w) = Term.Bool ->
    bvExtractMultLeadingRaw high low xi xin x yi yin y w =
      bvExtractMultLeadingDirect high low xi xin x yi yin y w := by
  intro hTy
  have hTop :
      bvExtractMultLeadingRaw high low xi xin x yi yin y w ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  unfold bvExtractMultLeadingRaw at hTop ⊢
  dsimp only
  have hEqFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hTop
  have hExtract := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFun
  have hProduct := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hExtract
  have hInner := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hProduct
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hTop,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFun,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hExtract,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hProduct,
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hInner]
  rfl

private theorem extractLead_int_to_bv_context
    (width value : Term) :
    width ≠ Term.Stuck -> value ≠ Term.Stuck ->
    __eo_typeof
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv width) value) ≠ Term.Stuck ->
    ∃ W : native_Int,
      width = Term.Numeral W ∧ native_zleq 0 W = true ∧
      __eo_typeof value = Term.UOp UserOp.Int ∧
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv width) value) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
  intro hWidthNe hValueNe hTyNe
  change __eo_typeof_int_to_bv (__eo_typeof width) width
      (__eo_typeof value) ≠ Term.Stuck at hTyNe
  have hValueTy : __eo_typeof value = Term.UOp UserOp.Int := by
    cases hv : __eo_typeof value <;>
      simp [__eo_typeof_int_to_bv, hv] at hTyNe ⊢
    case UOp op =>
      cases op <;>
        simp at hTyNe ⊢
  have hWidthTy : __eo_typeof width = Term.UOp UserOp.Int := by
    cases hw : __eo_typeof width <;>
      simp [__eo_typeof_int_to_bv, hw, hValueTy] at hTyNe ⊢
    case UOp op =>
      cases op <;>
        simp at hTyNe ⊢
  have hReqNe :
      __eo_requires (__eo_gt width (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) width) ≠
        Term.Stuck := by
    simpa [__eo_typeof_int_to_bv, hWidthTy, hValueTy, hWidthNe] using hTyNe
  have hGuard :
      __eo_gt width (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReqNe
  cases width <;> simp [__eo_gt] at hGuard
  case Numeral W =>
    have hW0 : native_zleq 0 W = true := by
      have hW : (-1 : Int) < W := by
        simpa [SmtEval.native_zlt] using hGuard
      have : (0 : Int) ≤ W := by omega
      simpa [SmtEval.native_zleq] using this
    refine ⟨W, rfl, hW0, hValueTy, ?_⟩
    change __eo_typeof_int_to_bv (Term.UOp UserOp.Int) (Term.Numeral W)
        (__eo_typeof value) = _
    rw [hValueTy]
    have hGt : native_zlt (-1 : native_Int) W = true := by
      simpa [__eo_gt] using hGuard
    simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, hGt,
      native_ite, native_teq, native_not]

private theorem extractLead_operand_context
    (i n tail width : Term) :
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation tail ->
    __eo_typeof (bvExtractMultLeadingOperand i n tail) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    ∃ N WT : native_Int,
      n = Term.Numeral N ∧ width = Term.Numeral (native_zplus N WT) ∧
      native_zleq 0 N = true ∧ native_zleq 0 WT = true ∧
      __eo_typeof i = Term.UOp UserOp.Int ∧
      __eo_typeof tail =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral WT) ∧
      __smtx_typeof (__eo_to_smt i) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt tail) =
        SmtType.BitVec (native_int_to_nat WT) := by
  intro hITrans hNTrans hTailTrans hOperandTy
  have hINe := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hTailNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tail hTailTrans
  have hOperandNe :
      __eo_typeof (bvExtractMultLeadingOperand i n tail) ≠ Term.Stuck := by
    rw [hOperandTy]
    intro h
    cases h
  have hOuterCore :
      __eo_typeof_concat
          (__eo_typeof
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) i))
          (__eo_typeof
            (extractLeadApp2 (Term.UOp UserOp.concat) tail
              (Term.Binary 0 0))) ≠ Term.Stuck := by
    have hsimpa := hOperandNe
    try simp [bvExtractMultLeadingOperand, extractLeadApp1, extractLeadApp2] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hOuterCore with
    ⟨prefixWidth, tailWidth, hPrefixTy, hTailConcatTy⟩
  have hPrefixNe :
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) i) ≠
        Term.Stuck := by
    rw [hPrefixTy]
    intro h
    cases h
  rcases extractLead_int_to_bv_context n i hNNe hINe hPrefixNe with
    ⟨N, hN, hN0, hITy, hPrefixTy'⟩
  have hPrefixWidth : prefixWidth = Term.Numeral N := by
    rw [hPrefixTy] at hPrefixTy'
    injection hPrefixTy'
  subst prefixWidth
  subst n
  have hTailConcatNe :
      __eo_typeof
          (extractLeadApp2 (Term.UOp UserOp.concat) tail
            (Term.Binary 0 0)) ≠ Term.Stuck := by
    rw [hTailConcatTy]
    intro h
    cases h
  have hTailCore :
      __eo_typeof_concat (__eo_typeof tail)
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    have hsimpa := hTailConcatNe
    try simp [extractLeadApp2] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hTailCore with
    ⟨tailArgWidth, _emptyWidth, hTailTyRaw, _hEmptyTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width tail tailArgWidth
      hTailTrans hTailTyRaw with
    ⟨WT, hTailArgWidth, hWT0, hTailSmtTy⟩
  subst tailArgWidth
  have hTailTy :
      __eo_typeof tail =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral WT) := hTailTyRaw
  have hITySmt : __smtx_typeof (__eo_to_smt i) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      i (Term.UOp UserOp.Int) (__eo_to_smt i) rfl hITrans hITy
  have hTailCalculated :
      __eo_typeof
          (extractLeadApp2 (Term.UOp UserOp.concat) tail
            (Term.Binary 0 0)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral WT) := by
    have hEmpty :
        __eo_typeof (Term.Binary 0 0) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0) := by
      native_decide
    change __eo_typeof_concat (__eo_typeof tail)
      (__eo_typeof (Term.Binary 0 0)) = _
    rw [hTailTy, hEmpty]
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus]
  have hCalculated :
      __eo_typeof (bvExtractMultLeadingOperand i (Term.Numeral N) tail) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus N WT)) := by
    change __eo_typeof_concat
      (__eo_typeof
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral N)) i))
      (__eo_typeof
        (extractLeadApp2 (Term.UOp UserOp.concat) tail (Term.Binary 0 0))) = _
    rw [hPrefixTy', hTailCalculated]
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply]
  have hWidth : width = Term.Numeral (native_zplus N WT) := by
    rw [hOperandTy] at hCalculated
    injection hCalculated
  exact ⟨N, WT, rfl, hWidth, hN0, hWT0, hITy, hTailTy,
    hITySmt, hTailSmtTy⟩

private theorem extractLead_smt_typeof_int_to_bv
    (value : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt value) = SmtType.Int ->
    native_zleq 0 W = true ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) value)) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hValueTy hW0
  change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt value)) = _
  rw [typeof_int_to_bv_eq, hValueTy]
  simp [__smtx_typeof_int_to_bv, native_ite, hW0]

private theorem extractLead_smt_typeof_bvmul
    (p q : Term) (W : Nat) :
    __smtx_typeof (__eo_to_smt p) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt q) = SmtType.BitVec W ->
    __smtx_typeof
        (__eo_to_smt (extractLeadApp2 (Term.UOp UserOp.bvmul) p q)) =
      SmtType.BitVec W := by
  intro hp hq
  change __smtx_typeof (SmtTerm.bvmul (__eo_to_smt p) (__eo_to_smt q)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hp, hq, native_ite,
    native_nateq, Smtm.native_nateq]

private theorem extractLead_smt_typeof_bitvec_payload (v : BitVec W) :
    __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int W) (v.toNat : Int)) =
      SmtType.BitVec W := by
  have hW0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hMod :
      native_mod_total (v.toNat : Int)
          (native_int_pow2 (native_nat_to_int W)) = (v.toNat : Int) := by
    rw [native_int_pow2_nat W]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by exact_mod_cast v.isLt)
  have hCanon :
      native_zeq (v.toNat : Int)
          (native_mod_total (v.toNat : Int)
            (native_int_pow2 (native_nat_to_int W))) = true := by
    simpa [SmtEval.native_zeq] using hMod.symm
  have hAnd :
      native_and (native_zleq 0 (native_nat_to_int W))
          (native_zeq (v.toNat : Int)
            (native_mod_total (v.toNat : Int)
              (native_int_pow2 (native_nat_to_int W)))) = true := by
    simp [SmtEval.native_and, hW0, hCanon]
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hAnd]
  simp [native_ite, native_int_to_nat, native_nat_to_int,
    SmtEval.native_int_to_nat, Smtm.native_nat_to_int]

private theorem bvExtractMultLeading_context
    (high low xi xin x yi yin y w : Term) :
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation xi ->
    RuleProofs.eo_has_smt_translation xin ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation yi ->
    RuleProofs.eo_has_smt_translation yin ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof
        (bvExtractMultLeadingDirect high low xi xin x yi yin y w) =
      Term.Bool ->
    ∃ XIN YIN XW YW H L RW : native_Int,
      xin = Term.Numeral XIN ∧ yin = Term.Numeral YIN ∧
      high = Term.Numeral H ∧ low = Term.Numeral L ∧
      w = Term.Numeral RW ∧
      native_zleq 0 XIN = true ∧ native_zleq 0 YIN = true ∧
      native_zleq 0 XW = true ∧ native_zleq 0 YW = true ∧
      native_zleq 0 RW = true ∧
      native_zplus XIN XW = native_zplus YIN YW ∧
      native_zleq 0 L = true ∧
      native_zlt H (native_zplus XIN XW) = true ∧
      native_zlt 0 (native_zplus (native_zplus H 1) (native_zneg L)) = true ∧
      RW = native_zplus (native_zplus H 1) (native_zneg L) ∧
      __smtx_typeof (__eo_to_smt xi) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt yi) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat XW) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat YW) ∧
      __eo_nil (Term.UOp UserOp.bvmul)
          (__eo_typeof (bvExtractMultLeadingOperand xi xin x)) =
        Term.Binary
          (native_nat_to_int
            (native_int_to_nat (native_zplus XIN XW)))
          ((1#(native_int_to_nat (native_zplus XIN XW))).toNat : Int) ∧
      __smtx_typeof
          (__eo_to_smt (bvExtractMultLeadingProduct xi xin x yi yin y)) =
        SmtType.BitVec (native_int_to_nat (native_zplus XIN XW)) := by
  intro hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
    hYTrans hWTrans hDirectTy
  change __eo_typeof_eq
      (__eo_typeof
        (bvExtractTerm (bvExtractMultLeadingProduct xi xin x yi yin y)
          high low))
      (__eo_typeof
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) =
    Term.Bool at hDirectTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hDirectTy with
    ⟨hExtractNe, hZeroNe⟩
  have hOperandTypes :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hDirectTy
  have hWNe := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases extractLead_int_to_bv_context w (Term.Numeral 0) hWNe (by simp)
      hZeroNe with
    ⟨RW, hW, hRW0, _hZeroIntTy, hZeroTy⟩
  have hProductTyNe :
      __eo_typeof (bvExtractMultLeadingProduct xi xin x yi yin y) ≠
        Term.Stuck := by
    change __eo_typeof_extract (__eo_typeof high) high (__eo_typeof low) low
      (__eo_typeof (bvExtractMultLeadingProduct xi xin x yi yin y)) ≠
        Term.Stuck at hExtractNe
    rcases eo_typeof_extract_arg_bitvec_of_ne_stuck hExtractNe with
      ⟨productWidth, hProductTy⟩
    rw [hProductTy]
    intro h
    cases h
  have hProductCore :
      __eo_typeof_bvand
          (__eo_typeof (bvExtractMultLeadingOperand xi xin x))
          (__eo_typeof
            (extractLeadApp2 (Term.UOp UserOp.bvmul)
              (bvExtractMultLeadingOperand yi yin y)
              (__eo_nil (Term.UOp UserOp.bvmul)
                (__eo_typeof (bvExtractMultLeadingOperand xi xin x))))) ≠
        Term.Stuck := by
    have hsimpa := hProductTyNe
    try simp [bvExtractMultLeadingProduct, extractLeadApp2] at hsimpa ⊢
    exact hsimpa
  rcases RuleProofs.eo_typeof_bvand_args_of_ne_stuck _ _ hProductCore with
    ⟨fullWidth, hXFullTy, hInnerTy, _hFullWidthNe⟩
  have hInnerNe :
      __eo_typeof
          (extractLeadApp2 (Term.UOp UserOp.bvmul)
            (bvExtractMultLeadingOperand yi yin y)
            (__eo_nil (Term.UOp UserOp.bvmul)
              (__eo_typeof (bvExtractMultLeadingOperand xi xin x)))) ≠
        Term.Stuck := by
    rw [hInnerTy]
    intro h
    cases h
  have hInnerCore :
      __eo_typeof_bvand
          (__eo_typeof (bvExtractMultLeadingOperand yi yin y))
          (__eo_typeof
            (__eo_nil (Term.UOp UserOp.bvmul)
              (__eo_typeof (bvExtractMultLeadingOperand xi xin x)))) ≠
        Term.Stuck := by
    have hsimpa := hInnerNe
    try simp [extractLeadApp2] at hsimpa ⊢
    exact hsimpa
  rcases RuleProofs.eo_typeof_bvand_args_of_ne_stuck _ _ hInnerCore with
    ⟨innerWidth, hYFullTy, hNilTy, _hInnerWidthNe⟩
  have hInnerWidth : innerWidth = fullWidth := by
    rw [hInnerTy] at hInnerNe
    have hInnerCalc :
        __eo_typeof_bvand
            (Term.Apply (Term.UOp UserOp.BitVec) innerWidth)
            (Term.Apply (Term.UOp UserOp.BitVec) innerWidth) =
          Term.Apply (Term.UOp UserOp.BitVec) innerWidth := by
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not]
    have hInnerTy' :
        __eo_typeof
            (extractLeadApp2 (Term.UOp UserOp.bvmul)
              (bvExtractMultLeadingOperand yi yin y)
              (__eo_nil (Term.UOp UserOp.bvmul)
                (__eo_typeof (bvExtractMultLeadingOperand xi xin x)))) =
          Term.Apply (Term.UOp UserOp.BitVec) innerWidth := by
      change __eo_typeof_bvand _ _ = _
      rw [hYFullTy, hNilTy]
      exact hInnerCalc
    rw [hInnerTy] at hInnerTy'
    symm
    injection hInnerTy'
  subst innerWidth
  rcases extractLead_operand_context xi xin x fullWidth hXiTrans hXinTrans
      hXTrans hXFullTy with
    ⟨XIN, XW, hXin, hFullWidth, hXIN0, hXW0, hXiTy, hXTy,
      hXiSmtTy, hXSmtTy⟩
  subst fullWidth
  rcases extractLead_operand_context yi yin y
      (Term.Numeral (native_zplus XIN XW)) hYiTrans hYinTrans hYTrans
      hYFullTy with
    ⟨YIN, YW, hYin, hWidthsRaw, hYIN0, hYW0, hYiTy, hYTy,
      hYiSmtTy, hYSmtTy⟩
  subst xin
  subst yin
  have hWidths : native_zplus XIN XW = native_zplus YIN YW := by
    injection hWidthsRaw
  have hFull0 : native_zleq 0 (native_zplus XIN XW) = true := by
    have h1 : (0 : Int) ≤ XIN := by
      simpa [SmtEval.native_zleq] using hXIN0
    have h2 : (0 : Int) ≤ XW := by
      simpa [SmtEval.native_zleq] using hXW0
    have : (0 : Int) ≤ XIN + XW := by omega
    have hsimpa := this
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  let FW := native_int_to_nat (native_zplus XIN XW)
  have hNatX :
      FW = native_int_to_nat XIN + native_int_to_nat XW := by
    change (XIN + XW).toNat = XIN.toNat + XW.toNat
    exact Int.toNat_add
      (by simpa [SmtEval.native_zleq] using hXIN0)
      (by simpa [SmtEval.native_zleq] using hXW0)
  have hNatY :
      FW = native_int_to_nat YIN + native_int_to_nat YW := by
    unfold FW
    rw [hWidths]
    change (YIN + YW).toNat = YIN.toNat + YW.toNat
    exact Int.toNat_add
      (by simpa [SmtEval.native_zleq] using hYIN0)
      (by simpa [SmtEval.native_zleq] using hYW0)
  have hXPrefixSmt :=
    extractLead_smt_typeof_int_to_bv xi XIN hXiSmtTy hXIN0
  have hYPrefixSmt :=
    extractLead_smt_typeof_int_to_bv yi YIN hYiSmtTy hYIN0
  have hXTailSmt := bvConcat_term_smt_type x (Term.Binary 0 0)
    (native_int_to_nat XW) 0 hXSmtTy bvConcat_empty_smt_type
  have hYTailSmt := bvConcat_term_smt_type y (Term.Binary 0 0)
    (native_int_to_nat YW) 0 hYSmtTy bvConcat_empty_smt_type
  have hXFullSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractMultLeadingOperand xi (Term.Numeral XIN) x)) =
        SmtType.BitVec FW := by
    have h := bvConcat_term_smt_type
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral XIN)) xi)
      (bvConcatTerm x (Term.Binary 0 0))
      (native_int_to_nat XIN) (native_int_to_nat XW)
      hXPrefixSmt (by simpa [Nat.add_zero] using hXTailSmt)
    simpa [bvExtractMultLeadingOperand, bvConcatTerm, extractLeadApp1,
      extractLeadApp2, hNatX] using h
  have hYFullSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractMultLeadingOperand yi (Term.Numeral YIN) y)) =
        SmtType.BitVec FW := by
    have h := bvConcat_term_smt_type
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral YIN)) yi)
      (bvConcatTerm y (Term.Binary 0 0))
      (native_int_to_nat YIN) (native_int_to_nat YW)
      hYPrefixSmt (by simpa [Nat.add_zero] using hYTailSmt)
    simpa [bvExtractMultLeadingOperand, bvConcatTerm, extractLeadApp1,
      extractLeadApp2, hNatY] using h
  have hRound := native_int_to_nat_roundtrip
    (native_zplus XIN XW) hFull0
  have hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zplus XIN XW))) ≠ Term.Stuck := by
    rw [hXFullTy] at hNilTy
    intro hNil
    rw [hNil] at hNilTy
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zplus XIN XW)) at hNilTy
    cases hNilTy
  have hNilEq :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_zplus XIN XW))) =
        Term.Binary (native_nat_to_int FW) ((1#FW).toNat : Int) := by
    rw [← hRound]
    exact bvMultSlt_nil_bvmul_bitvec FW (by
      simpa only [FW, hRound] using hNilNe)
  have hNilSmt :
      __smtx_typeof
          (__eo_to_smt
            (__eo_nil (Term.UOp UserOp.bvmul)
              (Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_zplus XIN XW))))) =
        SmtType.BitVec FW := by
    rw [hNilEq]
    exact extractLead_smt_typeof_bitvec_payload (1#FW)
  have hInnerSmt := extractLead_smt_typeof_bvmul
    (bvExtractMultLeadingOperand yi (Term.Numeral YIN) y)
    (__eo_nil (Term.UOp UserOp.bvmul)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zplus XIN XW)))) FW hYFullSmt hNilSmt
  have hInnerSmtCanon := hInnerSmt
  rw [← hXFullTy] at hInnerSmtCanon
  have hProductSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
              (Term.Numeral YIN) y)) = SmtType.BitVec FW := by
    simpa [bvExtractMultLeadingProduct] using
      extractLead_smt_typeof_bvmul
        (bvExtractMultLeadingOperand xi (Term.Numeral XIN) x)
        (extractLeadApp2 (Term.UOp UserOp.bvmul)
          (bvExtractMultLeadingOperand yi (Term.Numeral YIN) y)
          (__eo_nil (Term.UOp UserOp.bvmul)
            (__eo_typeof
              (bvExtractMultLeadingOperand xi (Term.Numeral XIN) x))))
        FW hXFullSmt hInnerSmtCanon
  have hProductTrans :
      RuleProofs.eo_has_smt_translation
        (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
          (Term.Numeral YIN) y) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hProductSmt]
    simp
  rcases bv_extract_context_of_non_stuck
      (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
        (Term.Numeral YIN) y) high low hProductTrans hExtractNe with
    ⟨fullInt, H, L, hProductEoTy, hHigh, hLow, _hFullInt0, hL0,
      hHFull, hResultPos, _hProductSmtTy⟩
  have hFullInt : fullInt = native_zplus XIN XW := by
    have hInnerTyCanon := hInnerTy
    rw [hXFullTy] at hInnerTyCanon
    have hProductEoTy' :
        __eo_typeof
            (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
              (Term.Numeral YIN) y) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_zplus XIN XW)) := by
      change __eo_typeof_bvand _ _ = _
      rw [hXFullTy, hInnerTyCanon]
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not]
    rw [hProductEoTy] at hProductEoTy'
    injection hProductEoTy' with _ hNum
    injection hNum
  subst fullInt
  subst high
  subst low
  subst w
  have hExtractTy := eo_typeof_extract_of_context
    (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
      (Term.Numeral YIN) y)
    (native_zplus XIN XW) H L hProductEoTy hL0 hHFull hResultPos
  have hRW :
      RW = native_zplus (native_zplus H 1) (native_zneg L) := by
    rw [hZeroTy] at hOperandTypes
    rw [hExtractTy] at hOperandTypes
    symm
    injection hOperandTypes with _ hNum
    injection hNum
  exact ⟨XIN, YIN, XW, YW, H, L, RW, rfl, rfl, rfl, rfl, rfl,
    hXIN0, hYIN0, hXW0, hYW0, hRW0, hWidths, hL0, hHFull,
    hResultPos, hRW, hXiSmtTy, hYiSmtTy, hXSmtTy, hYSmtTy,
    by simpa [FW, hXFullTy] using hNilEq,
    by simpa [FW] using hProductSmt⟩

def bvExtractMultLeadingProgram
    (high low xi xin x yi yin y w P1 P2 P3 P4 P5 P6 P7 : Term) : Term :=
  __eo_prog_bv_extract_mult_leading_bit high low xi xin x yi yin y w
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
    (Proof.pf P5) (Proof.pf P6) (Proof.pf P7)

theorem typed_bvExtractMultLeadingRaw
    (high low xi xin x yi yin y w : Term) :
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation xi ->
    RuleProofs.eo_has_smt_translation xin ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation yi ->
    RuleProofs.eo_has_smt_translation yin ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof
        (bvExtractMultLeadingRaw high low xi xin x yi yin y w) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractMultLeadingRaw high low xi xin x yi yin y w) := by
  intro hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
    hYTrans hWTrans hRawTy
  have hRawEq := bvExtractMultLeadingRaw_eq_direct
    high low xi xin x yi yin y w hRawTy
  have hDirectTy :
      __eo_typeof
          (bvExtractMultLeadingDirect high low xi xin x yi yin y w) =
        Term.Bool := by
    rw [← hRawEq]
    exact hRawTy
  rcases bvExtractMultLeading_context high low xi xin x yi yin y w
      hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
      hYTrans hWTrans hDirectTy with
    ⟨XIN, YIN, XW, YW, H, L, RW, rfl, rfl, rfl, rfl, rfl,
      hXIN0, _hYIN0, hXW0, _hYW0, hRW0, _hWidths, hL0, hHFull,
      hResultPos, hRW, _hXiSmtTy, _hYiSmtTy, _hXSmtTy, _hYSmtTy,
      _hNilEq, hProductSmtTy⟩
  subst RW
  let FI := native_zplus XIN XW
  have hFI0 : native_zleq 0 FI = true := by
    have h1 : (0 : Int) ≤ XIN := by
      simpa [SmtEval.native_zleq] using hXIN0
    have h2 : (0 : Int) ≤ XW := by
      simpa [SmtEval.native_zleq] using hXW0
    have : (0 : Int) ≤ XIN + XW := by omega
    simpa [FI, SmtEval.native_zleq, SmtEval.native_zplus] using this
  have hExtractSmtTy := smt_typeof_extract_of_context
    (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
      (Term.Numeral YIN) y) FI H L (by simpa [FI] using hProductSmtTy)
      hFI0 hL0 (by simpa [FI] using hHFull) hResultPos
  have hZeroSmtTy := extractLead_smt_typeof_int_to_bv
    (Term.Numeral 0)
      (native_zplus (native_zplus H 1) (native_zneg L)) (by rfl) hRW0
  rw [hRawEq]
  unfold bvExtractMultLeadingDirect
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hExtractSmtTy.trans hZeroSmtTy.symm) (by rw [hExtractSmtTy]; simp)

private theorem extractLead_eval_int_term
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ->
    ∃ k : native_Int,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral k := by
  intro hTy
  have hEvalTy := smt_model_eval_preserves_type_of_non_none M hM
    (__eo_to_smt t) (by simp [term_has_non_none_type, hTy])
  exact int_value_canonical (by simpa [hTy] using hEvalTy)

private theorem extractLead_nonneg_of_premise
    (M : SmtModel) (i : Term) (I : native_Int) :
    __smtx_model_eval M (__eo_to_smt i) = SmtValue.Numeral I ->
    eo_interprets M (bvExtractMultLeadingNonnegPrem i) true ->
    native_zleq 0 I = true := by
  intro hIEval hPrem
  have hEval := bvConcat_model_eval_eq_true_of_eo_eq_true M
    (extractLeadApp2 (Term.UOp UserOp.geq) i (Term.Numeral 0))
    (Term.Boolean true) hPrem
  simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval] at hEval
  change __smtx_model_eval M
      (SmtTerm.geq (__eo_to_smt i) (SmtTerm.Numeral 0)) =
    SmtValue.Boolean true at hEval
  rw [__smtx_model_eval.eq_def] at hEval
  simpa [__smtx_model_eval, __smtx_model_eval_geq,
    __smtx_model_eval_leq, hIEval] using hEval

private theorem extractLead_range_of_premise
    (M : SmtModel) (i : Term) (I N : native_Int) :
    __smtx_model_eval M (__eo_to_smt i) = SmtValue.Numeral I ->
    eo_interprets M
      (bvExtractMultLeadingRangePrem i (Term.Numeral N)) true ->
    native_zlt I (native_int_pow2 N) = true := by
  intro hIEval hPrem
  have hEval := bvConcat_model_eval_eq_true_of_eo_eq_true M
    (extractLeadApp2 (Term.UOp UserOp.lt) i
      (extractLeadApp1 (Term.UOp UserOp.int_pow2) (Term.Numeral N)))
    (Term.Boolean true) hPrem
  simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval] at hEval
  change __smtx_model_eval M
      (SmtTerm.lt (__eo_to_smt i)
        (SmtTerm.int_pow2 (SmtTerm.Numeral N))) =
    SmtValue.Boolean true at hEval
  rw [__smtx_model_eval.eq_def] at hEval
  simpa [__smtx_model_eval, __smtx_model_eval_lt,
    __smtx_model_eval_int_pow2, hIEval] using hEval

private def bvExtractMultLeadingZerosInt
    (i n : native_Int) : native_Int :=
  if i = 0 then n else n - (native_int_log2 i + 1)

private theorem bvExtractMultLeadingZerosInt_eq_nat
    (i n : native_Int)
    (hi0 : native_zleq 0 i = true)
    (hn0 : native_zleq 0 n = true)
    (hiRange : native_zlt i (native_int_pow2 n) = true) :
    bvExtractMultLeadingZerosInt i n =
      (bvExtractMultLeadingZeros (native_int_to_nat i)
        (native_int_to_nat n) : Nat) := by
  have hiNonneg : (0 : Int) ≤ i := by
    simpa [SmtEval.native_zleq] using hi0
  have hnNonneg : (0 : Int) ≤ n := by
    simpa [SmtEval.native_zleq] using hn0
  have hiRound := native_int_to_nat_roundtrip i hi0
  have hnRound := native_int_to_nat_roundtrip n hn0
  have hiRangeNat :
      native_int_to_nat i < 2 ^ native_int_to_nat n := by
    have hiRangeInt : i < native_int_pow2 n := by
      simpa [SmtEval.native_zlt] using hiRange
    have hiCast : ((native_int_to_nat i : Nat) : Int) = i := by
      simpa [native_int_to_nat, SmtEval.native_int_to_nat] using
        Int.toNat_of_nonneg hiNonneg
    have hnCast : ((native_int_to_nat n : Nat) : Int) = n := by
      simpa [native_int_to_nat, SmtEval.native_int_to_nat] using
        Int.toNat_of_nonneg hnNonneg
    rw [← hiCast, ← hnCast] at hiRangeInt
    have hPow :
        native_int_pow2 ((native_int_to_nat n : Nat) : Int) =
          (2 ^ native_int_to_nat n : Nat) := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using
        native_int_pow2_nat (native_int_to_nat n)
    rw [hPow] at hiRangeInt
    exact_mod_cast hiRangeInt
  unfold bvExtractMultLeadingZerosInt bvExtractMultLeadingZeros
  by_cases hi : i = 0
  · subst i
    simpa [native_int_to_nat, native_nat_to_int,
      SmtEval.native_int_to_nat, Smtm.native_nat_to_int] using hnRound.symm
  · have hiNat : native_int_to_nat i ≠ 0 := by
      intro h
      have : i = 0 := by
        calc
          i = native_nat_to_int (native_int_to_nat i) := hiRound.symm
          _ = 0 := by simp [h, native_nat_to_int, Smtm.native_nat_to_int]
      exact hi this
    rw [if_neg hi, if_neg hiNat]
    have hLogLt :
        Nat.log2 (native_int_to_nat i) < native_int_to_nat n :=
      (Nat.log2_lt hiNat).2 hiRangeNat
    have hLogLe :
        Nat.log2 (native_int_to_nat i) + 1 ≤ native_int_to_nat n := by
      omega
    unfold native_int_log2
    have hCast := Int.natCast_sub hLogLe
    rw [← hnRound]
    have hsimpa := hCast.symm
    try simp [native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact hsimpa

private theorem extractLead_low_of_premise
    (M : SmtModel) (low xi x yi : Term)
    (L I J XIN YIN XW : native_Int) :
    low = Term.Numeral L ->
    __smtx_model_eval M (__eo_to_smt xi) = SmtValue.Numeral I ->
    __smtx_model_eval M (__eo_to_smt yi) = SmtValue.Numeral J ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat XW) ->
    native_zleq 0 XW = true ->
    eo_interprets M
      (bvExtractMultLeadingLowPrem low xi (Term.Numeral XIN) x yi
        (Term.Numeral YIN)) true ->
    native_zleq
      (2 * (XIN + XW) -
        (bvExtractMultLeadingZerosInt I XIN +
          bvExtractMultLeadingZerosInt J YIN)) L = true := by
  intro hLow hIEval hJEval hXSmtTy hXW0 hPrem
  subst low
  have hXWidthEval := bvConcat_eval_bvsize_of_smt_bitvec_nat M x
    (native_int_to_nat XW) hXSmtTy
  have hXWRound := native_int_to_nat_roundtrip XW hXW0
  rw [hXWRound] at hXWidthEval
  have hEval := bvConcat_model_eval_eq_true_of_eo_eq_true M
    (extractLeadApp2 (Term.UOp UserOp.leq)
      (extractLeadApp2 (Term.UOp UserOp.neg)
        (extractLeadApp2 (Term.UOp UserOp.mult) (Term.Numeral 2)
          (extractLeadApp2 (Term.UOp UserOp.mult)
            (extractLeadApp2 (Term.UOp UserOp.plus) (Term.Numeral XIN)
              (extractLeadApp2 (Term.UOp UserOp.plus)
                (extractLeadApp1 (Term.UOp UserOp._at_bvsize) x)
                (Term.Numeral 0)))
            (Term.Numeral 1)))
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (bvExtractMultLeadingZerosTerm xi (Term.Numeral XIN))
          (extractLeadApp2 (Term.UOp UserOp.plus)
            (bvExtractMultLeadingZerosTerm yi (Term.Numeral YIN))
            (Term.Numeral 0))))
      (Term.Numeral L)) (Term.Boolean true) hPrem
  simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval] at hEval
  change __smtx_model_eval M
      (SmtTerm.leq
        (SmtTerm.neg
          (SmtTerm.mult (SmtTerm.Numeral 2)
            (SmtTerm.mult
              (SmtTerm.plus (SmtTerm.Numeral XIN)
                (SmtTerm.plus
                  (__eo_to_smt
                    (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                  (SmtTerm.Numeral 0)))
              (SmtTerm.Numeral 1)))
          (SmtTerm.plus
            (SmtTerm.ite
              (SmtTerm.eq (__eo_to_smt xi) (SmtTerm.Numeral 0))
              (SmtTerm.Numeral XIN)
              (SmtTerm.neg (SmtTerm.Numeral XIN)
                (SmtTerm.plus (SmtTerm.Numeral 1)
                  (SmtTerm.plus (SmtTerm.int_log2 (__eo_to_smt xi))
                    (SmtTerm.Numeral 0)))))
            (SmtTerm.plus
              (SmtTerm.ite
                (SmtTerm.eq (__eo_to_smt yi) (SmtTerm.Numeral 0))
                (SmtTerm.Numeral YIN)
                (SmtTerm.neg (SmtTerm.Numeral YIN)
                  (SmtTerm.plus (SmtTerm.Numeral 1)
                    (SmtTerm.plus (SmtTerm.int_log2 (__eo_to_smt yi))
                      (SmtTerm.Numeral 0)))))
              (SmtTerm.Numeral 0))))
        (SmtTerm.Numeral L)) = SmtValue.Boolean true at hEval
  rw [__smtx_model_eval.eq_def] at hEval
  by_cases hIz : I = 0 <;> by_cases hJz : J = 0 <;>
    simp [__smtx_model_eval, __smtx_model_eval_leq,
      __smtx_model_eval_mult, __smtx_model_eval_plus, __smtx_model_eval__,
      __smtx_model_eval_ite, __smtx_model_eval_eq,
      __smtx_model_eval_int_log2, hIEval, hJEval, hXWidthEval, native_veq,
      bvExtractMultLeadingZerosInt, hIz, hJz, SmtEval.native_zleq,
      SmtEval.native_zplus, SmtEval.native_zmult, SmtEval.native_zneg]
      at hEval ⊢ <;>
    simpa [Int.sub_eq_add_neg, Int.add_comm, Int.add_left_comm,
      Int.add_assoc] using hEval

private theorem bvExtractMultLeadingZeros_le (i n : Nat) :
    bvExtractMultLeadingZeros i n ≤ n := by
  unfold bvExtractMultLeadingZeros
  split <;> omega

private theorem extractLead_low_nat
    (I J XIN YIN XW YW L : native_Int)
    (hI0 : native_zleq 0 I = true)
    (hJ0 : native_zleq 0 J = true)
    (hXIN0 : native_zleq 0 XIN = true)
    (hYIN0 : native_zleq 0 YIN = true)
    (hXW0 : native_zleq 0 XW = true)
    (hYW0 : native_zleq 0 YW = true)
    (hL0 : native_zleq 0 L = true)
    (hWidths : native_zplus XIN XW = native_zplus YIN YW)
    (hIRange : native_zlt I (native_int_pow2 XIN) = true)
    (hJRange : native_zlt J (native_int_pow2 YIN) = true)
    (hLow : native_zleq
      (2 * (XIN + XW) -
        (bvExtractMultLeadingZerosInt I XIN +
          bvExtractMultLeadingZerosInt J YIN)) L = true) :
    2 * native_int_to_nat (native_zplus XIN XW) -
        (bvExtractMultLeadingZeros (native_int_to_nat I)
            (native_int_to_nat XIN) +
          bvExtractMultLeadingZeros (native_int_to_nat J)
            (native_int_to_nat YIN)) ≤
      native_int_to_nat L := by
  let FW := native_int_to_nat (native_zplus XIN XW)
  let ZX := bvExtractMultLeadingZeros (native_int_to_nat I)
    (native_int_to_nat XIN)
  let ZY := bvExtractMultLeadingZeros (native_int_to_nat J)
    (native_int_to_nat YIN)
  have hXZeros := bvExtractMultLeadingZerosInt_eq_nat I XIN
    hI0 hXIN0 hIRange
  have hYZeros := bvExtractMultLeadingZerosInt_eq_nat J YIN
    hJ0 hYIN0 hJRange
  have hXINRound := native_int_to_nat_roundtrip XIN hXIN0
  have hYINRound := native_int_to_nat_roundtrip YIN hYIN0
  have hXWRound := native_int_to_nat_roundtrip XW hXW0
  have hYWRound := native_int_to_nat_roundtrip YW hYW0
  have hLRound := native_int_to_nat_roundtrip L hL0
  have hFWX : FW = native_int_to_nat XIN + native_int_to_nat XW := by
    unfold FW
    change (XIN + XW).toNat = XIN.toNat + XW.toNat
    exact Int.toNat_add
      (by simpa [SmtEval.native_zleq] using hXIN0)
      (by simpa [SmtEval.native_zleq] using hXW0)
  have hFWY : FW = native_int_to_nat YIN + native_int_to_nat YW := by
    unfold FW
    rw [hWidths]
    change (YIN + YW).toNat = YIN.toNat + YW.toNat
    exact Int.toNat_add
      (by simpa [SmtEval.native_zleq] using hYIN0)
      (by simpa [SmtEval.native_zleq] using hYW0)
  have hZX : ZX ≤ native_int_to_nat XIN :=
    bvExtractMultLeadingZeros_le _ _
  have hZY : ZY ≤ native_int_to_nat YIN :=
    bvExtractMultLeadingZeros_le _ _
  have hLowInt :
      2 * (XIN + XW) -
          (bvExtractMultLeadingZerosInt I XIN +
            bvExtractMultLeadingZerosInt J YIN) ≤ L := by
    simpa [SmtEval.native_zleq] using hLow
  change 2 * FW - (ZX + ZY) ≤ native_int_to_nat L
  have hFWCast : ((FW : Nat) : Int) = XIN + XW := by
    have hXINCast : ((native_int_to_nat XIN : Nat) : Int) = XIN := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXINRound
    have hXWCast : ((native_int_to_nat XW : Nat) : Int) = XW := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXWRound
    calc
      (FW : Int) =
          ((native_int_to_nat XIN + native_int_to_nat XW : Nat) : Int) := by
        exact_mod_cast hFWX
      _ = (native_int_to_nat XIN : Int) +
          (native_int_to_nat XW : Int) := by norm_cast
      _ = XIN + XW := by rw [hXINCast, hXWCast]
  have hLCast : ((native_int_to_nat L : Nat) : Int) = L := by
    simpa [native_int_to_nat, SmtEval.native_int_to_nat] using
      Int.toNat_of_nonneg (by simpa [SmtEval.native_zleq] using hL0)
  have hZXCast : ((ZX : Nat) : Int) =
      bvExtractMultLeadingZerosInt I XIN := by
    simpa [ZX] using hXZeros.symm
  have hZYCast : ((ZY : Nat) : Int) =
      bvExtractMultLeadingZerosInt J YIN := by
    simpa [ZY] using hYZeros.symm
  have hXINLeFW : native_int_to_nat XIN ≤ FW := by
    calc
      native_int_to_nat XIN ≤
          native_int_to_nat XIN + native_int_to_nat XW :=
        Nat.le_add_right _ _
      _ = FW := hFWX.symm
  have hYINLeFW : native_int_to_nat YIN ≤ FW := by
    calc
      native_int_to_nat YIN ≤
          native_int_to_nat YIN + native_int_to_nat YW :=
        Nat.le_add_right _ _
      _ = FW := hFWY.symm
  have hZLe : ZX + ZY ≤ 2 * FW := by
    calc
      ZX + ZY ≤ native_int_to_nat XIN + native_int_to_nat YIN :=
        Nat.add_le_add hZX hZY
      _ ≤ FW + FW := Nat.add_le_add hXINLeFW hYINLeFW
      _ = 2 * FW := (Nat.two_mul FW).symm
  have hSubCast := Int.natCast_sub hZLe
  have hAsInt : ((2 * FW - (ZX + ZY) : Nat) : Int) ≤
      ((native_int_to_nat L : Nat) : Int) := by
    calc
      ((2 * FW - (ZX + ZY) : Nat) : Int) =
          ((2 * FW : Nat) : Int) - ((ZX + ZY : Nat) : Int) := hSubCast
      _ = 2 * (FW : Int) - ((ZX : Int) + (ZY : Int)) := by norm_cast
      _ = 2 * (XIN + XW) -
          (bvExtractMultLeadingZerosInt I XIN +
            bvExtractMultLeadingZerosInt J YIN) := by
        rw [hFWCast, hZXCast, hZYCast]
      _ ≤ L := hLowInt
      _ = ((native_int_to_nat L : Nat) : Int) := hLCast.symm
  exact_mod_cast hAsInt

private theorem extractLead_eval_int_to_bv
    (M : SmtModel) (i : Term) (I W : native_Int)
    (hIEval :
      __smtx_model_eval M (__eo_to_smt i) = SmtValue.Numeral I)
    (hI0 : native_zleq 0 I = true)
    (hRange : native_zlt I (native_int_pow2 W) = true) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) i)) =
      SmtValue.Binary W I := by
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt i)) = _
  rw [smtx_eval_int_to_bv_term_eq, hIEval,
    __smtx_model_eval.eq_def]
  have hMod : native_mod_total I (native_int_pow2 W) = I := by
    exact Int.emod_eq_of_lt
      (by simpa [SmtEval.native_zleq] using hI0)
      (by simpa [SmtEval.native_zlt] using hRange)
  simp only [__smtx_model_eval_int_to_bv]
  rw [hMod]

private theorem extractLead_concat_nat_values
    {A B a b : Nat} (ha : a < 2 ^ A) (hb : b < 2 ^ B) :
    __smtx_model_eval_concat
        (SmtValue.Binary (A : Int) (a : Int))
        (SmtValue.Binary (B : Int) (b : Int)) =
      SmtValue.Binary ((A + B : Nat) : Int)
        ((a * 2 ^ B + b : Nat) : Int) := by
  simp only [__smtx_model_eval_concat, SmtEval.native_zplus,
    native_mod_total, native_binary_concat, native_zmult]
  have hWidth : (A : Int) + (B : Int) = ((A + B : Nat) : Int) := by
    norm_cast
  rw [hWidth, natpow2_eq B, natpow2_eq (A + B),
    show ((2 : Int) ^ B) = ((2 ^ B : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ (A + B)) = ((2 ^ (A + B) : Nat) : Int) by
      norm_cast]
  norm_cast
  have hBound : a * 2 ^ B + b < 2 ^ (A + B) := by
    calc
      a * 2 ^ B + b < a * 2 ^ B + 2 ^ B :=
        Nat.add_lt_add_left hb _
      _ = (a + 1) * 2 ^ B := by rw [Nat.add_mul]; simp
      _ ≤ 2 ^ A * 2 ^ B :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr ha)
      _ = 2 ^ (A + B) := by rw [Nat.pow_add]
  rw [Nat.mod_eq_of_lt hBound]

private theorem eval_bv_extract_mult_leading_raw
    (M : SmtModel) (hM : model_wf M)
    (high low xi xin x yi yin y w : Term) :
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation xi ->
    RuleProofs.eo_has_smt_translation xin ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation yi ->
    RuleProofs.eo_has_smt_translation yin ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof
        (bvExtractMultLeadingRaw high low xi xin x yi yin y w) =
      Term.Bool ->
    eo_interprets M (bvExtractMultLeadingNonnegPrem xi) true ->
    eo_interprets M (bvExtractMultLeadingRangePrem xi xin) true ->
    eo_interprets M (bvExtractMultLeadingNonnegPrem yi) true ->
    eo_interprets M (bvExtractMultLeadingRangePrem yi yin) true ->
    eo_interprets M
      (bvExtractMultLeadingLowPrem low xi xin x yi yin) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractMultLeadingRaw high low xi xin x yi yin y w)) =
      SmtValue.Boolean true := by
  intro hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
    hYTrans hWTrans hRawTy hXiNonnegPrem hXiRangePrem hYiNonnegPrem
    hYiRangePrem hLowPrem
  have hRawEq := bvExtractMultLeadingRaw_eq_direct
    high low xi xin x yi yin y w hRawTy
  have hDirectTy :
      __eo_typeof
          (bvExtractMultLeadingDirect high low xi xin x yi yin y w) =
        Term.Bool := by
    rw [← hRawEq]
    exact hRawTy
  rcases bvExtractMultLeading_context high low xi xin x yi yin y w
      hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
      hYTrans hWTrans hDirectTy with
    ⟨XIN, YIN, XW, YW, H, L, RW, rfl, rfl, rfl, rfl, rfl,
      hXIN0, hYIN0, hXW0, hYW0, hRW0, hWidths, hL0, _hHFull,
      _hResultPos, hRW, hXiSmtTy, hYiSmtTy, hXSmtTy, hYSmtTy,
      hNilEq, _hProductSmtTy⟩
  rcases extractLead_eval_int_term M hM xi hXiSmtTy with
    ⟨I, hIEval⟩
  rcases extractLead_eval_int_term M hM yi hYiSmtTy with
    ⟨J, hJEval⟩
  have hI0 := extractLead_nonneg_of_premise M xi I hIEval hXiNonnegPrem
  have hJ0 := extractLead_nonneg_of_premise M yi J hJEval hYiNonnegPrem
  have hIRange := extractLead_range_of_premise M xi I XIN hIEval
    hXiRangePrem
  have hJRange := extractLead_range_of_premise M yi J YIN hJEval
    hYiRangePrem
  have hLowInt := extractLead_low_of_premise M (Term.Numeral L) xi x yi
    L I J XIN YIN XW rfl hIEval hJEval hXSmtTy hXW0 hLowPrem
  let NX := native_int_to_nat XIN
  let NY := native_int_to_nat YIN
  let WX := native_int_to_nat XW
  let WY := native_int_to_nat YW
  let FW := native_int_to_nat (native_zplus XIN XW)
  let LN := native_int_to_nat L
  let RN := native_int_to_nat RW
  let IN := native_int_to_nat I
  let JN := native_int_to_nat J
  have hXINRound : native_nat_to_int NX = XIN := by
    simpa [NX] using native_int_to_nat_roundtrip XIN hXIN0
  have hYINRound : native_nat_to_int NY = YIN := by
    simpa [NY] using native_int_to_nat_roundtrip YIN hYIN0
  have hXWRound : native_nat_to_int WX = XW := by
    simpa [WX] using native_int_to_nat_roundtrip XW hXW0
  have hYWRound : native_nat_to_int WY = YW := by
    simpa [WY] using native_int_to_nat_roundtrip YW hYW0
  have hLRound : native_nat_to_int LN = L := by
    simpa [LN] using native_int_to_nat_roundtrip L hL0
  have hRWRound : native_nat_to_int RN = RW := by
    simpa [RN] using native_int_to_nat_roundtrip RW hRW0
  have hIRound : native_nat_to_int IN = I := by
    simpa [IN] using native_int_to_nat_roundtrip I hI0
  have hJRound : native_nat_to_int JN = J := by
    simpa [JN] using native_int_to_nat_roundtrip J hJ0
  have hFWX : FW = NX + WX := by
    unfold FW NX WX
    change (XIN + XW).toNat = XIN.toNat + XW.toNat
    exact Int.toNat_add
      (by simpa [SmtEval.native_zleq] using hXIN0)
      (by simpa [SmtEval.native_zleq] using hXW0)
  have hFWY : FW = NY + WY := by
    unfold FW NY WY
    rw [hWidths]
    change (YIN + YW).toNat = YIN.toNat + YW.toNat
    exact Int.toNat_add
      (by simpa [SmtEval.native_zleq] using hYIN0)
      (by simpa [SmtEval.native_zleq] using hYW0)
  have hFWRound : native_nat_to_int FW = native_zplus XIN XW := by
    calc
      native_nat_to_int FW = native_nat_to_int NX + native_nat_to_int WX := by
        simp [hFWX, native_nat_to_int, Smtm.native_nat_to_int]
      _ = XIN + XW := by rw [hXINRound, hXWRound]
      _ = native_zplus XIN XW := rfl
  have hIRangeNat : IN < 2 ^ NX := by
    have h : I < native_int_pow2 XIN := by
      simpa [SmtEval.native_zlt] using hIRange
    have hICast : ((IN : Nat) : Int) = I := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hIRound
    have hNXCast : ((NX : Nat) : Int) = XIN := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXINRound
    rw [← hICast, ← hNXCast] at h
    have hPow : native_int_pow2 (NX : Int) = (2 ^ NX : Nat) := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using
        native_int_pow2_nat NX
    rw [hPow] at h
    exact_mod_cast h
  have hJRangeNat : JN < 2 ^ NY := by
    have h : J < native_int_pow2 YIN := by
      simpa [SmtEval.native_zlt] using hJRange
    have hJCast : ((JN : Nat) : Int) = J := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hJRound
    have hNYCast : ((NY : Nat) : Int) = YIN := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using hYINRound
    rw [← hJCast, ← hNYCast] at h
    have hPow : native_int_pow2 (NY : Int) = (2 ^ NY : Nat) := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int] using
        native_int_pow2_nat NY
    rw [hPow] at h
    exact_mod_cast h
  rcases bitvec_eval_nat_payload M hM x WX (by simpa [WX] using hXSmtTy) with
    ⟨XV, hXEval, hXVBound⟩
  rcases bitvec_eval_nat_payload M hM y WY (by simpa [WY] using hYSmtTy) with
    ⟨YV, hYEval, hYVBound⟩
  let XP := IN * 2 ^ WX + XV
  let YP := JN * 2 ^ WY + YV
  have hXPBound : XP < 2 ^ FW := by
    rw [hFWX, Nat.pow_add]
    unfold XP
    calc
      IN * 2 ^ WX + XV < IN * 2 ^ WX + 2 ^ WX :=
        Nat.add_lt_add_left hXVBound _
      _ = (IN + 1) * 2 ^ WX := by rw [Nat.add_mul]; simp
      _ ≤ 2 ^ NX * 2 ^ WX :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hIRangeNat)
  have hYPBound : YP < 2 ^ FW := by
    rw [hFWY, Nat.pow_add]
    unfold YP
    calc
      JN * 2 ^ WY + YV < JN * 2 ^ WY + 2 ^ WY :=
        Nat.add_lt_add_left hYVBound _
      _ = (JN + 1) * 2 ^ WY := by rw [Nat.add_mul]; simp
      _ ≤ 2 ^ NY * 2 ^ WY :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hJRangeNat)
  let xb : BitVec FW := BitVec.ofNat FW XP
  let yb : BitVec FW := BitVec.ofNat FW YP
  have hXbToNat : xb.toNat = XP := by
    simp [xb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hXPBound]
  have hYbToNat : yb.toNat = YP := by
    simp [yb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hYPBound]
  have hXPrefixEval := extractLead_eval_int_to_bv M xi I XIN hIEval hI0
    hIRange
  have hYPrefixEval := extractLead_eval_int_to_bv M yi J YIN hJEval hJ0
    hJRange
  have hXTailEval :=
    (bvConcat_eval_right_empty M hM x WX (by simpa [WX] using hXSmtTy)).trans
      hXEval
  have hYTailEval :=
    (bvConcat_eval_right_empty M hM y WY (by simpa [WY] using hYSmtTy)).trans
      hYEval
  have hXFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractMultLeadingOperand xi (Term.Numeral XIN) x)) =
        SmtValue.Binary (FW : Int) (xb.toNat : Int) := by
    unfold bvExtractMultLeadingOperand extractLeadApp1 extractLeadApp2
    change __smtx_model_eval M
      (SmtTerm.concat
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral XIN)) xi))
        (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0))) = _
    rw [smtx_eval_concat_term_eq, hXPrefixEval,
      smtx_eval_concat_term_eq, hXEval, smtx_eval_binary_term_eq]
    rw [show XIN = (NX : Int) by simpa [native_nat_to_int,
      Smtm.native_nat_to_int] using hXINRound.symm]
    rw [show I = (IN : Int) by simpa [native_nat_to_int,
      Smtm.native_nat_to_int] using hIRound.symm]
    rw [concat_zero_right_value WX XV hXVBound]
    have hConcat := extractLead_concat_nat_values hIRangeNat hXVBound
    rw [hXbToNat]
    simpa [hXINRound, hXWRound, hIRound, hFWX, XP,
      native_nat_to_int, Smtm.native_nat_to_int] using hConcat
  have hYFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractMultLeadingOperand yi (Term.Numeral YIN) y)) =
        SmtValue.Binary (FW : Int) (yb.toNat : Int) := by
    unfold bvExtractMultLeadingOperand extractLeadApp1 extractLeadApp2
    change __smtx_model_eval M
      (SmtTerm.concat
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral YIN)) yi))
        (SmtTerm.concat (__eo_to_smt y) (SmtTerm.Binary 0 0))) = _
    rw [smtx_eval_concat_term_eq, hYPrefixEval,
      smtx_eval_concat_term_eq, hYEval, smtx_eval_binary_term_eq]
    rw [show YIN = (NY : Int) by simpa [native_nat_to_int,
      Smtm.native_nat_to_int] using hYINRound.symm]
    rw [show J = (JN : Int) by simpa [native_nat_to_int,
      Smtm.native_nat_to_int] using hJRound.symm]
    rw [concat_zero_right_value WY YV hYVBound]
    have hConcat := extractLead_concat_nat_values hJRangeNat hYVBound
    rw [hYbToNat]
    simpa [hYINRound, hYWRound, hJRound, hFWY, YP,
      native_nat_to_int, Smtm.native_nat_to_int] using hConcat
  have hNilEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_nil (Term.UOp UserOp.bvmul)
              (__eo_typeof
                (bvExtractMultLeadingOperand xi (Term.Numeral XIN) x)))) =
        SmtValue.Binary (FW : Int) ((1#FW).toNat : Int) := by
    rw [hNilEq]
    simpa [FW, native_nat_to_int, Smtm.native_nat_to_int] using
      eval_binary M
        (native_nat_to_int
          (native_int_to_nat (native_zplus XIN XW)))
        ((1#(native_int_to_nat (native_zplus XIN XW))).toNat : Int)
  have hInnerEval :
      __smtx_model_eval M
          (__eo_to_smt
            (extractLeadApp2 (Term.UOp UserOp.bvmul)
              (bvExtractMultLeadingOperand yi (Term.Numeral YIN) y)
              (__eo_nil (Term.UOp UserOp.bvmul)
                (__eo_typeof
                  (bvExtractMultLeadingOperand xi (Term.Numeral XIN) x))))) =
        SmtValue.Binary (FW : Int) (yb.toNat : Int) := by
    unfold extractLeadApp2
    rw [eval_bvmul_term M _ _ _ _ hYFullEval hNilEval,
      bvMultSlt_bvmul_bitvec_values]
    simp
  have hProductEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
              (Term.Numeral YIN) y)) =
        SmtValue.Binary (FW : Int) ((xb * yb).toNat : Int) := by
    change __smtx_model_eval M
      (SmtTerm.bvmul
        (__eo_to_smt
          (bvExtractMultLeadingOperand xi (Term.Numeral XIN) x))
        (__eo_to_smt
          (extractLeadApp2 (Term.UOp UserOp.bvmul)
            (bvExtractMultLeadingOperand yi (Term.Numeral YIN) y)
            (__eo_nil (Term.UOp UserOp.bvmul)
              (__eo_typeof
                (bvExtractMultLeadingOperand xi (Term.Numeral XIN) x)))))) = _
    rw [smtx_eval_bvmul_term_eq, hXFullEval, hInnerEval,
      bvMultSlt_bvmul_bitvec_values]
  have hLowNat := extractLead_low_nat I J XIN YIN XW YW L hI0 hJ0
    hXIN0 hYIN0 hXW0 hYW0 hL0 hWidths hIRange hJRange hLowInt
  have hProductZero :
      ((xb * yb).extractLsb' LN RN).toNat = 0 := by
    have hWXLe : WX ≤ FW := by
      rw [hFWX]
      exact Nat.le_add_left WX NX
    have hWYLe : WY ≤ FW := by
      rw [hFWY]
      exact Nat.le_add_left WY NY
    have hFWSubX : FW - WX = NX := by
      rw [hFWX, Nat.add_sub_cancel_right]
    have hFWSubY : FW - WY = NY := by
      rw [hFWY, Nat.add_sub_cancel_right]
    have hLowCore :
        2 * FW -
            (bvExtractMultLeadingZeros IN (FW - WX) +
              bvExtractMultLeadingZeros JN (FW - WY)) ≤ LN := by
      rw [hFWSubX, hFWSubY]
      simpa [FW, NX, NY, LN, IN, JN] using hLowNat
    have hCore := extract_mult_leading_bit_core
      (W := FW) (WX := WX) (WY := WY) (xi := IN) (yi := JN)
      (xv := XV) (yv := YV) (low := LN) (len := RN)
      hWXLe hWYLe
      (by simpa [hFWSubX] using hIRangeNat)
      (by simpa [hFWSubY] using hJRangeNat)
      hXVBound hYVBound hLowCore
    simpa [xb, yb, hXbToNat, hYbToNat, XP, YP] using hCore
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm
              (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
                (Term.Numeral YIN) y)
              (Term.Numeral H) (Term.Numeral L))) =
        SmtValue.Binary (RN : Int) 0 := by
    rw [eval_extract_term, hProductEval]
    have hVal := extract_val_bitvec_start_len FW LN RN
      ((xb * yb).toNat : Int) H L (Int.natCast_nonneg _)
      (by exact_mod_cast (xb * yb).isLt)
      (by simpa [native_nat_to_int, Smtm.native_nat_to_int] using
        hLRound.symm)
      (by
        have : H + 1 + -L = RW := by
          simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hRW.symm
        simpa [native_nat_to_int, Smtm.native_nat_to_int] using
          this.trans hRWRound.symm)
    rw [hVal, bitvec_ofInt_natCast_toNat, hProductZero]
    simp
  have hZeroEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral RW))
              (Term.Numeral 0))) =
        SmtValue.Binary (RN : Int) 0 := by
    change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral RW) (SmtTerm.Numeral 0)) = _
    rw [smtx_eval_int_to_bv_numerals]
    simp [← hRWRound, native_nat_to_int,
      Smtm.native_nat_to_int, SmtEval.native_mod_total]
  rw [hRawEq]
  change __smtx_model_eval M
      (SmtTerm.eq
        (__eo_to_smt
          (bvExtractTerm
            (bvExtractMultLeadingProduct xi (Term.Numeral XIN) x yi
              (Term.Numeral YIN) y)
            (Term.Numeral H) (Term.Numeral L)))
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral RW))
            (Term.Numeral 0)))) = SmtValue.Boolean true
  rw [smtx_eval_eq_term_eq, hExtractEval, hZeroEval]
  simp [__smtx_model_eval_eq, native_veq]

theorem facts_bv_extract_mult_leading_raw
    (M : SmtModel) (hM : model_wf M)
    (high low xi xin x yi yin y w : Term) :
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation xi ->
    RuleProofs.eo_has_smt_translation xin ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation yi ->
    RuleProofs.eo_has_smt_translation yin ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof
        (bvExtractMultLeadingRaw high low xi xin x yi yin y w) =
      Term.Bool ->
    eo_interprets M (bvExtractMultLeadingNonnegPrem xi) true ->
    eo_interprets M (bvExtractMultLeadingRangePrem xi xin) true ->
    eo_interprets M (bvExtractMultLeadingNonnegPrem yi) true ->
    eo_interprets M (bvExtractMultLeadingRangePrem yi yin) true ->
    eo_interprets M
      (bvExtractMultLeadingLowPrem low xi xin x yi yin) true ->
    eo_interprets M
      (bvExtractMultLeadingRaw high low xi xin x yi yin y w) true := by
  intro hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
    hYTrans hWTrans hRawTy hXiNonnegPrem hXiRangePrem hYiNonnegPrem
    hYiRangePrem hLowPrem
  exact RuleProofs.eo_interprets_of_bool_eval M _ true
    (typed_bvExtractMultLeadingRaw high low xi xin x yi yin y w
      hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
      hYTrans hWTrans hRawTy)
    (eval_bv_extract_mult_leading_raw M hM high low xi xin x yi yin y w
      hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
      hYTrans hWTrans hRawTy hXiNonnegPrem hXiRangePrem hYiNonnegPrem
      hYiRangePrem hLowPrem)
