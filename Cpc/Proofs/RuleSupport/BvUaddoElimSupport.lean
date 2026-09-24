module

public import Cpc.Proofs.RuleSupport.BvUsuboElimSupport
import all Cpc.Proofs.RuleSupport.BvUsuboElimSupport

public section

/-! Support for the `bv_uaddo_eliminate` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def uaddoZeroBit : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)

def uaddoOneBit : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)

def uaddoExt (x : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat) uaddoZeroBit)
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) (Term.Binary 0 0))

def uaddoNil (x : Term) : Term :=
  __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof (uaddoExt x))

def uaddoSum (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) (uaddoExt x))
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) (uaddoExt y))
      (uaddoNil x))

def uaddoBit (x y n : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract n n) (uaddoSum x y)

def uaddoRhs (x y n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (uaddoBit x y n))
    uaddoOneBit

def uaddoLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) x) y

def uaddoTerm (x y n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (uaddoLhs x y))
    (uaddoRhs x y n)

def uaddoPrem (x n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) n)
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)

theorem typeof_uaddo_ext (x : Term) (w : Nat)
    (hx : __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    __eo_typeof (uaddoExt x) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1))) := by
  have hZeroTy :
      __eo_typeof uaddoZeroBit =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    native_decide
  unfold uaddoExt
  change __eo_typeof_concat (__eo_typeof uaddoZeroBit)
      (__eo_typeof_concat (__eo_typeof x) (__eo_typeof (Term.Binary 0 0))) = _
  rw [hZeroTy, hx]
  change __eo_mk_apply (Term.UOp UserOp.BitVec)
      (__eo_add (Term.Numeral 1)
        (__eo_add (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0))) = _
  have hInner :
      __eo_add (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Numeral (native_nat_to_int w) := by
    simp [__eo_add, SmtEval.native_zplus, native_nat_to_int]
  have hOuter :
      __eo_add (Term.Numeral 1) (Term.Numeral (native_nat_to_int w)) =
        Term.Numeral (native_nat_to_int (w + 1)) := by
    have h : (1 : Int) + (w : Int) = ((w + 1 : Nat) : Int) := by omega
    simp [__eo_add, SmtEval.native_zplus, native_nat_to_int, h]
  rw [hInner, hOuter]
  rfl

theorem smt_typeof_uaddo_ext (x : Term) (w : Nat)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __smtx_typeof (__eo_to_smt (uaddoExt x)) =
      SmtType.BitVec (w + 1) := by
  have hZeroTy :
      __smtx_typeof (__eo_to_smt uaddoZeroBit) = SmtType.BitVec 1 := by
    simpa [uaddoZeroBit, native_int_to_nat, SmtEval.native_int_to_nat]
      using smt_typeof_bv_const 0 1 (by decide)
  have hEmptyTy :
      __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0 := by
    native_decide
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0)) =
        SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def]
    simp only
    simp [__smtx_typeof_concat, hx, hEmptyTy,
      Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      Smtm.native_nateq, SmtEval.native_zplus, native_ite]
  change __smtx_typeof
      (SmtTerm.concat (__eo_to_smt uaddoZeroBit)
        (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0))) = _
  rw [__smtx_typeof.eq_def]
  simp only
  simp only [__smtx_typeof_concat, hZeroTy, hInnerTy]
  simp [SmtEval.native_int_to_nat, Smtm.native_nat_to_int,
    SmtEval.native_zplus, native_int_to_nat, native_nat_to_int]
  have hCast : (1 : Int) + (w : Int) = ((w + 1 : Nat) : Int) := by omega
  rw [hCast]
  simp

theorem uaddo_nil_ne (x y n : Term) :
    __eo_typeof (uaddoTerm x y n) = Term.Bool ->
    uaddoNil x ≠ Term.Stuck := by
  intro hTy hNil
  have hRhsNe : __eo_typeof (uaddoRhs x y n) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hTy; (try simp [uaddoTerm] at hsimpa ⊢); exact hsimpa)).2
  have hBitNe : __eo_typeof (uaddoBit x y n) ≠ Term.Stuck := by
    intro hBit
    apply hRhsNe
    unfold uaddoRhs
    change __eo_typeof_eq (__eo_typeof (uaddoBit x y n))
      (__eo_typeof uaddoOneBit) = Term.Stuck
    rw [hBit]
    simp [__eo_typeof_eq]
  apply hBitNe
  unfold uaddoBit uaddoSum
  rw [show uaddoNil x = Term.Stuck from hNil]
  change __eo_typeof_extract (__eo_typeof n) n (__eo_typeof n) n
      (__eo_typeof_bvand (__eo_typeof (uaddoExt x))
        (__eo_typeof_bvand (__eo_typeof (uaddoExt y)) Term.Stuck)) =
    Term.Stuck
  simp [__eo_typeof_bvand]
  unfold __eo_typeof_extract
  split <;> simp_all

theorem uaddo_nil_eq_zero (x : Term) (w : Nat)
    (hExtTy : __eo_typeof (uaddoExt x) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1))))
    (hNilNe : uaddoNil x ≠ Term.Stuck) :
    uaddoNil x = Term.Binary (native_nat_to_int (w + 1)) 0 := by
  unfold uaddoNil
  rw [hExtTy]
  change __eo_to_bin (Term.Numeral (native_nat_to_int (w + 1)))
      (Term.Numeral 0) = _
  by_cases hBound : native_zleq (native_nat_to_int (w + 1)) 4294967296 = true
  · have hBoundProp : native_nat_to_int (w + 1) <= 4294967296 := by
      simpa [SmtEval.native_zleq] using hBound
    have hWidthNonneg : 0 <= native_nat_to_int (w + 1) := by
      simpa [native_nat_to_int] using (Int.natCast_nonneg (w + 1))
    simp [__eo_to_bin, __eo_mk_binary, native_ite, SmtEval.native_zleq,
      hBoundProp, hWidthNonneg, SmtEval.native_mod_total]
  · have hStuck :
        __eo_to_bin (Term.Numeral (native_nat_to_int (w + 1)))
            (Term.Numeral 0) = Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int (w + 1) <= 4294967296 := by
        simpa [SmtEval.native_zleq] using hBound
      simp [__eo_to_bin, hBoundFalse, native_ite, SmtEval.native_zleq]
    exact False.elim (hNilNe (by have hsimpa := hStuck; (try simp [uaddoNil, hExtTy] at hsimpa ⊢); exact hsimpa))

theorem smt_typeof_uaddo_nil (x : Term) (w : Nat)
    (hNilEq : uaddoNil x = Term.Binary (native_nat_to_int (w + 1)) 0) :
    __smtx_typeof (__eo_to_smt (uaddoNil x)) = SmtType.BitVec (w + 1) := by
  rw [hNilEq]
  change __smtx_typeof (SmtTerm.Binary (native_nat_to_int (w + 1)) 0) =
    SmtType.BitVec (w + 1)
  have hWidth : native_zleq 0 (native_nat_to_int (w + 1)) = true := by
    have hNonneg : (0 : Int) <= native_nat_to_int (w + 1) := by
      simpa [native_nat_to_int] using (Int.natCast_nonneg (w + 1))
    simpa [SmtEval.native_zleq] using hNonneg
  have hMod :
      native_zeq 0
          (native_mod_total 0
            (native_int_pow2 (native_nat_to_int (w + 1)))) = true := by
    simp [SmtEval.native_zeq, SmtEval.native_mod_total]
  rw [__smtx_typeof.eq_def]
  simp only
  simp [hWidth, hMod, SmtEval.native_and, native_ite,
    SmtEval.native_int_to_nat, Smtm.native_nat_to_int]
  exact ⟨hWidth, hMod⟩

theorem smt_typeof_uaddo_sum (x y : Term) (w : Nat)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hNilEq : uaddoNil x = Term.Binary (native_nat_to_int (w + 1)) 0) :
    __smtx_typeof (__eo_to_smt (uaddoSum x y)) =
      SmtType.BitVec (w + 1) := by
  have hxExt := smt_typeof_uaddo_ext x w hx
  have hyExt := smt_typeof_uaddo_ext y w hy
  have hNilTy := smt_typeof_uaddo_nil x w hNilEq
  have hInner :
      __smtx_typeof
          (SmtTerm.bvadd (__eo_to_smt (uaddoExt y))
            (__eo_to_smt (uaddoNil x))) = SmtType.BitVec (w + 1) := by
    apply smt_typeof_bvbin_same SmtTerm.bvadd
      (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ (w + 1) hyExt hNilTy
  change __smtx_typeof
      (SmtTerm.bvadd (__eo_to_smt (uaddoExt x))
        (SmtTerm.bvadd (__eo_to_smt (uaddoExt y))
          (__eo_to_smt (uaddoNil x)))) = _
  apply smt_typeof_bvbin_same SmtTerm.bvadd
    (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
    _ _ (w + 1) hxExt hInner

theorem uaddo_context (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (uaddoTerm x y n) = Term.Bool ->
    ∃ w i : native_Int,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      n = Term.Numeral i ∧
      native_zleq 0 w = true ∧ native_zleq 0 i = true ∧
      native_zlt i
        (native_nat_to_int (native_int_to_nat w + 1)) = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat w) ∧
      uaddoNil x ≠ Term.Stuck := by
  intro hXTrans hYTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult (__eo_typeof x) (__eo_typeof y))
      (__eo_typeof (uaddoRhs x y n)) = Term.Bool at hResultTy
  have hOps := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy
  rcases typeof_bvult_args_of_ne_stuck hOps.1 with
    ⟨widthTerm, hXTy, hYTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width x widthTerm
      hXTrans hXTy with ⟨w, hWidth, hw0, hXSmtTy⟩
  subst widthTerm
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat w) := by
    have hsimpa :=
      (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        y (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
        (__eo_to_smt y) rfl hYTrans hYTy)
    try simp [__eo_to_smt_type, hw0] at hsimpa ⊢
    exact hsimpa
  have hLeftTy : __eo_typeof (uaddoLhs x y) = Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool
    rw [hXTy, hYTy]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hRhsTy : __eo_typeof (uaddoRhs x y n) = Term.Bool := by
    have hLeftTy' :
        __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool := by
      have hsimpa := hLeftTy
      try simp [uaddoLhs] at hsimpa ⊢
      exact hsimpa
    rw [hLeftTy'] at hTypeEq
    exact hTypeEq.symm
  have hBitNe : __eo_typeof (uaddoBit x y n) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hRhsTy; (try simp [uaddoRhs] at hsimpa ⊢); exact hsimpa)).1
  let W := native_int_to_nat w
  have hRound : native_nat_to_int W = w :=
    native_nat_to_int_int_to_nat_eq w hw0
  have hXTyW :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int W)) := by
    simpa [W, hRound] using hXTy
  have hExtTy := typeof_uaddo_ext x W hXTyW
  have hNilNe := uaddo_nil_ne x y n (by have hsimpa := hResultTy; (try simp [uaddoTerm] at hsimpa ⊢); exact hsimpa)
  have hNilEq := uaddo_nil_eq_zero x W hExtTy hNilNe
  have hSumSmtTy :
      __smtx_typeof (__eo_to_smt (uaddoSum x y)) =
        SmtType.BitVec (W + 1) :=
    smt_typeof_uaddo_sum x y W
      (by simpa [W] using hXSmtTy) (by simpa [W] using hYSmtTy) hNilEq
  have hSumTrans : RuleProofs.eo_has_smt_translation (uaddoSum x y) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSumSmtTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck (uaddoSum x y) n n
      hSumTrans (by have hsimpa := hBitNe; (try simp [uaddoBit] at hsimpa ⊢); exact hsimpa) with
    ⟨ws, hi, lo, _hSumEoTy, hNHi, hNLo, hws0, hlo0, hiws,
      _hExtractWidth0, hSumSmtTy'⟩
  have hLo : lo = hi := by
    rw [hNHi] at hNLo
    injection hNLo with h
    exact h.symm
  subst lo
  have hWsNat : native_int_to_nat ws = W + 1 := by
    rw [hSumSmtTy] at hSumSmtTy'
    exact (SmtType.BitVec.inj hSumSmtTy').symm
  have hWs : ws = native_nat_to_int (W + 1) := by
    have hWsRound := native_nat_to_int_int_to_nat_eq ws hws0
    rw [hWsNat] at hWsRound
    exact hWsRound.symm
  subst ws
  exact ⟨w, hi, hXTy, hYTy, hNHi, hw0, hlo0, hiws,
    hXSmtTy, hYSmtTy, hNilNe⟩

theorem typed_uaddo_term (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (uaddoTerm x y n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (uaddoTerm x y n) := by
  intro hXTrans hYTrans hResultTy
  rcases uaddo_context x y n hXTrans hYTrans hResultTy with
    ⟨w, i, hXTy, _hYTy, rfl, hw0, hi0, hiLt,
      hXSmtTy, hYSmtTy, hNilNe⟩
  let W := native_int_to_nat w
  have hRound : native_nat_to_int W = w :=
    native_nat_to_int_int_to_nat_eq w hw0
  have hXTyW :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int W)) := by
    simpa [W, hRound] using hXTy
  have hNilEq := uaddo_nil_eq_zero x W
    (typeof_uaddo_ext x W hXTyW) hNilNe
  have hXSmtTyW : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  have hLhsBool : RuleProofs.eo_has_bool_type (uaddoLhs x y) := by
    change __smtx_typeof
      (SmtTerm.bvuaddo (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
    simp only
    simp [__smtx_typeof_bv_op_2_ret, hXSmtTyW, hYSmtTyW,
      Smtm.native_nateq, native_ite]
  have hSumSmtTy :=
    smt_typeof_uaddo_sum x y W hXSmtTyW hYSmtTyW hNilEq
  have hBitSmtTy :
      __smtx_typeof
          (__eo_to_smt (uaddoBit x y (Term.Numeral i))) =
        SmtType.BitVec 1 := by
    change __smtx_typeof
      (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral i)
        (__eo_to_smt (uaddoSum x y))) = _
    rw [__smtx_typeof.eq_def]
    simp only
    rw [hSumSmtTy]
    have hiLtW : native_zlt i (native_nat_to_int (W + 1)) = true := by
      simpa [W] using hiLt
    have hOne : native_zplus (native_zplus i 1) (native_zneg i) = 1 := by
      simp [SmtEval.native_zplus, SmtEval.native_zneg]
      rw [Int.add_comm i 1]
      exact Int.add_neg_cancel_right 1 i
    unfold __smtx_typeof_extract
    simp only
    rw [hi0, hiLtW, hOne]
    native_decide
  have hOneTy :
      __smtx_typeof (__eo_to_smt uaddoOneBit) = SmtType.BitVec 1 := by
    simpa [uaddoOneBit, native_int_to_nat, SmtEval.native_int_to_nat]
      using smt_typeof_bv_const 1 1 (by decide)
  have hRhsBool : RuleProofs.eo_has_bool_type
      (uaddoRhs x y (Term.Numeral i)) := by
    unfold uaddoRhs
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hBitSmtTy.trans hOneTy.symm)
      (by rw [hBitSmtTy]; intro h; cases h)
  unfold uaddoTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

def extendedAddPayload (A B : Nat) : Nat := A + B

theorem extended_add_payload_lt (w A B : Nat)
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    extendedAddPayload A B < 2 ^ (w + 1) := by
  unfold extendedAddPayload
  rw [Nat.pow_succ]
  omega

theorem extended_add_payload_bit (w A B : Nat)
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    (extendedAddPayload A B).testBit w = decide (2 ^ w ≤ A + B) := by
  have hHi := extended_add_payload_lt w A B ha hb
  unfold extendedAddPayload
  by_cases hOverflow : 2 ^ w ≤ A + B
  · rw [decide_eq_true hOverflow]
    exact bit_w_of_range hOverflow hHi
  · rw [decide_eq_false hOverflow]
    apply Bool.eq_false_iff.mpr
    intro hBit
    exact hOverflow (Nat.ge_two_pow_of_testBit hBit)

theorem eval_uaddo_ext
    (M : SmtModel) (x : Term) (w A : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (ha : A < 2 ^ w) :
    __smtx_model_eval M (__eo_to_smt (uaddoExt x)) =
      SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) := by
  have hZeroEval :
      __smtx_model_eval M (__eo_to_smt uaddoZeroBit) =
        SmtValue.Binary 1 0 := by
    have h := eval_bv_const M 0 1 (by decide)
    simpa [uaddoZeroBit, SmtEval.native_mod_total] using h
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := by
    change __smtx_model_eval M (SmtTerm.Binary 0 0) = SmtValue.Binary 0 0
    simp only [__smtx_model_eval]
  have hInner := eval_concat_term M x (Term.Binary 0 0)
    (SmtValue.Binary (native_nat_to_int w) (A : Int))
    (SmtValue.Binary 0 0) hx hEmptyEval
  have hInner' :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x)
              (Term.Binary 0 0))) =
        SmtValue.Binary (native_nat_to_int w) (A : Int) := by
    rw [hInner]
    exact concat_zero_right_value w A ha
  have hOuter := eval_concat_term M uaddoZeroBit
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) (Term.Binary 0 0))
    (SmtValue.Binary 1 0)
    (SmtValue.Binary (native_nat_to_int w) (A : Int))
    hZeroEval hInner'
  simpa [uaddoExt] using hOuter.trans (concat_zero_left_value w A ha)

theorem eval_uaddo_nil
    (M : SmtModel) (x : Term) (w : Nat)
    (hNilEq : uaddoNil x = Term.Binary (native_nat_to_int (w + 1)) 0) :
    __smtx_model_eval M (__eo_to_smt (uaddoNil x)) =
      SmtValue.Binary (native_nat_to_int (w + 1)) 0 := by
  rw [hNilEq]
  change __smtx_model_eval M (SmtTerm.Binary (native_nat_to_int (w + 1)) 0) = _
  simp only [__smtx_model_eval]

theorem eval_bvadd_extended (w A B : Nat)
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    __smtx_model_eval_bvadd
        (SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int))
        (__smtx_model_eval_bvadd
          (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))
          (SmtValue.Binary (native_nat_to_int (w + 1)) 0)) =
      SmtValue.Binary (native_nat_to_int (w + 1))
        (extendedAddPayload A B : Int) := by
  have hBWide : B < 2 ^ (w + 1) :=
    Nat.lt_trans hb (Nat.pow_lt_pow_right (by decide) (by omega))
  have hSumWide := extended_add_payload_lt w A B ha hb
  have hBMod :
      native_mod_total (B : Int)
          (native_int_pow2 (native_nat_to_int (w + 1))) = (B : Int) := by
    rw [native_int_pow2_nat]
    exact native_mod_nat_of_lt (Nat.two_pow_pos _) hBWide
  have hSumMod :
      native_mod_total ((A + B : Nat) : Int)
          (native_int_pow2 (native_nat_to_int (w + 1))) =
        ((A + B : Nat) : Int) := by
    rw [native_int_pow2_nat]
    exact native_mod_nat_of_lt (Nat.two_pow_pos _) hSumWide
  have hSumMod' :
      native_mod_total ((A : Int) + (B : Int))
          (native_int_pow2 (native_nat_to_int (w + 1))) =
        (A : Int) + (B : Int) := by
    simpa using hSumMod
  change SmtValue.Binary (native_nat_to_int (w + 1))
      (native_mod_total
        (native_zplus (A : Int)
          (native_mod_total (native_zplus (B : Int) 0)
            (native_int_pow2 (native_nat_to_int (w + 1)))))
        (native_int_pow2 (native_nat_to_int (w + 1)))) = _
  simp [SmtEval.native_zplus, hBMod, hSumMod', extendedAddPayload]

theorem smtx_eval_bvadd_term_eq_uaddo
    (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvadd a b) =
      __smtx_model_eval_bvadd
        (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

theorem eval_uaddo_sum
    (M : SmtModel) (x y : Term) (w A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (ha : A < 2 ^ w) (hb : B < 2 ^ w)
    (hNilEq : uaddoNil x = Term.Binary (native_nat_to_int (w + 1)) 0) :
    __smtx_model_eval M (__eo_to_smt (uaddoSum x y)) =
      SmtValue.Binary (native_nat_to_int (w + 1))
        (extendedAddPayload A B : Int) := by
  change __smtx_model_eval M
      (SmtTerm.bvadd (__eo_to_smt (uaddoExt x))
        (SmtTerm.bvadd (__eo_to_smt (uaddoExt y))
          (__eo_to_smt (uaddoNil x)))) = _
  rw [smtx_eval_bvadd_term_eq_uaddo,
    smtx_eval_bvadd_term_eq_uaddo]
  rw [eval_uaddo_ext M x w A hx ha, eval_uaddo_ext M y w B hy hb,
    eval_uaddo_nil M x w hNilEq]
  exact eval_bvadd_extended w A B ha hb

theorem eval_uaddo_rhs
    (M : SmtModel) (x y : Term) (w A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (ha : A < 2 ^ w) (hb : B < 2 ^ w)
    (hNilEq : uaddoNil x = Term.Binary (native_nat_to_int (w + 1)) 0) :
    __smtx_model_eval M
        (__eo_to_smt
          (uaddoRhs x y (Term.Numeral (native_nat_to_int w)))) =
      SmtValue.Boolean (decide (2 ^ w ≤ A + B)) := by
  have hSum := eval_uaddo_sum M x y w A B hx hy ha hb hNilEq
  have hBit := eval_extract_bit_term M (uaddoSum x y)
    (native_nat_to_int (w + 1)) (extendedAddPayload A B : Int) w
    hSum (by omega)
  have hOne :
      __smtx_model_eval M (__eo_to_smt uaddoOneBit) =
        SmtValue.Binary 1 1 := by
    have h := eval_bv_const M 1 1 (by decide)
    have hsimpa := h
    try simp [uaddoOneBit, SmtEval.native_mod_total] at hsimpa ⊢
    exact hsimpa
  unfold uaddoRhs
  change __smtx_model_eval M
      (SmtTerm.eq
        (__eo_to_smt
          (uaddoBit x y (Term.Numeral (native_nat_to_int w))))
        (__eo_to_smt uaddoOneBit)) = _
  rw [smtx_eval_eq_term_eq, hOne]
  rw [show __smtx_model_eval M
      (__eo_to_smt
        (uaddoBit x y (Term.Numeral (native_nat_to_int w)))) =
      bv1 ((extendedAddPayload A B).testBit w) by
        simpa [uaddoBit] using hBit]
  rw [bv1_eq_one, extended_add_payload_bit w A B ha hb]

theorem eval_uaddo_lhs
    (M : SmtModel) (x y : Term) (w A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int w) (B : Int)) :
    __smtx_model_eval M (__eo_to_smt (uaddoLhs x y)) =
      SmtValue.Boolean (decide (2 ^ w ≤ A + B)) := by
  change __smtx_model_eval M
      (SmtTerm.bvuaddo (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def]
  simp only
  rw [hx, hy]
  change SmtValue.Boolean
      (native_zleq (native_int_pow2 (native_nat_to_int w))
        (native_zplus (A : Int) (B : Int))) = _
  rw [native_int_pow2_nat]
  congr 1
  simp [SmtEval.native_zleq, SmtEval.native_zplus]
  norm_cast

theorem uaddo_index_eq_of_premise
    (M : SmtModel) (x : Term) (w i : native_Int) :
    eo_interprets M (uaddoPrem x (Term.Numeral i)) true ->
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    i = w := by
  intro hPrem hw0 hXSmtTy
  exact usubo_index_eq_of_premise M x w i
    (by simpa [uaddoPrem, usuboPrem] using hPrem) hw0 hXSmtTy

theorem facts_uaddo_term
    (M : SmtModel) (hM : model_wf M) (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    eo_interprets M (uaddoPrem x n) true ->
    __eo_typeof (uaddoTerm x y n) = Term.Bool ->
    eo_interprets M (uaddoTerm x y n) true := by
  intro hXTrans hYTrans hPrem hResultTy
  rcases uaddo_context x y n hXTrans hYTrans hResultTy with
    ⟨w, i, hXTy, _hYTy, rfl, hw0, _hi0, _hiLt,
      hXSmtTy, hYSmtTy, hNilNe⟩
  have hIndex := uaddo_index_eq_of_premise M x w i hPrem hw0 hXSmtTy
  subst i
  let W := native_int_to_nat w
  have hRound : native_nat_to_int W = w :=
    native_nat_to_int_int_to_nat_eq w hw0
  have hXSmtTyW : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  rcases bitvec_eval_nat_payload M hM x W hXSmtTyW with
    ⟨A, hXEval, hABound⟩
  rcases bitvec_eval_nat_payload M hM y W hYSmtTyW with
    ⟨B, hYEval, hBBound⟩
  have hXTyW :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int W)) := by
    simpa [W, hRound] using hXTy
  have hNilEq := uaddo_nil_eq_zero x W
    (typeof_uaddo_ext x W hXTyW) hNilNe
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (uaddoLhs x y)) =
        SmtValue.Boolean (decide (2 ^ W ≤ A + B)) :=
    eval_uaddo_lhs M x y W A B hXEval hYEval
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt (uaddoRhs x y (Term.Numeral w))) =
        SmtValue.Boolean (decide (2 ^ W ≤ A + B)) := by
    simpa [hRound] using
      eval_uaddo_rhs M x y W A B hXEval hYEval hABound hBBound hNilEq
  have hBool := typed_uaddo_term x y (Term.Numeral w)
    hXTrans hYTrans hResultTy
  unfold uaddoTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [uaddoTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (uaddoLhs x y)))
      (__smtx_model_eval M
        (__eo_to_smt (uaddoRhs x y (Term.Numeral w))))
    rw [hLhsEval, hRhsEval]
    exact RuleProofs.smt_value_rel_refl _

def uaddoProgram (x y n : Term) : Term :=
  __eo_prog_bv_uaddo_eliminate x y n (Proof.pf (uaddoPrem x n))

private def uaddoProgramSkeleton (x y n : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) (uaddoLhs x y))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (__eo_mk_apply (Term.UOp2 UserOp2.extract n n)
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.bvadd) (uaddoExt x))
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.bvadd) (uaddoExt y))
              (uaddoNil x)))))
      uaddoOneBit)

private theorem uaddo_program_eq_skeleton_of_ne_stuck (x y n : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> n ≠ Term.Stuck ->
    uaddoProgram x y n = uaddoProgramSkeleton x y n := by
  intro hXNe hYNe hNNe
  unfold uaddoProgram uaddoPrem
  rw [__eo_prog_bv_uaddo_eliminate.eq_4 x y n n x hXNe hYNe hNNe]
  simp [uaddoProgramSkeleton, uaddoLhs, uaddoExt, uaddoNil,
    uaddoZeroBit, uaddoOneBit, __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, SmtEval.native_and, hXNe, hNNe]

theorem uaddo_program_eq_term_of_type_bool (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation n ->
    __eo_typeof (uaddoProgram x y n) = Term.Bool ->
    uaddoProgram x y n = uaddoTerm x y n := by
  intro hXTrans hYTrans hNTrans hTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hSkeleton :=
    uaddo_program_eq_skeleton_of_ne_stuck x y n hXNe hYNe hNNe
  by_cases hNil : uaddoNil x = Term.Stuck
  · have hProgStuck : uaddoProgram x y n = Term.Stuck := by
      rw [hSkeleton]
      simp [uaddoProgramSkeleton, __eo_mk_apply, hNil]
    rw [hProgStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by native_decide
    exact False.elim (hBad hTy)
  · rw [hSkeleton]
    simp [uaddoProgramSkeleton, uaddoTerm, uaddoLhs, uaddoRhs,
      uaddoBit, uaddoSum, uaddoOneBit, __eo_mk_apply, hNil]

theorem uaddo_shape_of_ne_stuck (x y n P : Term) :
    __eo_prog_bv_uaddo_eliminate x y n (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck ∧ n ≠ Term.Stuck ∧
      ∃ pn px, P = uaddoPrem px pn := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_uaddo_eliminate.eq_1 y n (Proof.pf P))
  have hYNe : y ≠ Term.Stuck := by
    intro hY
    subst y
    exact hProg
      (__eo_prog_bv_uaddo_eliminate.eq_2 x n (Proof.pf P) hXNe)
  have hNNe : n ≠ Term.Stuck := by
    intro hN
    subst n
    exact hProg
      (__eo_prog_bv_uaddo_eliminate.eq_3 x y (Proof.pf P) hXNe hYNe)
  refine ⟨hXNe, hYNe, hNNe, ?_⟩
  by_cases hShape : ∃ pn px, P = uaddoPrem px pn
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_uaddo_eliminate.eq_5 x y n (Proof.pf P)
        hXNe hYNe hNNe (by
          intro pn px hP
          cases hP
          exact hShape ⟨pn, px, rfl⟩)))

theorem typed_uaddo_program (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation n ->
    __eo_typeof (uaddoProgram x y n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (uaddoProgram x y n) := by
  intro hXTrans hYTrans hNTrans hResultTy
  have hEq := uaddo_program_eq_term_of_type_bool x y n
    hXTrans hYTrans hNTrans hResultTy
  have hTermTy : __eo_typeof (uaddoTerm x y n) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_uaddo_term x y n hXTrans hYTrans hTermTy

theorem facts_uaddo_program
    (M : SmtModel) (hM : model_wf M) (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation n ->
    eo_interprets M (uaddoPrem x n) true ->
    __eo_typeof (uaddoProgram x y n) = Term.Bool ->
    eo_interprets M (uaddoProgram x y n) true := by
  intro hXTrans hYTrans hNTrans hPrem hResultTy
  have hEq := uaddo_program_eq_term_of_type_bool x y n
    hXTrans hYTrans hNTrans hResultTy
  have hTermTy : __eo_typeof (uaddoTerm x y n) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_uaddo_term M hM x y n hXTrans hYTrans hPrem hTermTy
