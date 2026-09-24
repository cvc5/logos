module

public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport
public import Cpc.Proofs.RuleSupport.BvSdivElimSupport
import all Cpc.Proofs.RuleSupport.BvSdivElimSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

public section

/-! Support for the `bv_usubo_eliminate` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem emod_sub_nat (w A B : Nat)
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    ((A : Int) - (B : Int)) % (2 ^ (w + 1) : Nat) =
      ((if A < B then 2 ^ (w + 1) + A - B else A - B : Nat) : Int) := by
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by
    simp [Nat.pow_succ, Nat.mul_comm]
  by_cases hlt : A < B
  · simp only [hlt, if_true]
    have hBLe : B ≤ 2 ^ (w + 1) + A := by omega
    have hCast :
        ((2 ^ (w + 1) + A - B : Nat) : Int) =
          (2 ^ (w + 1) : Nat) + ((A : Int) - (B : Int)) := by
      rw [Int.ofNat_sub hBLe]
      simp
      omega
    rw [hCast]
    have hCongr :
        ((A : Int) - (B : Int)) % (2 ^ (w + 1) : Nat) =
          ((2 ^ (w + 1) : Nat) + ((A : Int) - (B : Int))) %
            (2 ^ (w + 1) : Nat) := by
      rw [Int.add_emod]
      simp
    rw [hCongr]
    apply Int.emod_eq_of_lt
    · omega
    · omega
  · simp only [hlt, if_false]
    have hBA : B ≤ A := Nat.le_of_not_gt hlt
    have hCast : ((A - B : Nat) : Int) = (A : Int) - (B : Int) := by
      rw [Int.ofNat_sub hBA]
    rw [hCast]
    apply Int.emod_eq_of_lt
    · omega
    · omega

def extendedSubPayload (w A B : Nat) : Nat :=
  if A < B then 2 ^ (w + 1) + A - B else A - B

theorem extended_sub_payload_lt (w A B : Nat)
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    extendedSubPayload w A B < 2 ^ (w + 1) := by
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by
    simp [Nat.pow_succ, Nat.mul_comm]
  unfold extendedSubPayload
  by_cases hlt : A < B <;> simp only [hlt, if_true, if_false] <;> omega

theorem extended_sub_payload_bit (w A B : Nat)
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    (extendedSubPayload w A B).testBit w = decide (A < B) := by
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by
    simp [Nat.pow_succ, Nat.mul_comm]
  unfold extendedSubPayload
  by_cases hlt : A < B
  · simp only [hlt, if_true, decide_true]
    apply bit_w_of_range
    · omega
    · omega
  · simp only [hlt, if_false, decide_false]
    apply Bool.eq_false_iff.mpr
    intro hbit
    have hge := Nat.ge_two_pow_of_testBit hbit
    omega

theorem eval_bvsub_extended (w A B : Nat)
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    __smtx_model_eval_bvsub
        (SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int))
        (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int)) =
      SmtValue.Binary (native_nat_to_int (w + 1))
        (extendedSubPayload w A B : Int) := by
  have hpow := native_int_pow2_nat (w + 1)
  have haWide : A < 2 ^ (w + 1) := by
    have hpowStep : 2 ^ (w + 1) = 2 * 2 ^ w := by
      simp [Nat.pow_succ, Nat.mul_comm]
    omega
  have hAmod : (A : Int) % (2 ^ (w + 1) : Nat) = (A : Int) := by
    apply Int.emod_eq_of_lt
    · omega
    · exact_mod_cast haWide
  have hNested :
      ((A : Int) + ((-(B : Int)) % (2 ^ (w + 1) : Nat))) %
          (2 ^ (w + 1) : Nat) =
        ((A : Int) - (B : Int)) % (2 ^ (w + 1) : Nat) := by
    calc
      ((A : Int) + ((-(B : Int)) % (2 ^ (w + 1) : Nat))) %
          (2 ^ (w + 1) : Nat) =
          (((A : Int) % (2 ^ (w + 1) : Nat)) +
            ((-(B : Int)) % (2 ^ (w + 1) : Nat))) %
              (2 ^ (w + 1) : Nat) := by rw [hAmod]
      _ = ((A : Int) + (-(B : Int))) % (2 ^ (w + 1) : Nat) :=
        (Int.add_emod (A : Int) (-(B : Int))
          (2 ^ (w + 1) : Nat)).symm
      _ = ((A : Int) - (B : Int)) % (2 ^ (w + 1) : Nat) := by
        rw [Int.sub_eq_add_neg]
  have hPowCast :
      (2 : Int) ^ (w + 1) = ((2 ^ (w + 1) : Nat) : Int) := by
    exact_mod_cast (rfl : 2 ^ (w + 1) = 2 ^ (w + 1))
  have hNestedInt :
      ((A : Int) + ((-(B : Int)) % (2 : Int) ^ (w + 1))) %
          ((2 : Int) ^ (w + 1)) =
        ((A : Int) - (B : Int)) % ((2 : Int) ^ (w + 1)) := by
    rw [hPowCast]
    exact hNested
  have hEmodInt :
      ((A : Int) - (B : Int)) % ((2 : Int) ^ (w + 1)) =
        (extendedSubPayload w A B : Int) := by
    rw [hPowCast]
    exact emod_sub_nat w A B ha hb
  unfold __smtx_model_eval_bvsub
  simp only [__smtx_model_eval_bvadd, __smtx_model_eval_bvneg,
    SmtEval.native_zplus, SmtEval.native_zneg, SmtEval.native_mod_total]
  rw [hpow, hNestedInt, hEmodInt]

theorem eval_zero_extend_one_direct
    (M : SmtModel) (t : Term) (w A : Nat)
    (hEval : __smtx_model_eval M (__eo_to_smt t) =
      SmtValue.Binary (native_nat_to_int w) (A : Int)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.UOp1 UserOp1.zero_extend (Term.Numeral 1)) t)) =
      SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) := by
  change __smtx_model_eval M
      (SmtTerm.zero_extend (SmtTerm.Numeral 1) (__eo_to_smt t)) = _
  rw [__smtx_model_eval.eq_def]
  simp only
  rw [hEval]
  change SmtValue.Binary
      (native_zplus 1 (native_nat_to_int w)) (A : Int) = _
  congr 1
  simp [SmtEval.native_zplus, Smtm.native_nat_to_int, Int.add_comm]

def usuboExt (x : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral 1)) x

def usuboDiff (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) (usuboExt x)) (usuboExt y)

def usuboBit (x y n : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract n n) (usuboDiff x y)

def usuboOne : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)

def usuboRhs (x y n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (usuboBit x y n)) usuboOne

def usuboLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) x) y

theorem smt_typeof_usubo_ext (x : Term) (w : Nat)
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __smtx_typeof (__eo_to_smt (usuboExt x)) = SmtType.BitVec (w + 1) := by
  change __smtx_typeof
      (SmtTerm.zero_extend (SmtTerm.Numeral 1) (__eo_to_smt x)) = _
  rw [__smtx_typeof.eq_def]
  simp only
  simp [__smtx_typeof_zero_extend, hTy, SmtEval.native_zleq,
    SmtEval.native_zplus, Smtm.native_nat_to_int,
    SmtEval.native_int_to_nat, native_ite, Int.add_comm]

theorem smt_typeof_usubo_diff (x y : Term) (w : Nat)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w) :
    __smtx_typeof (__eo_to_smt (usuboDiff x y)) =
      SmtType.BitVec (w + 1) := by
  change __smtx_typeof
      (SmtTerm.bvsub (__eo_to_smt (usuboExt x))
        (__eo_to_smt (usuboExt y))) = _
  rw [__smtx_typeof.eq_def]
  simp only
  rw [smt_typeof_usubo_ext x w hx, smt_typeof_usubo_ext y w hy]
  simp [__smtx_typeof_bv_op_2, Smtm.native_nateq,
    SmtEval.native_ite]

theorem typeof_bvult_args_of_ne_stuck {A B : Term}
    (h : __eo_typeof_bvult A B ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) w := by
  rcases RuleProofs.eo_typeof_bvult_args_of_ne_stuck A B h with
    ⟨w, hA, hB, _hW⟩
  exact ⟨w, hA, hB⟩

def usuboTerm (x y n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (usuboLhs x y))
    (usuboRhs x y n)

def usuboPrem (x n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) n)
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)

theorem usubo_context (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (usuboTerm x y n) = Term.Bool ->
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
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hYTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult (__eo_typeof x) (__eo_typeof y))
      (__eo_typeof (usuboRhs x y n)) = Term.Bool at hResultTy
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
  have hLeftTy : __eo_typeof (usuboLhs x y) = Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool
    rw [hXTy, hYTy]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hRhsTy : __eo_typeof (usuboRhs x y n) = Term.Bool := by
    have hLeftTy' :
        __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool := by
      have hsimpa := hLeftTy
      try simp [usuboLhs] at hsimpa ⊢
      exact hsimpa
    rw [hLeftTy'] at hTypeEq
    exact hTypeEq.symm
  have hBitNe : __eo_typeof (usuboBit x y n) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hRhsTy; (try simp [usuboRhs] at hsimpa ⊢); exact hsimpa)).1
  let W := native_int_to_nat w
  have hDiffSmtTy :
      __smtx_typeof (__eo_to_smt (usuboDiff x y)) =
        SmtType.BitVec (W + 1) := by
    exact smt_typeof_usubo_diff x y W
      (by simpa [W] using hXSmtTy) (by simpa [W] using hYSmtTy)
  have hDiffTrans : RuleProofs.eo_has_smt_translation (usuboDiff x y) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hDiffSmtTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck (usuboDiff x y) n n
      hDiffTrans (by have hsimpa := hBitNe; (try simp [usuboBit] at hsimpa ⊢); exact hsimpa) with
    ⟨wd, hi, lo, _hDiffEoTy, hNHi, hNLo, hwd0, hlo0, hiwd,
      _hExtractWidth0, hDiffSmtTy'⟩
  have hILo : lo = hi := by
    rw [hNHi] at hNLo
    injection hNLo with h
    exact h.symm
  subst lo
  have hWdNat : native_int_to_nat wd = W + 1 := by
    rw [hDiffSmtTy] at hDiffSmtTy'
    exact (SmtType.BitVec.inj hDiffSmtTy').symm
  have hWd : wd = native_nat_to_int (W + 1) := by
    have hRound := native_nat_to_int_int_to_nat_eq wd hwd0
    rw [hWdNat] at hRound
    exact hRound.symm
  subst wd
  exact ⟨w, hi, hXTy, hYTy, hNHi, hw0, hlo0, hiwd,
    hXSmtTy, hYSmtTy⟩

theorem typed_usubo_term (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (usuboTerm x y n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (usuboTerm x y n) := by
  intro hXTrans hYTrans hResultTy
  rcases usubo_context x y n hXTrans hYTrans hResultTy with
    ⟨w, i, _hXTy, _hYTy, rfl, _hw0, hi0, hiLt, hXSmtTy, hYSmtTy⟩
  let W := native_int_to_nat w
  have hXSmtTyW : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  have hLhsBool : RuleProofs.eo_has_bool_type (usuboLhs x y) := by
    change __smtx_typeof
      (SmtTerm.bvusubo (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
    simp only
    simp [__smtx_typeof_bv_op_2_ret, hXSmtTyW, hYSmtTyW,
      Smtm.native_nateq, native_ite]
  have hDiffSmtTy :
      __smtx_typeof (__eo_to_smt (usuboDiff x y)) =
        SmtType.BitVec (W + 1) :=
    smt_typeof_usubo_diff x y W hXSmtTyW hYSmtTyW
  have hBitSmtTy :
      __smtx_typeof
          (__eo_to_smt (usuboBit x y (Term.Numeral i))) =
        SmtType.BitVec 1 := by
    change __smtx_typeof
      (SmtTerm.extract (SmtTerm.Numeral i) (SmtTerm.Numeral i)
        (__eo_to_smt (usuboDiff x y))) = _
    rw [__smtx_typeof.eq_def]
    simp only
    rw [hDiffSmtTy]
    have hiLtW :
        native_zlt i (native_nat_to_int (W + 1)) = true := by
      simpa [W] using hiLt
    have hOne : native_zplus (native_zplus i 1) (native_zneg i) = 1 := by
      simp [SmtEval.native_zplus, SmtEval.native_zneg]
      rw [Int.add_comm i 1]
      exact Int.add_neg_cancel_right 1 i
    unfold __smtx_typeof_extract
    simp only
    rw [hi0, hiLtW, hOne]
    native_decide
  have hOneSmtTy : __smtx_typeof (__eo_to_smt usuboOne) =
      SmtType.BitVec 1 := by
    simpa [usuboOne, native_int_to_nat, SmtEval.native_int_to_nat]
      using smt_typeof_bv_const 1 1 (by decide)
  have hRhsBool : RuleProofs.eo_has_bool_type
      (usuboRhs x y (Term.Numeral i)) := by
    unfold usuboRhs
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hBitSmtTy.trans hOneSmtTy.symm)
      (by rw [hBitSmtTy]; intro h; cases h)
  unfold usuboTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

theorem eval_usubo_bvsize
    (M : SmtModel) (x : Term) (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral w := by
  intro hw0 hXSmtTy
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral w
  have hRound := native_int_to_nat_roundtrip w hw0
  have hNN :
      native_zleq 0 (native_nat_to_int (native_int_to_nat w)) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int]
  rw [hXSmtTy]
  simp [__eo_to_smt_bv_size, native_ite, hw0, hNN, hRound,
    __smtx_model_eval, __smtx_model_eval__at_purify]

theorem bool_of_true_eval_local
    {M : SmtModel} {t : Term} {b : Bool} :
    eo_interprets M t true ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
    b = true := by
  intro hTrue hEval
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue
  cases hTrue with
  | intro_true _ hEvalTrue =>
      rw [hEval] at hEvalTrue
      cases b <;> simp at hEvalTrue ⊢

theorem usubo_index_eq_of_premise
    (M : SmtModel) (x : Term) (w i : native_Int) :
    eo_interprets M (usuboPrem x (Term.Numeral i)) true ->
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    i = w := by
  intro hPrem hw0 hXSmtTy
  have hSize := eval_usubo_bvsize M x w hw0 hXSmtTy
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt (usuboPrem x (Term.Numeral i))) =
        SmtValue.Boolean (native_zeq i w) := by
    unfold usuboPrem
    change __smtx_model_eval M
      (SmtTerm.eq (SmtTerm.Numeral i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) = _
    rw [smtx_eval_eq_term_eq, hSize]
    simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
      SmtEval.native_zeq]
  have hEq := bool_of_true_eval_local hPrem hEval
  simpa [SmtEval.native_zeq] using hEq

theorem eval_usubo_diff
    (M : SmtModel) (x y : Term) (w A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    __smtx_model_eval M (__eo_to_smt (usuboDiff x y)) =
      SmtValue.Binary (native_nat_to_int (w + 1))
        (extendedSubPayload w A B : Int) := by
  change __smtx_model_eval M
      (SmtTerm.bvsub
        (__eo_to_smt (usuboExt x)) (__eo_to_smt (usuboExt y))) = _
  rw [__smtx_model_eval.eq_def]
  simp only
  rw [show __smtx_model_eval M (__eo_to_smt (usuboExt x)) =
      SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) by
        exact eval_zero_extend_one_direct M x w A hx]
  rw [show __smtx_model_eval M (__eo_to_smt (usuboExt y)) =
      SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int) by
        exact eval_zero_extend_one_direct M y w B hy]
  exact eval_bvsub_extended w A B ha hb

theorem eval_usubo_rhs
    (M : SmtModel) (x y : Term) (w A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (ha : A < 2 ^ w) (hb : B < 2 ^ w) :
    __smtx_model_eval M
        (__eo_to_smt
          (usuboRhs x y (Term.Numeral (native_nat_to_int w)))) =
      SmtValue.Boolean (decide (A < B)) := by
  have hDiff := eval_usubo_diff M x y w A B hx hy ha hb
  have hPayload0 : (0 : Int) ≤ (extendedSubPayload w A B : Int) := by
    omega
  have hBit := eval_extract_bit_term M (usuboDiff x y)
    (native_nat_to_int (w + 1)) (extendedSubPayload w A B : Int) w
    hDiff hPayload0
  have hOne : __smtx_model_eval M (__eo_to_smt usuboOne) =
      SmtValue.Binary 1 1 := by
    change __smtx_model_eval M (SmtTerm.Binary 1 1) =
      SmtValue.Binary 1 1
    simp only [__smtx_model_eval]
  unfold usuboRhs
  change __smtx_model_eval M
      (SmtTerm.eq
        (__eo_to_smt
          (usuboBit x y (Term.Numeral (native_nat_to_int w))))
        (__eo_to_smt usuboOne)) = _
  rw [smtx_eval_eq_term_eq, hOne]
  rw [show __smtx_model_eval M
      (__eo_to_smt
        (usuboBit x y (Term.Numeral (native_nat_to_int w)))) =
      bv1 ((extendedSubPayload w A B).testBit w) by
        simpa [usuboBit] using hBit]
  rw [bv1_eq_one, extended_sub_payload_bit w A B ha hb]

theorem eval_usubo_lhs
    (M : SmtModel) (x y : Term) (w A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int w) (B : Int)) :
    __smtx_model_eval M (__eo_to_smt (usuboLhs x y)) =
      SmtValue.Boolean (decide (A < B)) := by
  change __smtx_model_eval M
      (SmtTerm.bvusubo (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def]
  simp only
  rw [hx, hy]
  simp [__smtx_model_eval_bvusubo, __smtx_model_eval_bvult,
    __smtx_model_eval_bvugt, SmtEval.native_zlt]

theorem facts_usubo_term
    (M : SmtModel) (hM : model_wf M) (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    eo_interprets M (usuboPrem x n) true ->
    __eo_typeof (usuboTerm x y n) = Term.Bool ->
    eo_interprets M (usuboTerm x y n) true := by
  intro hXTrans hYTrans hPrem hResultTy
  rcases usubo_context x y n hXTrans hYTrans hResultTy with
    ⟨w, i, _hXTy, _hYTy, rfl, hw0, _hi0, _hiLt, hXSmtTy, hYSmtTy⟩
  have hIndex := usubo_index_eq_of_premise M x w i hPrem hw0 hXSmtTy
  subst i
  let W := native_int_to_nat w
  have hRound : native_nat_to_int W = w := by
    exact native_nat_to_int_int_to_nat_eq w hw0
  have hXSmtTyW : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  rcases bitvec_eval_nat_payload M hM x W hXSmtTyW with
    ⟨A, hXEval, hABound⟩
  rcases bitvec_eval_nat_payload M hM y W hYSmtTyW with
    ⟨B, hYEval, hBBound⟩
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (usuboLhs x y)) =
        SmtValue.Boolean (decide (A < B)) :=
    eval_usubo_lhs M x y W A B hXEval hYEval
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt (usuboRhs x y (Term.Numeral w))) =
        SmtValue.Boolean (decide (A < B)) := by
    simpa [hRound] using
      eval_usubo_rhs M x y W A B hXEval hYEval hABound hBBound
  have hBool := typed_usubo_term x y (Term.Numeral w)
    hXTrans hYTrans hResultTy
  unfold usuboTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [usuboTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (usuboLhs x y)))
      (__smtx_model_eval M
        (__eo_to_smt (usuboRhs x y (Term.Numeral w))))
    rw [hLhsEval, hRhsEval]
    exact RuleProofs.smt_value_rel_refl _

def usuboProgram (x y n : Term) : Term :=
  __eo_prog_bv_usubo_eliminate x y n (Proof.pf (usuboPrem x n))

theorem usubo_program_eq_term_of_ne_stuck (x y n : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> n ≠ Term.Stuck ->
    usuboProgram x y n = usuboTerm x y n := by
  intro hXNe hYNe hNNe
  unfold usuboProgram usuboPrem
  rw [__eo_prog_bv_usubo_eliminate.eq_4 x y n n x hXNe hYNe hNNe]
  simp [usuboTerm, usuboLhs, usuboRhs, usuboBit, usuboDiff, usuboExt,
    usuboOne, __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, SmtEval.native_not, native_and, SmtEval.native_and,
    hXNe, hNNe]

theorem usubo_shape_of_ne_stuck (x y n P : Term) :
    __eo_prog_bv_usubo_eliminate x y n (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck ∧ n ≠ Term.Stuck ∧
      ∃ pn px, P = usuboPrem px pn := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_usubo_eliminate.eq_1 y n (Proof.pf P))
  have hYNe : y ≠ Term.Stuck := by
    intro hY
    subst y
    exact hProg
      (__eo_prog_bv_usubo_eliminate.eq_2 x n (Proof.pf P) hXNe)
  have hNNe : n ≠ Term.Stuck := by
    intro hN
    subst n
    exact hProg
      (__eo_prog_bv_usubo_eliminate.eq_3 x y (Proof.pf P) hXNe hYNe)
  refine ⟨hXNe, hYNe, hNNe, ?_⟩
  by_cases hShape : ∃ pn px, P = usuboPrem px pn
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_usubo_eliminate.eq_5 x y n (Proof.pf P)
        hXNe hYNe hNNe (by
          intro pn px hP
          cases hP
          exact hShape ⟨pn, px, rfl⟩)))

theorem typed_usubo_program (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation n ->
    __eo_typeof (usuboProgram x y n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (usuboProgram x y n) := by
  intro hXTrans hYTrans hNTrans hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hEq := usubo_program_eq_term_of_ne_stuck x y n hXNe hYNe hNNe
  have hTermTy : __eo_typeof (usuboTerm x y n) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_usubo_term x y n hXTrans hYTrans hTermTy

theorem facts_usubo_program
    (M : SmtModel) (hM : model_wf M) (x y n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation n ->
    eo_interprets M (usuboPrem x n) true ->
    __eo_typeof (usuboProgram x y n) = Term.Bool ->
    eo_interprets M (usuboProgram x y n) true := by
  intro hXTrans hYTrans hNTrans hPrem hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hEq := usubo_program_eq_term_of_ne_stuck x y n hXNe hYNe hNNe
  have hTermTy : __eo_typeof (usuboTerm x y n) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_usubo_term M hM x y n hXTrans hYTrans hPrem hTermTy
