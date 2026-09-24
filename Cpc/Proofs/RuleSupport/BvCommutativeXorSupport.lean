module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvCommutativeXorLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
      (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))

def bvCommutativeXorRhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
      (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y)))

def bvCommutativeXorTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvCommutativeXorLhs x y))
    (bvCommutativeXorRhs x y)

private theorem eo_typeof_bvand_arg_types_of_ne_stuck_local
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    ∃ u,
      A = Term.Apply (Term.UOp UserOp.BitVec) u ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) u := by
  cases A <;> cases B <;> simp [__eo_typeof_bvand] at h ⊢
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_bvand] at h ⊢
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_bvand] at h ⊢
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
            Term.Stuck := by
        simpa [__eo_typeof_bvand] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

private theorem eo_typeof_bvand_args_of_eq_bitvec
    {A B u : Term}
    (h : __eo_typeof_bvand A B = Term.Apply (Term.UOp UserOp.BitVec) u) :
    A = Term.Apply (Term.UOp UserOp.BitVec) u ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) u ∧
      u ≠ Term.Stuck := by
  have hNe : __eo_typeof_bvand A B ≠ Term.Stuck := by
    rw [h]
    intro hBad
    cases hBad
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hNe with
    ⟨v, hA, hB⟩
  have hvNe : v ≠ Term.Stuck := by
    intro hv
    apply hNe
    rw [hA, hB, hv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hReduce :
      __eo_typeof_bvand
          (Term.Apply (Term.UOp UserOp.BitVec) v)
          (Term.Apply (Term.UOp UserOp.BitVec) v) =
        Term.Apply (Term.UOp UserOp.BitVec) v := by
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hvNe]
  have hvEq : v = u := by
    rw [hA, hB] at h
    rw [hReduce] at h
    cases h
    rfl
  subst u
  exact ⟨hA, hB, hvNe⟩

theorem bv_commutative_xor_args_type_of_bool (x y : Term) :
    __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  have hLeftNN :
      __eo_typeof (bvCommutativeXorLhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvCommutativeXorLhs x y))
        (__eo_typeof (bvCommutativeXorRhs x y))
        (by
          exact hTy)
    exact hOperands.1
  have hOuterNN :
      __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
              (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) ≠
        Term.Stuck := by
    exact hLeftNN
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hOuterNN with
    ⟨w, hXTy, hInnerTy⟩
  have hInnerEq :
      __eo_typeof_bvand (__eo_typeof y)
          (__eo_typeof (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    exact hInnerTy
  rcases eo_typeof_bvand_args_of_eq_bitvec hInnerEq with
    ⟨hYTy, _hNilTy, hWNe⟩
  exact ⟨w, hXTy, hYTy, hWNe⟩

theorem bv_commutative_xor_nil_x_ne (x y : Term) :
    __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck := by
  intro hTy hNil
  have hLeftNN :
      __eo_typeof (bvCommutativeXorLhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvCommutativeXorLhs x y))
        (__eo_typeof (bvCommutativeXorRhs x y))
        (by
          exact hTy)
    exact hOperands.1
  apply hLeftNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof x)
      (__eo_typeof_bvand (__eo_typeof y) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

theorem bv_commutative_xor_nil_y_ne (x y : Term) :
    __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y) ≠ Term.Stuck := by
  intro hTy hNil
  have hRightNN :
      __eo_typeof (bvCommutativeXorRhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvCommutativeXorLhs x y))
        (__eo_typeof (bvCommutativeXorRhs x y))
        (by
          exact hTy)
    exact hOperands.2
  apply hRightNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof y)
      (__eo_typeof_bvand (__eo_typeof x) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) := by
  intro hXTrans hXType
  have hSmtType :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x) rfl
      hXTrans hXType
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;>
      simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hXTrans hSmtType)

private theorem bvZero_to_bin_eq_of_bound (w : Nat) :
    native_zleq (native_nat_to_int w) 4294967296 = true ->
    __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hBound
  have hBoundProp : native_nat_to_int w <= 4294967296 := by
    simpa [native_zleq] using hBound
  have hWidthNonneg : 0 <= native_nat_to_int w := by
    simp [native_nat_to_int]
  simp [__eo_to_bin, __eo_mk_binary, native_ite, native_zleq,
    hBoundProp, hWidthNonneg, native_mod_total]

private theorem bvXor_nil_eq_zero_of_type
    {ty : Term} (w : Nat) :
    __eo_to_smt_type ty = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) ty ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvxor) ty =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hTy hNe
  have hTyEq :
      ty =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hTy
  subst ty
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · change
      __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Binary (native_nat_to_int w) 0
    exact bvZero_to_bin_eq_of_bound w hBound
  · have hStuck :
        __eo_nil (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w))) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_nil, __eo_nil_bvxor, __eo_to_bin, hBoundFalse,
        native_ite, native_zleq]
    exact False.elim (hNe hStuck)

private theorem smt_typeof_binary_zero (w : Nat) :
    __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) 0) =
      SmtType.BitVec w := by
  simp [__smtx_typeof, SmtEval.native_and, native_ite, native_zleq,
    native_zeq, native_nat_to_int, native_mod_total, SmtEval.native_int_to_nat,
    native_int_to_nat]

private theorem smt_typeof_bvxor_nil
    (x : Term) (w : Nat) :
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
      SmtType.BitVec w := by
  intro hTy hNilNe
  have hEq := bvXor_nil_eq_zero_of_type w hTy hNilNe
  rw [hEq]
  exact smt_typeof_binary_zero w

private theorem smt_eval_bvxor_nil
    (M : SmtModel) (x : Term) (w : Nat) :
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
      SmtValue.Binary (native_nat_to_int w) 0 := by
  intro hTy hNilNe
  have hEq := bvXor_nil_eq_zero_of_type w hTy hNilNe
  rw [hEq]
  change __smtx_model_eval M (SmtTerm.Binary (native_nat_to_int w) 0) =
    SmtValue.Binary (native_nat_to_int w) 0
  have hMod0 :
      native_mod_total 0 (native_int_pow2 (native_nat_to_int w)) = 0 := by
    simp [native_mod_total]
  simp [__smtx_model_eval, hMod0]

private theorem bv_commutative_xor_context
    (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool ->
    ∃ w,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof y) = SmtType.BitVec w ∧
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ∧
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y) ≠ Term.Stuck := by
  intro hXTrans hYTrans hResultTy
  rcases bv_commutative_xor_args_type_of_bool x y hResultTy with
    ⟨wTerm, hXTy, hYTy, _hWNe⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x wTerm hXTrans hXTy with
    ⟨n, hWTerm, hNonneg, hXSmtTy⟩
  subst wTerm
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y (Term.Numeral n)
      hYTrans (by simpa using hYTy) with
    ⟨m, hM, _hMNonneg, hYSmtTy⟩
  cases hM
  have hXTypeSmt :
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec (native_int_to_nat n) := by
    rw [hXTy]
    simp [__eo_to_smt_type, hNonneg, native_ite]
  have hYTypeSmt :
      __eo_to_smt_type (__eo_typeof y) = SmtType.BitVec (native_int_to_nat n) := by
    rw [hYTy]
    simp [__eo_to_smt_type, hNonneg, native_ite]
  exact ⟨native_int_to_nat n, hXSmtTy, hYSmtTy, hXTypeSmt, hYTypeSmt,
    bv_commutative_xor_nil_x_ne x y hResultTy,
    bv_commutative_xor_nil_y_ne x y hResultTy⟩

private theorem smtx_typeof_bvxor_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvxor x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smt_typeof_bv_comm_xor_lhs
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvCommutativeXorLhs x y)) =
      SmtType.BitVec w := by
  intro hXTy hYTy hXTypeSmt hNilXNe
  have hNilTy := smt_typeof_bvxor_nil x w hXTypeSmt hNilXNe
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvxor (__eo_to_smt y)
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
        SmtType.BitVec w := by
    rw [smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_2, hYTy, hNilTy, native_nateq, native_ite]
  change __smtx_typeof
      (SmtTerm.bvxor (__eo_to_smt x)
        (SmtTerm.bvxor (__eo_to_smt y)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))))) =
    SmtType.BitVec w
  rw [smtx_typeof_bvxor_term_eq]
  simp [__smtx_typeof_bv_op_2, hXTy, hInnerTy, native_nateq, native_ite]

private theorem smt_typeof_bv_comm_xor_rhs
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof y) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvCommutativeXorRhs x y)) =
      SmtType.BitVec w := by
  intro hXTy hYTy hYTypeSmt hNilYNe
  have hNilTy := smt_typeof_bvxor_nil y w hYTypeSmt hNilYNe
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvxor (__eo_to_smt x)
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y)))) =
        SmtType.BitVec w := by
    rw [smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_2, hXTy, hNilTy, native_nateq, native_ite]
  change __smtx_typeof
      (SmtTerm.bvxor (__eo_to_smt y)
        (SmtTerm.bvxor (__eo_to_smt x)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y))))) =
    SmtType.BitVec w
  rw [smtx_typeof_bvxor_term_eq]
  simp [__smtx_typeof_bv_op_2, hYTy, hInnerTy, native_nateq, native_ite]

theorem typed_bv_commutative_xor_term (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvCommutativeXorTerm x y) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_commutative_xor_context x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hYTypeSmt, hNilXNe, hNilYNe⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvCommutativeXorLhs x y) (bvCommutativeXorRhs x y)
    (by
      rw [smt_typeof_bv_comm_xor_lhs x y w hXTy hYTy hXTypeSmt hNilXNe,
        smt_typeof_bv_comm_xor_rhs x y w hXTy hYTy hYTypeSmt hNilYNe])
    (by
      rw [smt_typeof_bv_comm_xor_lhs x y w hXTy hYTy hXTypeSmt hNilXNe]
      simp)

private theorem smt_eval_binary_of_smt_type_bitvec
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm)
    (w : native_Nat) :
    __smtx_typeof t = SmtType.BitVec w ->
    ∃ n, __smtx_model_eval M t =
      SmtValue.Binary (native_nat_to_int w) n ∧
      native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.BitVec w := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  rcases bitvec_value_canonical hValTy with ⟨n, hEval⟩
  have hCan :
      native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true :=
    bitvec_payload_canonical (by simpa [hEval] using hValTy)
  exact ⟨n, hEval, hCan⟩

private theorem smtx_eval_bvxor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvxor x y) =
      __smtx_model_eval_bvxor (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private theorem bitvec_toInt_emod_pow (w : Nat) (x : BitVec w) :
    x.toInt % (2 ^ w : Int) = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : 2 * x.toNat < 2 ^ w
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)

private theorem native_mod_pow2_eq_bitvec_toNat (w : Nat) (n : Int) :
    native_mod_total n (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n).toNat : Int) := by
  rw [native_int_pow2_nat]
  change n % (2 ^ w : Int) = ((BitVec.ofInt w n).toNat : Int)
  rw [BitVec.toNat_ofInt]
  have hpow : 0 < (2 ^ w : Int) := by exact_mod_cast Nat.two_pow_pos w
  exact (Int.toNat_of_nonneg (Int.emod_nonneg n (Int.ne_of_gt hpow))).symm

private theorem native_binary_xor_mod_eq_toNat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n1 ^^^ BitVec.ofInt w n2).toNat : Int) := by
  cases w with
  | zero =>
      simp [native_binary_xor, impl_native_pixor, native_mod_total,
        native_int_pow2_nat]
  | succ w =>
      simp [native_binary_xor, impl_native_pixor, native_mod_total,
        native_nat_to_int, native_ite, native_zeq]
      exact bitvec_toInt_emod_pow (Nat.succ w)
        (BitVec.ofInt (Nat.succ w) n1 ^^^ BitVec.ofInt (Nat.succ w) n2)

private theorem native_binary_xor_right_zero_mod_nat
    (w : Nat) (n : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) n 0)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_binary_xor_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  simp

private theorem native_binary_xor_comm_mod_nat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total (native_binary_xor (native_nat_to_int w) n2 n1)
        (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_binary_xor_mod_eq_toNat, native_binary_xor_mod_eq_toNat]
  rw [BitVec.xor_comm]

private theorem bvxor_right_zero_of_canonical (w : Nat) (p : native_Int) :
    native_zeq p
        (native_mod_total p (native_int_pow2 (native_nat_to_int w))) = true ->
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) p)
        (SmtValue.Binary (native_nat_to_int w) 0) =
      SmtValue.Binary (native_nat_to_int w) p := by
  intro hCan
  have hPayloadMod :
      native_mod_total p (native_int_pow2 (native_nat_to_int w)) = p := by
    have hPayloadEq :
        p = native_mod_total p (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hCan
    exact hPayloadEq.symm
  simp [__smtx_model_eval_bvxor]
  rw [native_binary_xor_right_zero_mod_nat w p, hPayloadMod]

private theorem bvxor_eval_comm (w : Nat) (nx ny : native_Int) :
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) nx)
        (SmtValue.Binary (native_nat_to_int w) ny) =
      __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) ny)
        (SmtValue.Binary (native_nat_to_int w) nx) := by
  simp [__smtx_model_eval_bvxor]
  exact native_binary_xor_comm_mod_nat w nx ny

private theorem eval_bv_commutative_xor
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvCommutativeXorLhs x y)) =
      __smtx_model_eval M (__eo_to_smt (bvCommutativeXorRhs x y)) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_commutative_xor_context x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hYTypeSmt, hNilXNe, hNilYNe⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, hXCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hYTy with
    ⟨ny, hYEval, hYCan⟩
  have hNilXEval := smt_eval_bvxor_nil M x w hXTypeSmt hNilXNe
  have hNilYEval := smt_eval_bvxor_nil M y w hYTypeSmt hNilYNe
  change __smtx_model_eval M
      (SmtTerm.bvxor (__eo_to_smt x)
        (SmtTerm.bvxor (__eo_to_smt y)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))))) =
    __smtx_model_eval M
      (SmtTerm.bvxor (__eo_to_smt y)
        (SmtTerm.bvxor (__eo_to_smt x)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y)))))
  repeat rw [smtx_eval_bvxor_term_eq]
  rw [hXEval, hYEval, hNilXEval, hNilYEval]
  rw [bvxor_right_zero_of_canonical w ny hYCan,
    bvxor_right_zero_of_canonical w nx hXCan]
  exact bvxor_eval_comm w nx ny

theorem facts_bv_commutative_xor_term
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool ->
    eo_interprets M (bvCommutativeXorTerm x y) true := by
  intro hXTrans hYTrans hResultTy
  have hBool :=
    typed_bv_commutative_xor_term x y hXTrans hYTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvCommutativeXorLhs x y)))
      (__smtx_model_eval M (__eo_to_smt (bvCommutativeXorRhs x y)))
    rw [eval_bv_commutative_xor M hM x y hXTrans hYTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvCommutativeXorProgram (x y : Term) : Term :=
  __eo_prog_bv_commutative_xor x y

private def bvCommutativeXorProgramSkeleton (x y : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) x)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) y)
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))))
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) y)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) x)
        (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y))))

private theorem bvCommutativeXorProgram_eq_skeleton_of_ne_stuck
    (x y : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    bvCommutativeXorProgram x y =
      bvCommutativeXorProgramSkeleton x y := by
  intro hXNe hYNe
  cases x <;> cases y <;>
    simp [bvCommutativeXorProgram, bvCommutativeXorProgramSkeleton,
      __eo_prog_bv_commutative_xor] at hXNe hYNe ⊢

theorem bvCommutativeXorProgram_eq_term_of_type_bool
    (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeXorProgram x y) = Term.Bool ->
    bvCommutativeXorProgram x y = bvCommutativeXorTerm x y := by
  intro hXTrans hYTrans hTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hSkeleton :=
    bvCommutativeXorProgram_eq_skeleton_of_ne_stuck x y hXNe hYNe
  by_cases hNilX :
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) = Term.Stuck
  · have hProgStuck : bvCommutativeXorProgram x y = Term.Stuck := by
      rw [hSkeleton]
      simp [bvCommutativeXorProgramSkeleton, __eo_mk_apply, hNilX]
    rw [hProgStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · by_cases hNilY :
        __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof y) = Term.Stuck
    · have hProgStuck : bvCommutativeXorProgram x y = Term.Stuck := by
        rw [hSkeleton]
        simp [bvCommutativeXorProgramSkeleton, __eo_mk_apply, hNilX, hNilY]
      rw [hProgStuck] at hTy
      have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
        native_decide
      exact False.elim (hBad hTy)
    · rw [hSkeleton]
      simp [bvCommutativeXorProgramSkeleton, bvCommutativeXorTerm,
        bvCommutativeXorLhs, bvCommutativeXorRhs, __eo_mk_apply, hNilX, hNilY]

theorem typed_bv_commutative_xor_program (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeXorProgram x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvCommutativeXorProgram x y) := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvCommutativeXorProgram_eq_term_of_type_bool x y hXTrans hYTrans hResultTy
  have hTermTy :
      __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_commutative_xor_term x y hXTrans hYTrans hTermTy

theorem facts_bv_commutative_xor_program
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeXorProgram x y) = Term.Bool ->
    eo_interprets M (bvCommutativeXorProgram x y) true := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvCommutativeXorProgram_eq_term_of_type_bool x y hXTrans hYTrans hResultTy
  have hTermTy :
      __eo_typeof (bvCommutativeXorTerm x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_commutative_xor_term M hM x y hXTrans hYTrans hTermTy

def bvXorNotLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
    (Term.Apply (Term.UOp UserOp.bvnot) x))
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
      (Term.Apply (Term.UOp UserOp.bvnot) y))
      (__eo_nil (Term.UOp UserOp.bvxor)
        (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x))))

def bvXorNotRhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
      (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))

def bvXorNotTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvXorNotLhs x y))
    (bvXorNotRhs x y)

theorem bv_xor_not_args_type_of_bool (x y : Term) :
    __eo_typeof (bvXorNotTerm x y) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  have hRightNN :
      __eo_typeof (bvXorNotRhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvXorNotLhs x y))
        (__eo_typeof (bvXorNotRhs x y))
        (by exact hTy)
    exact hOperands.2
  have hOuterNN :
      __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
              (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) ≠
        Term.Stuck := by
    exact hRightNN
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hOuterNN with
    ⟨w, hXTy, hInnerTy⟩
  have hInnerEq :
      __eo_typeof_bvand (__eo_typeof y)
          (__eo_typeof (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    exact hInnerTy
  rcases eo_typeof_bvand_args_of_eq_bitvec hInnerEq with
    ⟨hYTy, _hNilTy, hWNe⟩
  exact ⟨w, hXTy, hYTy, hWNe⟩

theorem bv_xor_not_nil_x_ne (x y : Term) :
    __eo_typeof (bvXorNotTerm x y) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck := by
  intro hTy hNil
  have hRightNN :
      __eo_typeof (bvXorNotRhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvXorNotLhs x y))
        (__eo_typeof (bvXorNotRhs x y))
        (by exact hTy)
    exact hOperands.2
  apply hRightNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof x)
      (__eo_typeof_bvand (__eo_typeof y) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

theorem bv_xor_not_nil_not_x_ne (x y : Term) :
    __eo_typeof (bvXorNotTerm x y) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvxor)
        (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) ≠ Term.Stuck := by
  intro hTy hNil
  have hLeftNN :
      __eo_typeof (bvXorNotLhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvXorNotLhs x y))
        (__eo_typeof (bvXorNotRhs x y))
        (by exact hTy)
    exact hOperands.1
  apply hLeftNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
        (Term.Apply (Term.UOp UserOp.bvnot) x))
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
          (Term.Apply (Term.UOp UserOp.bvnot) y))
          (__eo_nil (Term.UOp UserOp.bvxor)
            (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x))))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof_bvnot (__eo_typeof x))
      (__eo_typeof_bvand (__eo_typeof_bvnot (__eo_typeof y)) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

private theorem bv_xor_not_context
    (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvXorNotTerm x y) = Term.Bool ->
    ∃ w,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) =
        SmtType.BitVec w ∧
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ∧
      __eo_nil (Term.UOp UserOp.bvxor)
        (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) ≠ Term.Stuck := by
  intro hXTrans hYTrans hResultTy
  rcases bv_xor_not_args_type_of_bool x y hResultTy with
    ⟨wTerm, hXTy, hYTy, _hWNe⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x wTerm hXTrans hXTy with
    ⟨n, hWTerm, hNonneg, hXSmtTy⟩
  subst wTerm
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y (Term.Numeral n)
      hYTrans (by simpa using hYTy) with
    ⟨m, hM, _hMNonneg, hYSmtTy⟩
  cases hM
  have hXTypeSmt :
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec (native_int_to_nat n) := by
    rw [hXTy]
    simp [__eo_to_smt_type, hNonneg, native_ite]
  have hNotXTypeSmt :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) =
        SmtType.BitVec (native_int_to_nat n) := by
    change __eo_to_smt_type (__eo_typeof_bvnot (__eo_typeof x)) =
      SmtType.BitVec (native_int_to_nat n)
    rw [hXTy]
    simp [__eo_typeof_bvnot, __eo_to_smt_type, hNonneg, native_ite]
  exact ⟨native_int_to_nat n, hXSmtTy, hYSmtTy, hXTypeSmt, hNotXTypeSmt,
    bv_xor_not_nil_x_ne x y hResultTy,
    bv_xor_not_nil_not_x_ne x y hResultTy⟩

private theorem smt_typeof_bv_xor_not_lhs
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) =
      SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor)
      (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvXorNotLhs x y)) = SmtType.BitVec w := by
  intro hXTy hYTy hNotXTypeSmt hNilNotXNe
  have hNotXTy :
      __smtx_typeof (SmtTerm.bvnot (__eo_to_smt x)) = SmtType.BitVec w := by
    rw [smtx_typeof_bvnot_term_eq]
    simp [__smtx_typeof_bv_op_1, hXTy]
  have hNotYTy :
      __smtx_typeof (SmtTerm.bvnot (__eo_to_smt y)) = SmtType.BitVec w := by
    rw [smtx_typeof_bvnot_term_eq]
    simp [__smtx_typeof_bv_op_1, hYTy]
  have hNilTy :=
    smt_typeof_bvxor_nil (Term.Apply (Term.UOp UserOp.bvnot) x) w
      hNotXTypeSmt hNilNotXNe
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvxor (SmtTerm.bvnot (__eo_to_smt y))
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor)
              (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x))))) =
        SmtType.BitVec w := by
    rw [smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_2, hNotYTy, hNilTy, native_nateq, native_ite]
  change __smtx_typeof
      (SmtTerm.bvxor (SmtTerm.bvnot (__eo_to_smt x))
        (SmtTerm.bvxor (SmtTerm.bvnot (__eo_to_smt y))
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor)
            (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)))))) =
    SmtType.BitVec w
  rw [smtx_typeof_bvxor_term_eq]
  simp [__smtx_typeof_bv_op_2, hNotXTy, hInnerTy, native_nateq, native_ite]

private theorem smt_typeof_bv_xor_not_rhs
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvXorNotRhs x y)) = SmtType.BitVec w := by
  intro hXTy hYTy hXTypeSmt hNilXNe
  have hNilTy := smt_typeof_bvxor_nil x w hXTypeSmt hNilXNe
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvxor (__eo_to_smt y)
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
        SmtType.BitVec w := by
    rw [smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_2, hYTy, hNilTy, native_nateq, native_ite]
  change __smtx_typeof
      (SmtTerm.bvxor (__eo_to_smt x)
        (SmtTerm.bvxor (__eo_to_smt y)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))))) =
    SmtType.BitVec w
  rw [smtx_typeof_bvxor_term_eq]
  simp [__smtx_typeof_bv_op_2, hXTy, hInnerTy, native_nateq, native_ite]

theorem typed_bv_xor_not_term (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvXorNotTerm x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvXorNotTerm x y) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_xor_not_context x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hNotXTypeSmt, hNilXNe, hNilNotXNe⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvXorNotLhs x y) (bvXorNotRhs x y)
    (by
      rw [smt_typeof_bv_xor_not_lhs x y w hXTy hYTy hNotXTypeSmt hNilNotXNe,
        smt_typeof_bv_xor_not_rhs x y w hXTy hYTy hXTypeSmt hNilXNe])
    (by
      rw [smt_typeof_bv_xor_not_lhs x y w hXTy hYTy hNotXTypeSmt hNilNotXNe]
      simp)

private theorem native_binary_not_eq_pow_sub_succ
    (w n : native_Int) :
    native_binary_not w n =
      native_int_pow2 w - (n + 1) := by
  simp [native_binary_not, native_zplus, native_zneg,
    Int.sub_eq_add_neg]

private theorem native_binary_not_mod_of_canonical_nat
    (w : Nat) (n : native_Int) :
    native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true ->
    native_mod_total (native_binary_not (native_nat_to_int w) n)
        (native_int_pow2 (native_nat_to_int w)) =
      native_int_pow2 (native_nat_to_int w) - 1 - n := by
  intro hCan
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth hCan
  have hRaw :
      native_binary_not (native_nat_to_int w) n =
        native_int_pow2 (native_nat_to_int w) - 1 - n := by
    rw [native_binary_not_eq_pow_sub_succ]
    let p := native_int_pow2 (native_nat_to_int w)
    change p - (n + 1) = p - 1 - n
    simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm,
      Int.add_left_comm]
  rw [hRaw]
  have hLo : 0 <= native_int_pow2 (native_nat_to_int w) - 1 - n := by
    have hEq :
        native_int_pow2 (native_nat_to_int w) - 1 - n =
          native_int_pow2 (native_nat_to_int w) - (n + 1) := by
      simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    rw [hEq]
    exact Int.sub_nonneg.mpr (Int.add_one_le_of_lt hRange.2)
  have hHi :
      native_int_pow2 (native_nat_to_int w) - 1 - n <
        native_int_pow2 (native_nat_to_int w) := by
    have hEq :
        native_int_pow2 (native_nat_to_int w) - 1 - n =
          native_int_pow2 (native_nat_to_int w) - (1 + n) := by
      simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    rw [hEq]
    exact Int.sub_lt_self _ (Int.add_pos_of_pos_of_nonneg (by decide) hRange.1)
  simpa [native_mod_total] using Int.emod_eq_of_lt hLo hHi

private theorem bitvec_ofInt_not_payload_of_canonical
    (w : Nat) (n : native_Int) :
    native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true ->
    BitVec.ofInt w (native_int_pow2 (native_nat_to_int w) - 1 - n) =
      ~~~(BitVec.ofInt w n) := by
  intro hCan
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_not, BitVec.toNat_ofInt]
  rw [native_int_pow2_nat]
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, native_nat_to_int]
  have hRangeNative := bitvec_payload_range_of_canonical hWidth hCan
  have hPowPosInt : 0 < (2 ^ w : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have hNMod :
      n % (2 ^ w : Int) = n := by
    exact Int.emod_eq_of_lt hRangeNative.1 (by simpa [native_int_pow2_nat] using hRangeNative.2)
  have hUpper : n < (2 ^ w : Int) := by
    simpa [native_int_pow2_nat] using hRangeNative.2
  have hNotLo : 0 <= (2 ^ w : Int) - 1 - n := by
    have hEq :
        (2 ^ w : Int) - 1 - n = (2 ^ w : Int) - (n + 1) := by
      simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    rw [hEq]
    exact Int.sub_nonneg.mpr (Int.add_one_le_of_lt hUpper)
  have hNotHi : (2 ^ w : Int) - 1 - n < (2 ^ w : Int) := by
    have hEq :
        (2 ^ w : Int) - 1 - n = (2 ^ w : Int) - (1 + n) := by
      simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    rw [hEq]
    exact Int.sub_lt_self _ (Int.add_pos_of_pos_of_nonneg (by decide) hRangeNative.1)
  simp [Int.emod_eq_of_lt hNotLo hNotHi, hNMod]
  have hNToNat : ((Int.toNat n : Nat) : Int) = n :=
    Int.toNat_of_nonneg hRangeNative.1
  have hNotToNat :
      (((2 ^ w : Int) - 1 - n).toNat : Int) =
        (2 ^ w : Int) - 1 - n :=
    Int.toNat_of_nonneg hNotLo
  have hRhsInt :
      ((2 ^ w - 1 - Int.toNat n : Nat) : Int) =
        (2 ^ w : Int) - 1 - n := by
    have hOneLe : 1 <= 2 ^ w := Nat.one_le_two_pow
    have hSubOne :
        ((2 ^ w - 1 : Nat) : Int) = (2 ^ w : Int) - 1 :=
      Int.ofNat_sub hOneLe
    have hNLe : Int.toNat n <= 2 ^ w - 1 := by
      have hUpperNat : Int.toNat n < 2 ^ w := by
        have hUpperInt : ((Int.toNat n : Nat) : Int) < (2 ^ w : Int) := by
          rw [hNToNat]
          exact hUpper
        exact_mod_cast hUpperInt
      exact Nat.le_pred_of_lt hUpperNat
    rw [Int.ofNat_sub hNLe, hSubOne, hNToNat]
  exact Int.ofNat.inj (hNotToNat.trans hRhsInt.symm)

private theorem bvxor_eval_bvnot_bvnot_of_canonical
    (w : Nat) (nx ny : native_Int) :
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq ny
        (native_mod_total ny (native_int_pow2 (native_nat_to_int w))) = true ->
    __smtx_model_eval_bvxor
        (__smtx_model_eval_bvnot (SmtValue.Binary (native_nat_to_int w) nx))
        (__smtx_model_eval_bvnot (SmtValue.Binary (native_nat_to_int w) ny)) =
      __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) nx)
        (SmtValue.Binary (native_nat_to_int w) ny) := by
  intro hXCan hYCan
  have hNotX :=
    native_binary_not_mod_of_canonical_nat w nx hXCan
  have hNotY :=
    native_binary_not_mod_of_canonical_nat w ny hYCan
  simp [__smtx_model_eval_bvnot, __smtx_model_eval_bvxor]
  rw [hNotX, hNotY]
  rw [native_binary_xor_mod_eq_toNat, native_binary_xor_mod_eq_toNat]
  have hBvX :=
    bitvec_ofInt_not_payload_of_canonical w nx hXCan
  have hBvY :=
    bitvec_ofInt_not_payload_of_canonical w ny hYCan
  rw [hBvX, hBvY]
  have hId :
      (~~~(BitVec.ofInt w nx) ^^^ ~~~(BitVec.ofInt w ny)) =
        (BitVec.ofInt w nx ^^^ BitVec.ofInt w ny) := by
    rw [← BitVec.xor_allOnes (x := BitVec.ofInt w nx)]
    rw [← BitVec.xor_allOnes (x := BitVec.ofInt w ny)]
    rw [show
        (BitVec.ofInt w nx ^^^ BitVec.allOnes w) ^^^
            (BitVec.ofInt w ny ^^^ BitVec.allOnes w) =
          (BitVec.ofInt w nx ^^^ BitVec.ofInt w ny) ^^^
            (BitVec.allOnes w ^^^ BitVec.allOnes w) by
          ac_rfl]
    rw [BitVec.xor_self, BitVec.xor_zero]
  exact congrArg (fun b : BitVec w => (b.toNat : Int)) hId

private theorem bvnot_eval_canonical
    (w : Nat) (n : native_Int) :
    ∃ p,
      __smtx_model_eval_bvnot (SmtValue.Binary (native_nat_to_int w) n) =
        SmtValue.Binary (native_nat_to_int w) p ∧
      native_zeq p
        (native_mod_total p (native_int_pow2 (native_nat_to_int w))) = true := by
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, native_nat_to_int]
  have hTy :
      __smtx_typeof_value
          (__smtx_model_eval_bvnot
            (SmtValue.Binary (native_nat_to_int w) n)) =
        SmtType.BitVec w := by
    simpa [native_int_to_nat, native_nat_to_int] using
      typeof_value_model_eval_bvnot_value (native_nat_to_int w) n hWidth
  rcases bitvec_value_canonical hTy with ⟨p, hEval⟩
  have hCan :
      native_zeq p
        (native_mod_total p (native_int_pow2 (native_nat_to_int w))) = true :=
    bitvec_payload_canonical (by simpa [hEval] using hTy)
  exact ⟨p, hEval, hCan⟩

private theorem eval_bv_xor_not
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvXorNotTerm x y) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvXorNotLhs x y)) =
      __smtx_model_eval M (__eo_to_smt (bvXorNotRhs x y)) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_xor_not_context x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hNotXTypeSmt, hNilXNe, hNilNotXNe⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, hXCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hYTy with
    ⟨ny, hYEval, hYCan⟩
  have hNilXEval := smt_eval_bvxor_nil M x w hXTypeSmt hNilXNe
  have hNilNotXEval :=
    smt_eval_bvxor_nil M (Term.Apply (Term.UOp UserOp.bvnot) x) w
      hNotXTypeSmt hNilNotXNe
  have hRightInner :
      __smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) ny)
          (SmtValue.Binary (native_nat_to_int w) 0) =
        SmtValue.Binary (native_nat_to_int w) ny :=
    bvxor_right_zero_of_canonical w ny hYCan
  rcases bvnot_eval_canonical w ny with ⟨notY, hNotYEval, hNotYCan⟩
  have hLeftInner :
      __smtx_model_eval_bvxor
          (__smtx_model_eval_bvnot (SmtValue.Binary (native_nat_to_int w) ny))
          (SmtValue.Binary (native_nat_to_int w) 0) =
        __smtx_model_eval_bvnot (SmtValue.Binary (native_nat_to_int w) ny) := by
    rw [hNotYEval]
    exact bvxor_right_zero_of_canonical w notY hNotYCan
  change __smtx_model_eval M
      (SmtTerm.bvxor (SmtTerm.bvnot (__eo_to_smt x))
        (SmtTerm.bvxor (SmtTerm.bvnot (__eo_to_smt y))
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor)
            (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)))))) =
    __smtx_model_eval M
      (SmtTerm.bvxor (__eo_to_smt x)
        (SmtTerm.bvxor (__eo_to_smt y)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))))
  repeat rw [smtx_eval_bvxor_term_eq]
  repeat rw [smtx_eval_bvnot_term_eq]
  rw [hXEval, hYEval, hNilNotXEval, hNilXEval]
  rw [hLeftInner, hRightInner]
  exact bvxor_eval_bvnot_bvnot_of_canonical w nx ny hXCan hYCan

theorem facts_bv_xor_not_term
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvXorNotTerm x y) = Term.Bool ->
    eo_interprets M (bvXorNotTerm x y) true := by
  intro hXTrans hYTrans hResultTy
  have hBool :=
    typed_bv_xor_not_term x y hXTrans hYTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvXorNotLhs x y)))
      (__smtx_model_eval M (__eo_to_smt (bvXorNotRhs x y)))
    rw [eval_bv_xor_not M hM x y hXTrans hYTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvXorNotProgram (x y : Term) : Term :=
  __eo_prog_bv_xor_not x y

private def bvXorNotProgramSkeleton (x y : Term) : Term :=
  let v0 := Term.Apply (Term.UOp UserOp.bvnot) x
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) v0)
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.UOp UserOp.bvnot) y))
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof v0)))))
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) x)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) y)
        (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))))

private theorem bvXorNotProgram_eq_skeleton_of_ne_stuck
    (x y : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    bvXorNotProgram x y = bvXorNotProgramSkeleton x y := by
  intro hXNe hYNe
  cases x <;> cases y <;>
    simp [bvXorNotProgram, bvXorNotProgramSkeleton,
      __eo_prog_bv_xor_not] at hXNe hYNe ⊢

theorem bvXorNotProgram_eq_term_of_type_bool
    (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvXorNotProgram x y) = Term.Bool ->
    bvXorNotProgram x y = bvXorNotTerm x y := by
  intro hXTrans hYTrans hTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hSkeleton := bvXorNotProgram_eq_skeleton_of_ne_stuck x y hXNe hYNe
  by_cases hNilNotX :
      __eo_nil (Term.UOp UserOp.bvxor)
        (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) = Term.Stuck
  · have hProgStuck : bvXorNotProgram x y = Term.Stuck := by
      rw [hSkeleton]
      simp [bvXorNotProgramSkeleton, __eo_mk_apply, hNilNotX]
    rw [hProgStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · by_cases hNilX :
        __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) = Term.Stuck
    · have hProgStuck : bvXorNotProgram x y = Term.Stuck := by
        rw [hSkeleton]
        simp [bvXorNotProgramSkeleton, __eo_mk_apply, hNilNotX, hNilX]
      rw [hProgStuck] at hTy
      have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
        native_decide
      exact False.elim (hBad hTy)
    · rw [hSkeleton]
      simp [bvXorNotProgramSkeleton, bvXorNotTerm, bvXorNotLhs,
        bvXorNotRhs, __eo_mk_apply, hNilNotX, hNilX]

theorem typed_bv_xor_not_program (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvXorNotProgram x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvXorNotProgram x y) := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvXorNotProgram_eq_term_of_type_bool x y hXTrans hYTrans hResultTy
  have hTermTy : __eo_typeof (bvXorNotTerm x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_xor_not_term x y hXTrans hYTrans hTermTy

theorem facts_bv_xor_not_program
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvXorNotProgram x y) = Term.Bool ->
    eo_interprets M (bvXorNotProgram x y) true := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvXorNotProgram_eq_term_of_type_bool x y hXTrans hYTrans hResultTy
  have hTermTy : __eo_typeof (bvXorNotTerm x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_xor_not_term M hM x y hXTrans hYTrans hTermTy

def bvXorDuplicateLhs (x : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
      (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))

def bvXorDuplicateRhs (w : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0)

def bvXorDuplicateTerm (x w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvXorDuplicateLhs x))
    (bvXorDuplicateRhs w)

theorem bv_xor_duplicate_nil_ne (x w : Term) :
    __eo_typeof (bvXorDuplicateTerm x w) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck := by
  intro hTy hNil
  have hLeftNN :
      __eo_typeof (bvXorDuplicateLhs x) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvXorDuplicateLhs x))
        (__eo_typeof (bvXorDuplicateRhs w))
        (by exact hTy)
    exact hOperands.1
  apply hLeftNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof x)
      (__eo_typeof_bvand (__eo_typeof x) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

private theorem bv_at_zero_width_eq_of_type_bitvec
    {w u : Term} :
    __eo_typeof (bvXorDuplicateRhs w) =
      Term.Apply (Term.UOp UserOp.BitVec) u ->
    w = u := by
  intro hTy
  have hW : w ≠ Term.Stuck := by
    intro hW
    subst w
    change __eo_typeof_int_to_bv Term.Stuck Term.Stuck (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) u at hTy
    simp [__eo_typeof_int_to_bv] at hTy
  change __eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) u at hTy
  cases hWTy : __eo_typeof w with
  | UOp op =>
      cases op
      · -- Int width type
        have hTy' :
            __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
                (Term.Boolean true)
                (Term.Apply (Term.UOp UserOp.BitVec) w) =
              Term.Apply (Term.UOp UserOp.BitVec) u := by
          simpa [__eo_typeof_int_to_bv, hWTy, hW] using hTy
        have hReqNe :
            __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
                (Term.Boolean true)
                (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
              Term.Stuck := by
          rw [hTy']
          intro hBad
          cases hBad
        have hCond :=
          support_eo_requires_cond_eq_of_non_stuck hReqNe
        have hReqEq :
            __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
                (Term.Boolean true)
                (Term.Apply (Term.UOp UserOp.BitVec) w) =
              Term.Apply (Term.UOp UserOp.BitVec) w := by
          simp [__eo_requires, hCond, native_ite, native_teq, native_not]
        have hBv :
            Term.Apply (Term.UOp UserOp.BitVec) w =
              Term.Apply (Term.UOp UserOp.BitVec) u :=
          hReqEq.symm.trans hTy'
        cases hBv
        rfl
      all_goals
        exfalso
        simpa [__eo_typeof_int_to_bv, hWTy, hW, __eo_requires,
          __eo_eq, native_ite, native_teq, native_not] using hTy
  | _ =>
      exfalso
      simpa [__eo_typeof_int_to_bv, hWTy, hW, __eo_requires,
        __eo_eq, native_ite, native_teq, native_not] using hTy

theorem bv_xor_duplicate_arg_type_of_bool (x w : Term) :
    __eo_typeof (bvXorDuplicateTerm x w) = Term.Bool ->
    ∃ u, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) u ∧
      w = u ∧ u ≠ Term.Stuck := by
  intro hTy
  have hLeftNN :
      __eo_typeof (bvXorDuplicateLhs x) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvXorDuplicateLhs x))
        (__eo_typeof (bvXorDuplicateRhs w))
        (by exact hTy)
    exact hOperands.1
  have hOuterNN :
      __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
              (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) ≠
        Term.Stuck := by
    exact hLeftNN
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hOuterNN with
    ⟨u, hXTy, hInnerTy⟩
  have hInnerEq :
      __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
        Term.Apply (Term.UOp UserOp.BitVec) u := by
    exact hInnerTy
  rcases eo_typeof_bvand_args_of_eq_bitvec hInnerEq with
    ⟨_hXTyInner, _hNilTy, hUNe⟩
  have hLhsTy :
      __eo_typeof (bvXorDuplicateLhs x) =
        Term.Apply (Term.UOp UserOp.BitVec) u := by
    change __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
            (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
      Term.Apply (Term.UOp UserOp.BitVec) u
    rw [hInnerTy, hXTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hUNe]
  have hTypesEq :
      __eo_typeof (bvXorDuplicateLhs x) =
        __eo_typeof (bvXorDuplicateRhs w) :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof (bvXorDuplicateLhs x))
      (__eo_typeof (bvXorDuplicateRhs w))
      (by exact hTy)
  have hRhsTy :
      __eo_typeof (bvXorDuplicateRhs w) =
        Term.Apply (Term.UOp UserOp.BitVec) u := by
    rw [← hTypesEq]
    exact hLhsTy
  exact ⟨u, hXTy, bv_at_zero_width_eq_of_type_bitvec hRhsTy, hUNe⟩

private theorem native_nat_to_int_of_int_to_nat_of_nonneg (n : native_Int) :
    native_zleq 0 n = true ->
    native_nat_to_int (native_int_to_nat n) = n := by
  intro hNonneg
  have hn : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
    Int.toNat_of_nonneg hn
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem bv_xor_duplicate_context
    (x width : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvXorDuplicateTerm x width) = Term.Bool ->
    ∃ n,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec n ∧
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec n ∧
      width = Term.Numeral (native_nat_to_int n) ∧
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck := by
  intro hXTrans hResultTy
  rcases bv_xor_duplicate_arg_type_of_bool x width hResultTy with
    ⟨u, hXTy, hWidthEqTerm, _hUNe⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x u hXTrans hXTy with
    ⟨n, hUEq, hNonneg, hXSmtTy⟩
  have hWidthEq :
      native_nat_to_int (native_int_to_nat n) = n :=
    native_nat_to_int_of_int_to_nat_of_nonneg n hNonneg
  have hXTypeSmt :
      __eo_to_smt_type (__eo_typeof x) =
        SmtType.BitVec (native_int_to_nat n) := by
    rw [hXTy, hUEq]
    simp [__eo_to_smt_type, hNonneg, native_ite]
  exact ⟨native_int_to_nat n, hXSmtTy, hXTypeSmt,
    by
      rw [hWidthEqTerm, hUEq, hWidthEq],
    bv_xor_duplicate_nil_ne x width hResultTy⟩

private theorem smt_typeof_bv_zero_nat (w : Nat) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral (native_nat_to_int w))) (Term.Numeral 0))) =
      SmtType.BitVec w := by
  have hNonneg : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, native_nat_to_int]
  have hMod0 :
      native_mod_total 0 (native_int_pow2 (native_nat_to_int w)) = 0 := by
    simp [native_mod_total]
  change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral (native_nat_to_int w))
        (SmtTerm.Numeral 0)) =
    SmtType.BitVec w
  have hZeroTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
    rw [__smtx_typeof.eq_def]
  rw [typeof_int_to_bv_eq, hZeroTy]
  simp [__smtx_typeof_int_to_bv, native_ite, hNonneg,
    native_zleq, native_int_to_nat, native_nat_to_int]

private theorem smt_eval_bv_zero_nat (M : SmtModel) (w : Nat) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral (native_nat_to_int w))) (Term.Numeral 0))) =
      SmtValue.Binary (native_nat_to_int w) 0 := by
  have hNonneg : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, native_nat_to_int]
  have hMod0 :
      native_mod_total 0 (native_int_pow2 (native_nat_to_int w)) = 0 := by
    simp [native_mod_total]
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral (native_nat_to_int w))
        (SmtTerm.Numeral 0)) =
    SmtValue.Binary (native_nat_to_int w) 0
  simp [__smtx_model_eval, __smtx_model_eval_int_to_bv, hMod0]

private theorem smt_typeof_bv_xor_duplicate_lhs
    (x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvXorDuplicateLhs x)) =
      SmtType.BitVec w := by
  intro hXTy hXTypeSmt hNilNe
  have hNilTy := smt_typeof_bvxor_nil x w hXTypeSmt hNilNe
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvxor (__eo_to_smt x)
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
        SmtType.BitVec w := by
    rw [smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_2, hXTy, hNilTy, native_nateq,
      native_ite]
  change __smtx_typeof
      (SmtTerm.bvxor (__eo_to_smt x)
        (SmtTerm.bvxor (__eo_to_smt x)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))))) =
    SmtType.BitVec w
  rw [smtx_typeof_bvxor_term_eq]
  simp [__smtx_typeof_bv_op_2, hXTy, hInnerTy, native_nateq,
    native_ite]

theorem typed_bv_xor_duplicate_term (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvXorDuplicateTerm x w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvXorDuplicateTerm x w) := by
  intro hXTrans hResultTy
  rcases bv_xor_duplicate_context x w hXTrans hResultTy with
    ⟨n, hXTy, hXTypeSmt, hWEq, hNilNe⟩
  rw [hWEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvXorDuplicateLhs x)
    (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral (native_nat_to_int n))) (Term.Numeral 0))
    (by
      rw [smt_typeof_bv_xor_duplicate_lhs x n hXTy hXTypeSmt hNilNe,
        smt_typeof_bv_zero_nat n])
    (by
      rw [smt_typeof_bv_xor_duplicate_lhs x n hXTy hXTypeSmt hNilNe]
      simp)

private theorem native_binary_xor_self_mod_nat (w : Nat) (n : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) n n)
        (native_int_pow2 (native_nat_to_int w)) =
      0 := by
  rw [native_binary_xor_mod_eq_toNat]
  simp

private theorem bvxor_self_eval (w : Nat) (n : native_Int) :
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) n)
        (SmtValue.Binary (native_nat_to_int w) n) =
      SmtValue.Binary (native_nat_to_int w) 0 := by
  simp [__smtx_model_eval_bvxor]
  exact native_binary_xor_self_mod_nat w n

private theorem eval_bv_xor_duplicate
    (M : SmtModel) (hM : model_wf M) (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvXorDuplicateTerm x w) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvXorDuplicateLhs x)) =
      __smtx_model_eval M (__eo_to_smt (bvXorDuplicateRhs w)) := by
  intro hXTrans hResultTy
  rcases bv_xor_duplicate_context x w hXTrans hResultTy with
    ⟨n, hXTy, hXTypeSmt, hWEq, hNilNe⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) n hXTy with
    ⟨payload, hXEval, hXCan⟩
  have hNilEval := smt_eval_bvxor_nil M x n hXTypeSmt hNilNe
  have hInner :
      __smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int n) payload)
          (SmtValue.Binary (native_nat_to_int n) 0) =
        SmtValue.Binary (native_nat_to_int n) payload :=
    bvxor_right_zero_of_canonical n payload hXCan
  rw [hWEq]
  change __smtx_model_eval M
      (SmtTerm.bvxor (__eo_to_smt x)
        (SmtTerm.bvxor (__eo_to_smt x)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) ) =
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral (native_nat_to_int n))) (Term.Numeral 0)))
  repeat rw [smtx_eval_bvxor_term_eq]
  rw [hXEval, hNilEval, hInner]
  rw [smt_eval_bv_zero_nat M n]
  exact bvxor_self_eval n payload

theorem facts_bv_xor_duplicate_term
    (M : SmtModel) (hM : model_wf M) (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvXorDuplicateTerm x w) = Term.Bool ->
    eo_interprets M (bvXorDuplicateTerm x w) true := by
  intro hXTrans hResultTy
  have hBool := typed_bv_xor_duplicate_term x w hXTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvXorDuplicateLhs x)))
      (__smtx_model_eval M (__eo_to_smt (bvXorDuplicateRhs w)))
    rw [eval_bv_xor_duplicate M hM x w hXTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvXorDuplicateProgram (x w : Term) : Term :=
  __eo_prog_bv_xor_duplicate x w
    (Proof.pf
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)))

private def bvXorDuplicateProgramSkeleton (x w : Term) : Term :=
  let v0 := Term.Apply (Term.UOp UserOp.bvxor) x
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply v0
        (__eo_mk_apply v0
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))))
    (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))

private theorem bvXorDuplicateProgram_eq_skeleton_of_ne_stuck
    (x w : Term) :
    x ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    bvXorDuplicateProgram x w = bvXorDuplicateProgramSkeleton x w := by
  intro hXNe hWNe
  unfold bvXorDuplicateProgram bvXorDuplicateProgramSkeleton
  rw [__eo_prog_bv_xor_duplicate.eq_3 x w w x hXNe hWNe]
  simp [__eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hXNe, hWNe]

theorem bvXorDuplicateProgram_eq_term_of_type_bool
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvXorDuplicateProgram x w) = Term.Bool ->
    bvXorDuplicateProgram x w = bvXorDuplicateTerm x w := by
  intro hXTrans hWTrans hTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hWNe : w ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  have hSkeleton := bvXorDuplicateProgram_eq_skeleton_of_ne_stuck x w hXNe hWNe
  by_cases hNil :
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) = Term.Stuck
  · have hProgStuck : bvXorDuplicateProgram x w = Term.Stuck := by
      rw [hSkeleton]
      simp [bvXorDuplicateProgramSkeleton, __eo_mk_apply, hNil]
    rw [hProgStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · rw [hSkeleton]
    simp [bvXorDuplicateProgramSkeleton, bvXorDuplicateTerm,
      bvXorDuplicateLhs, bvXorDuplicateRhs, __eo_mk_apply, hNil]

theorem typed_bv_xor_duplicate_program (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvXorDuplicateProgram x w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvXorDuplicateProgram x w) := by
  intro hXTrans hWTrans hResultTy
  have hEq :=
    bvXorDuplicateProgram_eq_term_of_type_bool x w hXTrans hWTrans hResultTy
  have hTermTy : __eo_typeof (bvXorDuplicateTerm x w) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_xor_duplicate_term x w hXTrans hTermTy

theorem facts_bv_xor_duplicate_program
    (M : SmtModel) (hM : model_wf M) (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvXorDuplicateProgram x w) = Term.Bool ->
    eo_interprets M (bvXorDuplicateProgram x w) true := by
  intro hXTrans hWTrans hResultTy
  have hEq :=
    bvXorDuplicateProgram_eq_term_of_type_bool x w hXTrans hWTrans hResultTy
  have hTermTy : __eo_typeof (bvXorDuplicateTerm x w) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_xor_duplicate_term M hM x w hXTrans hTermTy

theorem bv_xor_duplicate_shape_of_ne_stuck (x w P : Term) :
    __eo_prog_bv_xor_duplicate x w (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
      ∃ pw px,
        P =
          Term.Apply (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px) := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_xor_duplicate.eq_1 w (Proof.pf P))
  have hWNe : w ≠ Term.Stuck := by
    intro hW
    subst w
    exact hProg (__eo_prog_bv_xor_duplicate.eq_2 x (Proof.pf P) hXNe)
  refine ⟨hXNe, hWNe, ?_⟩
  by_cases hShape : ∃ pw px,
      P =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) pw)
          (Term.Apply (Term.UOp UserOp._at_bvsize) px)
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_xor_duplicate.eq_4 x w (Proof.pf P) hXNe hWNe (by
        intro pw px hP
        cases hP
        exact hShape ⟨pw, px, rfl⟩)))

def bvNotXorTail (y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) z

def bvNotXorLhs (x y z : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
      (bvNotXorTail y z))

def bvNotXorRhs (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
    (Term.Apply (Term.UOp UserOp.bvnot) x))
    (bvNotXorTail y z)

def bvNotXorTerm (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvNotXorLhs x y z))
    (bvNotXorRhs x y z)

private theorem eo_typeof_bvnot_arg_type_of_ne_stuck
    {A : Term} (h : __eo_typeof_bvnot A ≠ Term.Stuck) :
    ∃ u, A = Term.Apply (Term.UOp UserOp.BitVec) u := by
  cases A <;> simp [__eo_typeof_bvnot] at h ⊢
  case Apply f u =>
    cases f <;> simp [__eo_typeof_bvnot] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_bvnot] at h ⊢

theorem bv_not_xor_args_type_of_bool (x y z : Term) :
    __eo_typeof (bvNotXorTerm x y z) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  have hLeftNN :
      __eo_typeof (bvNotXorLhs x y z) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvNotXorLhs x y z))
        (__eo_typeof (bvNotXorRhs x y z))
        (by exact hTy)
    exact hOperands.1
  rcases eo_typeof_bvnot_arg_type_of_ne_stuck (by
      exact hLeftNN) with
    ⟨w, hInnerTy⟩
  have hOuterEq :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof (bvNotXorTail y z)) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    exact hInnerTy
  rcases eo_typeof_bvand_args_of_eq_bitvec hOuterEq with
    ⟨hXTy, hTailTy, hWNe⟩
  have hTailEq :
      __eo_typeof_bvand (__eo_typeof y) (__eo_typeof z) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    exact hTailTy
  rcases eo_typeof_bvand_args_of_eq_bitvec hTailEq with
    ⟨hYTy, hZTy, _hWNeTail⟩
  exact ⟨w, hXTy, hYTy, hZTy, hWNe⟩

private theorem bv_not_xor_context
    (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvNotXorTerm x y z) = Term.Bool ->
    ∃ w,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w := by
  intro hXTrans hYTrans hZTrans hResultTy
  rcases bv_not_xor_args_type_of_bool x y z hResultTy with
    ⟨wTerm, hXTy, hYTy, hZTy, _hWNe⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x wTerm hXTrans hXTy with
    ⟨n, hWTerm, _hNonneg, hXSmtTy⟩
  subst wTerm
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y (Term.Numeral n)
      hYTrans (by simpa using hYTy) with
    ⟨m, hM, _hMNonneg, hYSmtTy⟩
  cases hM
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width z (Term.Numeral n)
      hZTrans (by simpa using hZTy) with
    ⟨k, hK, _hKNonneg, hZSmtTy⟩
  cases hK
  exact ⟨native_int_to_nat n, hXSmtTy, hYSmtTy, hZSmtTy⟩

private theorem smt_typeof_bv_not_xor_tail
    (y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (bvNotXorTail y z)) =
      SmtType.BitVec w := by
  intro hYTy hZTy
  change __smtx_typeof (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt z)) =
    SmtType.BitVec w
  rw [smtx_typeof_bvxor_term_eq]
  simp [__smtx_typeof_bv_op_2, hYTy, hZTy, native_nateq, native_ite]

private theorem smt_typeof_bv_not_xor_lhs
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (bvNotXorLhs x y z)) =
      SmtType.BitVec w := by
  intro hXTy hYTy hZTy
  have hTailTy := smt_typeof_bv_not_xor_tail y z w hYTy hZTy
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt (bvNotXorTail y z))) =
        SmtType.BitVec w := by
    rw [smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_2, hXTy, hTailTy, native_nateq, native_ite]
  change __smtx_typeof
      (SmtTerm.bvnot
        (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt (bvNotXorTail y z)))) =
    SmtType.BitVec w
  rw [smtx_typeof_bvnot_term_eq]
  simp [__smtx_typeof_bv_op_1, hInnerTy]

private theorem smt_typeof_bv_not_xor_rhs
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (bvNotXorRhs x y z)) =
      SmtType.BitVec w := by
  intro hXTy hYTy hZTy
  have hNotXTy :
      __smtx_typeof (SmtTerm.bvnot (__eo_to_smt x)) = SmtType.BitVec w := by
    rw [smtx_typeof_bvnot_term_eq]
    simp [__smtx_typeof_bv_op_1, hXTy]
  have hTailTy := smt_typeof_bv_not_xor_tail y z w hYTy hZTy
  change __smtx_typeof
      (SmtTerm.bvxor (SmtTerm.bvnot (__eo_to_smt x))
        (__eo_to_smt (bvNotXorTail y z))) =
    SmtType.BitVec w
  rw [smtx_typeof_bvxor_term_eq]
  simp [__smtx_typeof_bv_op_2, hNotXTy, hTailTy, native_nateq,
    native_ite]

theorem typed_bv_not_xor_term (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvNotXorTerm x y z) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvNotXorTerm x y z) := by
  intro hXTrans hYTrans hZTrans hResultTy
  rcases bv_not_xor_context x y z hXTrans hYTrans hZTrans hResultTy with
    ⟨w, hXTy, hYTy, hZTy⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvNotXorLhs x y z) (bvNotXorRhs x y z)
    (by
      rw [smt_typeof_bv_not_xor_lhs x y z w hXTy hYTy hZTy,
        smt_typeof_bv_not_xor_rhs x y z w hXTy hYTy hZTy])
    (by
      rw [smt_typeof_bv_not_xor_lhs x y z w hXTy hYTy hZTy]
      simp)

private theorem bitvec_ofInt_natCast_toNat {w : Nat} (x : BitVec w) :
    BitVec.ofInt w (x.toNat : Int) = x := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp

theorem bitvec_toNat_canonical (w : Nat) (x : BitVec w) :
    native_zeq ((x.toNat : Int))
        (native_mod_total ((x.toNat : Int))
          (native_int_pow2 (native_nat_to_int w))) = true := by
  have hMod :
      native_mod_total ((x.toNat : Int))
          (native_int_pow2 (native_nat_to_int w)) =
        (x.toNat : Int) := by
    rw [native_int_pow2_nat]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast x.isLt)
  simp [native_zeq, hMod]

theorem native_binary_not_mod_eq_toNat_of_canonical
    (w : Nat) (n : native_Int) :
    native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true ->
    native_mod_total (native_binary_not (native_nat_to_int w) n)
        (native_int_pow2 (native_nat_to_int w)) =
      ((~~~(BitVec.ofInt w n)).toNat : Int) := by
  intro hCan
  have hMod := native_binary_not_mod_of_canonical_nat w n hCan
  rw [hMod]
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth hCan
  have hNotLo : 0 <= native_int_pow2 (native_nat_to_int w) - 1 - n := by
    have hEq :
        native_int_pow2 (native_nat_to_int w) - 1 - n =
          native_int_pow2 (native_nat_to_int w) - (n + 1) := by
      simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    rw [hEq]
    exact Int.sub_nonneg.mpr (Int.add_one_le_of_lt hRange.2)
  have hNotHi :
      native_int_pow2 (native_nat_to_int w) - 1 - n <
        native_int_pow2 (native_nat_to_int w) := by
    have hEq :
        native_int_pow2 (native_nat_to_int w) - 1 - n =
          native_int_pow2 (native_nat_to_int w) - (1 + n) := by
      simp [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    rw [hEq]
    exact Int.sub_lt_self _ (Int.add_pos_of_pos_of_nonneg (by decide)
      hRange.1)
  have hPayloadToNat :
      ((BitVec.ofInt w
          (native_int_pow2 (native_nat_to_int w) - 1 - n)).toNat : Int) =
        native_int_pow2 (native_nat_to_int w) - 1 - n := by
    rw [BitVec.toNat_ofInt]
    have hPowCast : ((2 ^ w : Nat) : Int) = (2 ^ w : Int) := by
      norm_cast
    have hEmod :
        (native_int_pow2 (native_nat_to_int w) - 1 - n) %
            ((2 ^ w : Nat) : Int) =
          native_int_pow2 (native_nat_to_int w) - 1 - n := by
      rw [native_int_pow2_nat, hPowCast]
      exact Int.emod_eq_of_lt (by simpa [native_int_pow2_nat] using hNotLo)
        (by simpa [native_int_pow2_nat] using hNotHi)
    rw [show
        ((native_int_pow2 (native_nat_to_int w) - 1 - n) %
            ((2 ^ w : Nat) : Int)).toNat =
          (native_int_pow2 (native_nat_to_int w) - 1 - n).toNat by
        rw [hEmod]]
    exact Int.toNat_of_nonneg hNotLo
  have hBv := bitvec_ofInt_not_payload_of_canonical w n hCan
  have hCong :
      ((BitVec.ofInt w
        (native_int_pow2 (native_nat_to_int w) - 1 - n)).toNat : Int) =
        ((~~~(BitVec.ofInt w n)).toNat : Int) :=
    congrArg (fun b : BitVec w => (b.toNat : Int)) hBv
  rw [← hCong]
  exact hPayloadToNat.symm

private theorem bitvec_not_xor (w : Nat) (x y : BitVec w) :
    ~~~(x ^^^ y) = ~~~x ^^^ y := by
  rw [← BitVec.xor_allOnes (x := x ^^^ y)]
  rw [← BitVec.xor_allOnes (x := x)]
  ac_rfl

private theorem bvnot_bvxor_eval_eq_bvxor_bvnot_of_canonical
    (w : Nat) (nx nt : native_Int) :
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nt
        (native_mod_total nt (native_int_pow2 (native_nat_to_int w))) = true ->
    __smtx_model_eval_bvnot
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) nx)
          (SmtValue.Binary (native_nat_to_int w) nt)) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int w) nx))
        (SmtValue.Binary (native_nat_to_int w) nt) := by
  intro hXCan _hTCan
  let xorPayload :=
    native_mod_total (native_binary_xor (native_nat_to_int w) nx nt)
      (native_int_pow2 (native_nat_to_int w))
  have hXorPayload :
      xorPayload =
        ((BitVec.ofInt w nx ^^^ BitVec.ofInt w nt).toNat : Int) := by
    dsimp [xorPayload]
    exact native_binary_xor_mod_eq_toNat w nx nt
  have hXorCan :
      native_zeq xorPayload
          (native_mod_total xorPayload
            (native_int_pow2 (native_nat_to_int w))) = true := by
    rw [hXorPayload]
    exact bitvec_toNat_canonical w (BitVec.ofInt w nx ^^^ BitVec.ofInt w nt)
  have hXorBv :
      BitVec.ofInt w xorPayload =
        BitVec.ofInt w nx ^^^ BitVec.ofInt w nt := by
    rw [hXorPayload]
    exact bitvec_ofInt_natCast_toNat _
  have hLeftPayload :
      native_mod_total (native_binary_not (native_nat_to_int w) xorPayload)
          (native_int_pow2 (native_nat_to_int w)) =
        ((~~~(BitVec.ofInt w nx ^^^ BitVec.ofInt w nt)).toNat : Int) := by
    rw [native_binary_not_mod_eq_toNat_of_canonical w xorPayload hXorCan,
      hXorBv]
  have hNotXPayload :
      native_mod_total (native_binary_not (native_nat_to_int w) nx)
          (native_int_pow2 (native_nat_to_int w)) =
        ((~~~(BitVec.ofInt w nx)).toNat : Int) :=
    native_binary_not_mod_eq_toNat_of_canonical w nx hXCan
  have hNotXBv :
      BitVec.ofInt w
          (native_mod_total (native_binary_not (native_nat_to_int w) nx)
            (native_int_pow2 (native_nat_to_int w))) =
        ~~~(BitVec.ofInt w nx) := by
    rw [hNotXPayload]
    exact bitvec_ofInt_natCast_toNat _
  have hRightPayload :
      native_mod_total
          (native_binary_xor (native_nat_to_int w)
            (native_mod_total (native_binary_not (native_nat_to_int w) nx)
              (native_int_pow2 (native_nat_to_int w))) nt)
          (native_int_pow2 (native_nat_to_int w)) =
        ((~~~(BitVec.ofInt w nx) ^^^ BitVec.ofInt w nt).toNat : Int) := by
    rw [native_binary_xor_mod_eq_toNat]
    rw [hNotXBv]
  simp [__smtx_model_eval_bvnot, __smtx_model_eval_bvxor]
  change native_mod_total (native_binary_not (native_nat_to_int w) xorPayload)
      (native_int_pow2 (native_nat_to_int w)) =
    native_mod_total
      (native_binary_xor (native_nat_to_int w)
        (native_mod_total (native_binary_not (native_nat_to_int w) nx)
          (native_int_pow2 (native_nat_to_int w))) nt)
      (native_int_pow2 (native_nat_to_int w))
  rw [hLeftPayload, hRightPayload]
  exact congrArg (fun b : BitVec w => (b.toNat : Int))
    (bitvec_not_xor w (BitVec.ofInt w nx) (BitVec.ofInt w nt))

private theorem bitvec_ofInt_allOnes_local (w : Nat) :
    BitVec.ofInt w (native_int_pow2 (native_nat_to_int w) - 1) =
      BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes, native_int_pow2_nat]
  have hPowPos : 0 < (2 ^ w : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have hLower : 0 <= (2 ^ w : Int) - 1 := by
    omega
  have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by
    omega
  change (((2 ^ w : Int) - 1) % (2 ^ w : Int)).toNat = 2 ^ w - 1
  rw [Int.emod_eq_of_lt hLower hUpper]
  have hToNat :
      (((2 ^ w : Int) - 1).toNat : Int) = (2 ^ w : Int) - 1 :=
    Int.toNat_of_nonneg hLower
  have hRhs :
      ((2 ^ w - 1 : Nat) : Int) = (2 ^ w : Int) - 1 :=
    Int.ofNat_sub Nat.one_le_two_pow
  exact Int.ofNat.inj (hToNat.trans hRhs.symm)

/-- XOR with the canonical all-ones value is bitwise negation. -/
theorem bvxor_all_ones_eval_eq_bvnot
    (w : Nat) (n : native_Int) :
    native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true ->
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1))
        (SmtValue.Binary (native_nat_to_int w) n) =
      __smtx_model_eval_bvnot
        (SmtValue.Binary (native_nat_to_int w) n) := by
  intro hCan
  simp [__smtx_model_eval_bvxor, __smtx_model_eval_bvnot]
  rw [native_binary_xor_mod_eq_toNat,
    native_binary_not_mod_eq_toNat_of_canonical w n hCan,
    bitvec_ofInt_allOnes_local]
  rw [BitVec.xor_comm, BitVec.xor_allOnes]

/-- Pushing a negation through the right operand of XOR negates the result. -/
theorem bvxor_bvnot_right_eval_eq_bvnot_bvxor
    (w : Nat) (nx ny : native_Int) :
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq ny
        (native_mod_total ny (native_int_pow2 (native_nat_to_int w))) = true ->
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) nx)
        (__smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int w) ny)) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) nx)
          (SmtValue.Binary (native_nat_to_int w) ny)) := by
  intro hXCan hYCan
  let notY :=
    native_mod_total (native_binary_not (native_nat_to_int w) ny)
      (native_int_pow2 (native_nat_to_int w))
  have hNotY :
      __smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int w) ny) =
        SmtValue.Binary (native_nat_to_int w) notY := by
    simp [notY, __smtx_model_eval_bvnot]
  calc
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) nx)
        (__smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int w) ny)) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int w) ny))
        (SmtValue.Binary (native_nat_to_int w) nx) := by
          rw [hNotY]
          exact bvxor_eval_comm w nx notY
    _ = __smtx_model_eval_bvnot
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) ny)
          (SmtValue.Binary (native_nat_to_int w) nx)) :=
      (bvnot_bvxor_eval_eq_bvxor_bvnot_of_canonical
        w ny nx hYCan hXCan).symm
    _ = __smtx_model_eval_bvnot
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) nx)
          (SmtValue.Binary (native_nat_to_int w) ny)) := by
      rw [bvxor_eval_comm w ny nx]

private theorem eval_bv_not_xor
    (M : SmtModel) (hM : model_wf M) (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvNotXorTerm x y z) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvNotXorLhs x y z)) =
      __smtx_model_eval M (__eo_to_smt (bvNotXorRhs x y z)) := by
  intro hXTrans hYTrans hZTrans hResultTy
  rcases bv_not_xor_context x y z hXTrans hYTrans hZTrans hResultTy with
    ⟨w, hXTy, hYTy, hZTy⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, hXCan⟩
  have hTailTy := smt_typeof_bv_not_xor_tail y z w hYTy hZTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt (bvNotXorTail y z)) w hTailTy with
    ⟨nt, hTailEval, hTailCan⟩
  change __smtx_model_eval M
      (SmtTerm.bvnot
        (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt (bvNotXorTail y z)))) =
    __smtx_model_eval M
      (SmtTerm.bvxor (SmtTerm.bvnot (__eo_to_smt x))
        (__eo_to_smt (bvNotXorTail y z)))
  rw [smtx_eval_bvnot_term_eq]
  rw [smtx_eval_bvxor_term_eq]
  rw [smtx_eval_bvxor_term_eq]
  rw [smtx_eval_bvnot_term_eq]
  rw [hXEval, hTailEval]
  exact bvnot_bvxor_eval_eq_bvxor_bvnot_of_canonical w nx nt hXCan hTailCan

theorem facts_bv_not_xor_term
    (M : SmtModel) (hM : model_wf M) (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvNotXorTerm x y z) = Term.Bool ->
    eo_interprets M (bvNotXorTerm x y z) true := by
  intro hXTrans hYTrans hZTrans hResultTy
  have hBool :=
    typed_bv_not_xor_term x y z hXTrans hYTrans hZTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvNotXorLhs x y z)))
      (__smtx_model_eval M (__eo_to_smt (bvNotXorRhs x y z)))
    rw [eval_bv_not_xor M hM x y z hXTrans hYTrans hZTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvNotXorProgram (x y z : Term) : Term :=
  __eo_prog_bv_not_xor x y z

private theorem bvNotXorProgram_eq_term_of_ne_stuck
    (x y z : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    z ≠ Term.Stuck ->
    bvNotXorProgram x y z = bvNotXorTerm x y z := by
  intro hXNe hYNe hZNe
  cases x <;> cases y <;> cases z <;>
    simp [bvNotXorProgram, bvNotXorTerm, bvNotXorLhs, bvNotXorRhs,
      bvNotXorTail, __eo_prog_bv_not_xor] at hXNe hYNe hZNe ⊢

theorem bvNotXorProgram_eq_term_of_type_bool
    (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvNotXorProgram x y z) = Term.Bool ->
    bvNotXorProgram x y z = bvNotXorTerm x y z := by
  intro hXTrans hYTrans hZTrans _hTy
  exact bvNotXorProgram_eq_term_of_ne_stuck x y z
    (RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans)
    (RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans)
    (RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans)

theorem typed_bv_not_xor_program (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvNotXorProgram x y z) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvNotXorProgram x y z) := by
  intro hXTrans hYTrans hZTrans hResultTy
  have hEq :=
    bvNotXorProgram_eq_term_of_type_bool x y z hXTrans hYTrans hZTrans
      hResultTy
  have hTermTy : __eo_typeof (bvNotXorTerm x y z) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_not_xor_term x y z hXTrans hYTrans hZTrans hTermTy

theorem facts_bv_not_xor_program
    (M : SmtModel) (hM : model_wf M) (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvNotXorProgram x y z) = Term.Bool ->
    eo_interprets M (bvNotXorProgram x y z) true := by
  intro hXTrans hYTrans hZTrans hResultTy
  have hEq :=
    bvNotXorProgram_eq_term_of_type_bool x y z hXTrans hYTrans hZTrans
      hResultTy
  have hTermTy : __eo_typeof (bvNotXorTerm x y z) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_not_xor_term M hM x y z hXTrans hYTrans hZTrans hTermTy

def bvEqXorSolveLhsXor (x y : Term) : Term :=
  bvCommutativeXorLhs x y

def bvEqXorSolveRhsXor (y z : Term) : Term :=
  bvCommutativeXorLhs z y

def bvEqXorSolveLeftEq (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvEqXorSolveLhsXor x y)) z

def bvEqXorSolveRightEq (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) (bvEqXorSolveRhsXor y z)

def bvEqXorSolveBody (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvEqXorSolveLeftEq x y z))
    (bvEqXorSolveRightEq x y z)

def bvEqXorSolveTerm (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvEqXorSolveBody x y z))
    (Term.Boolean true)

private theorem eo_typeof_eq_bool_of_ne_stuck_local (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at h ⊢
  all_goals
    assumption

private theorem bv_eq_xor_solve_body_type_of_result_type
    (x y z : Term) :
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    __eo_typeof (bvEqXorSolveBody x y z) = Term.Bool := by
  intro hTy
  change __eo_typeof_eq (__eo_typeof (bvEqXorSolveBody x y z)) Term.Bool =
    Term.Bool at hTy
  exact support_eo_typeof_eq_bool_operands_eq
    (__eo_typeof (bvEqXorSolveBody x y z)) Term.Bool hTy

private theorem bv_eq_xor_solve_left_eq_type_of_result_type
    (x y z : Term) :
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    __eo_typeof (bvEqXorSolveLeftEq x y z) = Term.Bool := by
  intro hTy
  have hBodyTy := bv_eq_xor_solve_body_type_of_result_type x y z hTy
  have hLeftNN :
      __eo_typeof (bvEqXorSolveLeftEq x y z) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvEqXorSolveLeftEq x y z))
      (__eo_typeof (bvEqXorSolveRightEq x y z))
      (by exact hBodyTy)).1
  change __eo_typeof_eq (__eo_typeof (bvEqXorSolveLhsXor x y))
      (__eo_typeof z) = Term.Bool
  apply eo_typeof_eq_bool_of_ne_stuck_local
  exact hLeftNN

private theorem bv_eq_xor_solve_right_eq_type_of_result_type
    (x y z : Term) :
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    __eo_typeof (bvEqXorSolveRightEq x y z) = Term.Bool := by
  intro hTy
  have hBodyTy := bv_eq_xor_solve_body_type_of_result_type x y z hTy
  have hRightNN :
      __eo_typeof (bvEqXorSolveRightEq x y z) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvEqXorSolveLeftEq x y z))
      (__eo_typeof (bvEqXorSolveRightEq x y z))
      (by exact hBodyTy)).2
  change __eo_typeof_eq (__eo_typeof x)
      (__eo_typeof (bvEqXorSolveRhsXor y z)) = Term.Bool
  apply eo_typeof_eq_bool_of_ne_stuck_local
  exact hRightNN

theorem bv_eq_xor_solve_args_type_of_bool (x y z : Term) :
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  have hLeftEqTy := bv_eq_xor_solve_left_eq_type_of_result_type x y z hTy
  have hLhsXorNN :
      __eo_typeof (bvEqXorSolveLhsXor x y) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvEqXorSolveLhsXor x y)) (__eo_typeof z)
      (by exact hLeftEqTy)).1
  have hLhsZEq :
      __eo_typeof (bvEqXorSolveLhsXor x y) = __eo_typeof z :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof (bvEqXorSolveLhsXor x y)) (__eo_typeof z)
      (by exact hLeftEqTy)
  have hOuterNN :
      __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
              (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) ≠
        Term.Stuck := by
    exact hLhsXorNN
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hOuterNN with
    ⟨w, hXTy, hInnerTy⟩
  have hInnerEq :
      __eo_typeof_bvand (__eo_typeof y)
          (__eo_typeof (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x))) =
        Term.Apply (Term.UOp UserOp.BitVec) w :=
    hInnerTy
  rcases eo_typeof_bvand_args_of_eq_bitvec hInnerEq with
    ⟨hYTy, _hNilTy, hWNe⟩
  have hLhsXorTy :
      __eo_typeof (bvEqXorSolveLhsXor x y) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    change __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
            (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
      Term.Apply (Term.UOp UserOp.BitVec) w
    have hInnerTy' :
        __eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
              (__eo_nil (Term.UOp UserOp.bvxor)
                (Term.Apply (Term.UOp UserOp.BitVec) w))) =
          Term.Apply (Term.UOp UserOp.BitVec) w := by
      simpa [hXTy] using hInnerTy
    rw [hXTy, hInnerTy']
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hWNe]
  have hZTy : __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) w := by
    rw [← hLhsZEq, hLhsXorTy]
  exact ⟨w, hXTy, hYTy, hZTy, hWNe⟩

theorem bv_eq_xor_solve_nil_x_ne (x y z : Term) :
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck := by
  intro hTy hNil
  have hLeftEqTy := bv_eq_xor_solve_left_eq_type_of_result_type x y z hTy
  have hLhsXorNN :
      __eo_typeof (bvEqXorSolveLhsXor x y) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvEqXorSolveLhsXor x y)) (__eo_typeof z)
      (by exact hLeftEqTy)).1
  apply hLhsXorNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof x)
      (__eo_typeof_bvand (__eo_typeof y) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

theorem bv_eq_xor_solve_nil_z_ne (x y z : Term) :
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z) ≠ Term.Stuck := by
  intro hTy hNil
  have hRightEqTy := bv_eq_xor_solve_right_eq_type_of_result_type x y z hTy
  have hRhsXorNN :
      __eo_typeof (bvEqXorSolveRhsXor y z) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof x) (__eo_typeof (bvEqXorSolveRhsXor y z))
      (by exact hRightEqTy)).2
  apply hRhsXorNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) z)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y)
          (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof z)
      (__eo_typeof_bvand (__eo_typeof y) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

private theorem bv_eq_xor_solve_context
    (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    ∃ w,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof z) = SmtType.BitVec w ∧
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ∧
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z) ≠ Term.Stuck := by
  intro hXTrans hYTrans hZTrans hResultTy
  rcases bv_eq_xor_solve_args_type_of_bool x y z hResultTy with
    ⟨wTerm, hXTy, hYTy, hZTy, _hWNe⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x wTerm hXTrans hXTy with
    ⟨n, hWTerm, hNonneg, hXSmtTy⟩
  subst wTerm
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y (Term.Numeral n)
      hYTrans (by simpa using hYTy) with
    ⟨m, hM, _hMNonneg, hYSmtTy⟩
  cases hM
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width z (Term.Numeral n)
      hZTrans (by simpa using hZTy) with
    ⟨k, hK, _hKNonneg, hZSmtTy⟩
  cases hK
  have hXTypeSmt :
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec (native_int_to_nat n) := by
    rw [hXTy]
    simp [__eo_to_smt_type, hNonneg, native_ite]
  have hZTypeSmt :
      __eo_to_smt_type (__eo_typeof z) = SmtType.BitVec (native_int_to_nat n) := by
    rw [hZTy]
    simp [__eo_to_smt_type, hNonneg, native_ite]
  exact ⟨native_int_to_nat n, hXSmtTy, hYSmtTy, hZSmtTy, hXTypeSmt,
    hZTypeSmt, bv_eq_xor_solve_nil_x_ne x y z hResultTy,
    bv_eq_xor_solve_nil_z_ne x y z hResultTy⟩

private theorem smt_typeof_eq_same_non_none_local
    (a b : SmtTerm) (T : SmtType) :
    __smtx_typeof a = T ->
    __smtx_typeof b = T ->
    T ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.eq a b) = SmtType.Bool := by
  intro ha hb hT
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [ha, hb]
  cases T <;>
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_Teq,
      native_ite] at hT ⊢

private theorem smt_typeof_boolean_local (b : Bool) :
    __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smt_typeof_bv_eq_xor_solve_lhs_xor
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvEqXorSolveLhsXor x y)) =
      SmtType.BitVec w := by
  intro hXTy hYTy hXTypeSmt hNilXNe
  simpa [bvEqXorSolveLhsXor] using
    smt_typeof_bv_comm_xor_lhs x y w hXTy hYTy hXTypeSmt hNilXNe

private theorem smt_typeof_bv_eq_xor_solve_rhs_xor
    (y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof z) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvEqXorSolveRhsXor y z)) =
      SmtType.BitVec w := by
  intro hYTy hZTy hZTypeSmt hNilZNe
  simpa [bvEqXorSolveRhsXor] using
    smt_typeof_bv_comm_xor_lhs z y w hZTy hYTy hZTypeSmt hNilZNe

private theorem smt_typeof_bv_eq_xor_solve_left_eq
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvEqXorSolveLeftEq x y z)) =
      SmtType.Bool := by
  intro hXTy hYTy hZTy hXTypeSmt hNilXNe
  change __smtx_typeof
      (SmtTerm.eq (__eo_to_smt (bvEqXorSolveLhsXor x y)) (__eo_to_smt z)) =
    SmtType.Bool
  exact smt_typeof_eq_same_non_none_local _ _ (SmtType.BitVec w)
    (smt_typeof_bv_eq_xor_solve_lhs_xor x y w hXTy hYTy hXTypeSmt hNilXNe)
    hZTy (by intro h; cases h)

private theorem smt_typeof_bv_eq_xor_solve_right_eq
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof z) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvEqXorSolveRightEq x y z)) =
      SmtType.Bool := by
  intro hXTy hYTy hZTy hZTypeSmt hNilZNe
  change __smtx_typeof
      (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (bvEqXorSolveRhsXor y z))) =
    SmtType.Bool
  exact smt_typeof_eq_same_non_none_local _ _ (SmtType.BitVec w)
    hXTy
    (smt_typeof_bv_eq_xor_solve_rhs_xor y z w hYTy hZTy hZTypeSmt hNilZNe)
    (by intro h; cases h)

private theorem smt_typeof_bv_eq_xor_solve_body
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof z) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvEqXorSolveBody x y z)) =
      SmtType.Bool := by
  intro hXTy hYTy hZTy hXTypeSmt hZTypeSmt hNilXNe hNilZNe
  have hLeftTy :=
    smt_typeof_bv_eq_xor_solve_left_eq x y z w hXTy hYTy hZTy
      hXTypeSmt hNilXNe
  have hRightTy :=
    smt_typeof_bv_eq_xor_solve_right_eq x y z w hXTy hYTy hZTy
      hZTypeSmt hNilZNe
  change __smtx_typeof
      (SmtTerm.eq (__eo_to_smt (bvEqXorSolveLeftEq x y z))
        (__eo_to_smt (bvEqXorSolveRightEq x y z))) =
    SmtType.Bool
  exact smt_typeof_eq_same_non_none_local _ _ SmtType.Bool hLeftTy hRightTy
    (by intro h; cases h)

theorem typed_bv_eq_xor_solve_term (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvEqXorSolveTerm x y z) := by
  intro hXTrans hYTrans hZTrans hResultTy
  rcases bv_eq_xor_solve_context x y z hXTrans hYTrans hZTrans hResultTy with
    ⟨w, hXTy, hYTy, hZTy, hXTypeSmt, hZTypeSmt, hNilXNe, hNilZNe⟩
  have hBodyTy :=
    smt_typeof_bv_eq_xor_solve_body x y z w hXTy hYTy hZTy hXTypeSmt
      hZTypeSmt hNilXNe hNilZNe
  change __smtx_typeof
      (SmtTerm.eq (__eo_to_smt (bvEqXorSolveBody x y z))
        (SmtTerm.Boolean true)) =
    SmtType.Bool
  exact smt_typeof_eq_same_non_none_local _ _ SmtType.Bool hBodyTy
    (smt_typeof_boolean_local true) (by intro h; cases h)

private theorem bitvec_xor_eq_solve (w : Nat) (x y z : BitVec w) :
    (x ^^^ y = z) ↔ (x = z ^^^ y) := by
  constructor
  · intro h
    rw [← h]
    rw [BitVec.xor_assoc]
    simp
  · intro h
    rw [h]
    rw [BitVec.xor_assoc]
    simp

theorem bitvec_ofInt_toNat_int_of_canonical
    (w : Nat) (n : native_Int) :
    native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true ->
    ((BitVec.ofInt w n).toNat : Int) = n := by
  intro hCan
  have hMod : native_mod_total n (native_int_pow2 (native_nat_to_int w)) = n := by
    have hEq :
        n = native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hCan
    exact hEq.symm
  exact (native_mod_pow2_eq_bitvec_toNat w n).symm.trans hMod

private theorem bvxor_eq_solve_payload_iff
    (w : Nat) (nx ny nz : native_Int) :
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nz
        (native_mod_total nz (native_int_pow2 (native_nat_to_int w))) = true ->
    (native_mod_total (native_binary_xor (native_nat_to_int w) nx ny)
        (native_int_pow2 (native_nat_to_int w)) = nz ↔
      nx = native_mod_total (native_binary_xor (native_nat_to_int w) nz ny)
        (native_int_pow2 (native_nat_to_int w))) := by
  intro hXCan hZCan
  have hXToNat := bitvec_ofInt_toNat_int_of_canonical w nx hXCan
  have hZToNat := bitvec_ofInt_toNat_int_of_canonical w nz hZCan
  have hLeftPayload := native_binary_xor_mod_eq_toNat w nx ny
  have hRightPayload := native_binary_xor_mod_eq_toNat w nz ny
  constructor
  · intro h
    have hBvLeft :
        BitVec.ofInt w nx ^^^ BitVec.ofInt w ny = BitVec.ofInt w nz := by
      apply BitVec.eq_of_toNat_eq
      apply Int.ofNat.inj
      change ((BitVec.ofInt w nx ^^^ BitVec.ofInt w ny).toNat : Int) =
        ((BitVec.ofInt w nz).toNat : Int)
      rw [← hLeftPayload, h, hZToNat]
    have hBvRight :
        BitVec.ofInt w nx = BitVec.ofInt w nz ^^^ BitVec.ofInt w ny :=
      (bitvec_xor_eq_solve w (BitVec.ofInt w nx) (BitVec.ofInt w ny)
        (BitVec.ofInt w nz)).mp hBvLeft
    have hPayloadEq :
        ((BitVec.ofInt w nx).toNat : Int) =
          ((BitVec.ofInt w nz ^^^ BitVec.ofInt w ny).toNat : Int) := by
      exact congrArg (fun b : BitVec w => (b.toNat : Int)) hBvRight
    rw [hXToNat, ← hRightPayload] at hPayloadEq
    exact hPayloadEq
  · intro h
    have hBvRight :
        BitVec.ofInt w nx = BitVec.ofInt w nz ^^^ BitVec.ofInt w ny := by
      apply BitVec.eq_of_toNat_eq
      apply Int.ofNat.inj
      change ((BitVec.ofInt w nx).toNat : Int) =
        ((BitVec.ofInt w nz ^^^ BitVec.ofInt w ny).toNat : Int)
      rw [hXToNat, ← hRightPayload]
      exact h
    have hBvLeft :
        BitVec.ofInt w nx ^^^ BitVec.ofInt w ny = BitVec.ofInt w nz :=
      (bitvec_xor_eq_solve w (BitVec.ofInt w nx) (BitVec.ofInt w ny)
        (BitVec.ofInt w nz)).mpr hBvRight
    have hPayloadEq :
        ((BitVec.ofInt w nx ^^^ BitVec.ofInt w ny).toNat : Int) =
          ((BitVec.ofInt w nz).toNat : Int) := by
      exact congrArg (fun b : BitVec w => (b.toNat : Int)) hBvLeft
    rw [← hLeftPayload, hZToNat] at hPayloadEq
    exact hPayloadEq

private theorem native_veq_binary_same_width_eq_of_iff
    {w n1 n2 m1 m2 : native_Int}
    (hiff : (n1 = n2 ↔ m1 = m2)) :
    native_veq (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      native_veq (SmtValue.Binary w m1) (SmtValue.Binary w m2) := by
  by_cases hn : n1 = n2
  · have hm : m1 = m2 := hiff.mp hn
    subst n2
    subst m2
    simp [native_veq]
  · have hm : m1 ≠ m2 := by
      intro h
      exact hn (hiff.mpr h)
    simp [native_veq, hn, hm]

private theorem native_veq_bvxor_solve
    (w : Nat) (nx ny nz : native_Int) :
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nz
        (native_mod_total nz (native_int_pow2 (native_nat_to_int w))) = true ->
    native_veq
        (SmtValue.Binary (native_nat_to_int w)
          (native_mod_total
            (native_binary_xor (native_nat_to_int w) nx ny)
            (native_int_pow2 (native_nat_to_int w))))
        (SmtValue.Binary (native_nat_to_int w) nz) =
      native_veq
        (SmtValue.Binary (native_nat_to_int w) nx)
        (SmtValue.Binary (native_nat_to_int w)
          (native_mod_total
            (native_binary_xor (native_nat_to_int w) nz ny)
            (native_int_pow2 (native_nat_to_int w)))) := by
  intro hXCan hZCan
  exact native_veq_binary_same_width_eq_of_iff
    (bvxor_eq_solve_payload_iff w nx ny nz hXCan hZCan)

private theorem eval_bv_eq_xor_solve_body
    (M : SmtModel) (hM : model_wf M) (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvEqXorSolveBody x y z)) =
      SmtValue.Boolean true := by
  intro hXTrans hYTrans hZTrans hResultTy
  rcases bv_eq_xor_solve_context x y z hXTrans hYTrans hZTrans hResultTy with
    ⟨w, hXTy, hYTy, hZTy, hXTypeSmt, hZTypeSmt, hNilXNe, hNilZNe⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, hXCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hYTy with
    ⟨ny, hYEval, hYCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt z) w hZTy with
    ⟨nz, hZEval, hZCan⟩
  have hNilXEval := smt_eval_bvxor_nil M x w hXTypeSmt hNilXNe
  have hNilZEval := smt_eval_bvxor_nil M z w hZTypeSmt hNilZNe
  change __smtx_model_eval M
      (SmtTerm.eq
        (SmtTerm.eq
          (SmtTerm.bvxor (__eo_to_smt x)
            (SmtTerm.bvxor (__eo_to_smt y)
              (__eo_to_smt
                (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))))
          (__eo_to_smt z))
        (SmtTerm.eq (__eo_to_smt x)
          (SmtTerm.bvxor (__eo_to_smt z)
            (SmtTerm.bvxor (__eo_to_smt y)
              (__eo_to_smt
                (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z))))))) =
    SmtValue.Boolean true
  repeat rw [smtx_eval_eq_term_eq]
  repeat rw [smtx_eval_bvxor_term_eq]
  rw [hXEval, hYEval, hZEval, hNilXEval, hNilZEval]
  rw [bvxor_right_zero_of_canonical w ny hYCan]
  change __smtx_model_eval_eq
      (__smtx_model_eval_eq
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) nx)
          (SmtValue.Binary (native_nat_to_int w) ny))
        (SmtValue.Binary (native_nat_to_int w) nz))
      (__smtx_model_eval_eq
        (SmtValue.Binary (native_nat_to_int w) nx)
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) nz)
          (SmtValue.Binary (native_nat_to_int w) ny))) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval_eq, __smtx_model_eval_bvxor]
  rw [native_veq_bvxor_solve w nx ny nz hXCan hZCan]
  simp [native_veq]

theorem facts_bv_eq_xor_solve_term
    (M : SmtModel) (hM : model_wf M) (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool ->
    eo_interprets M (bvEqXorSolveTerm x y z) true := by
  intro hXTrans hYTrans hZTrans hResultTy
  have hBool :=
    typed_bv_eq_xor_solve_term x y z hXTrans hYTrans hZTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [eval_bv_eq_xor_solve_body M hM x y z hXTrans hYTrans hZTrans hResultTy]
    change RuleProofs.smt_value_rel (SmtValue.Boolean true)
      (__smtx_model_eval M (SmtTerm.Boolean true))
    rw [__smtx_model_eval.eq_def] <;> simp only
    exact RuleProofs.smt_value_rel_refl _

def bvEqXorSolveProgram (x y z : Term) : Term :=
  __eo_prog_bv_eq_xor_solve x y z

private def bvEqXorSolveProgramSkeleton (x y z : Term) : Term :=
  let v0 := Term.Apply (Term.UOp UserOp.bvxor) y
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.eq)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) x)
                (__eo_mk_apply v0
                  (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x)))))
            z))
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) x)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) z)
            (__eo_mk_apply v0
              (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z)))))))
    (Term.Boolean true)

private theorem bvEqXorSolveProgram_eq_skeleton_of_ne_stuck
    (x y z : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    z ≠ Term.Stuck ->
    bvEqXorSolveProgram x y z = bvEqXorSolveProgramSkeleton x y z := by
  intro hXNe hYNe hZNe
  cases x <;> cases y <;> cases z <;>
    simp [bvEqXorSolveProgram, bvEqXorSolveProgramSkeleton,
      __eo_prog_bv_eq_xor_solve] at hXNe hYNe hZNe ⊢

theorem bvEqXorSolveProgram_eq_term_of_type_bool
    (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvEqXorSolveProgram x y z) = Term.Bool ->
    bvEqXorSolveProgram x y z = bvEqXorSolveTerm x y z := by
  intro hXTrans hYTrans hZTrans hTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZNe : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hSkeleton := bvEqXorSolveProgram_eq_skeleton_of_ne_stuck
    x y z hXNe hYNe hZNe
  by_cases hNilX :
      __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof x) = Term.Stuck
  · have hProgStuck : bvEqXorSolveProgram x y z = Term.Stuck := by
      rw [hSkeleton]
      simp [bvEqXorSolveProgramSkeleton, __eo_mk_apply, hNilX]
    rw [hProgStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · by_cases hNilZ :
        __eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof z) = Term.Stuck
    · have hProgStuck : bvEqXorSolveProgram x y z = Term.Stuck := by
        rw [hSkeleton]
        simp [bvEqXorSolveProgramSkeleton, __eo_mk_apply, hNilX, hNilZ]
      rw [hProgStuck] at hTy
      have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
        native_decide
      exact False.elim (hBad hTy)
    · rw [hSkeleton]
      simp [bvEqXorSolveProgramSkeleton, bvEqXorSolveTerm,
        bvEqXorSolveBody, bvEqXorSolveLeftEq, bvEqXorSolveRightEq,
        bvEqXorSolveLhsXor, bvEqXorSolveRhsXor, bvCommutativeXorLhs,
        __eo_mk_apply, hNilX, hNilZ]

theorem typed_bv_eq_xor_solve_program (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvEqXorSolveProgram x y z) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvEqXorSolveProgram x y z) := by
  intro hXTrans hYTrans hZTrans hResultTy
  have hEq :=
    bvEqXorSolveProgram_eq_term_of_type_bool x y z hXTrans hYTrans hZTrans
      hResultTy
  have hTermTy : __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_eq_xor_solve_term x y z hXTrans hYTrans hZTrans hTermTy

theorem facts_bv_eq_xor_solve_program
    (M : SmtModel) (hM : model_wf M) (x y z : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof (bvEqXorSolveProgram x y z) = Term.Bool ->
    eo_interprets M (bvEqXorSolveProgram x y z) true := by
  intro hXTrans hYTrans hZTrans hResultTy
  have hEq :=
    bvEqXorSolveProgram_eq_term_of_type_bool x y z hXTrans hYTrans hZTrans
      hResultTy
  have hTermTy : __eo_typeof (bvEqXorSolveTerm x y z) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_eq_xor_solve_term M hM x y z hXTrans hYTrans hZTrans
    hTermTy

/-! Algebraic evaluator identities used by the n-ary XOR simplification
rules.  Stating them at the `SmtValue` level keeps the list-normalization
proofs independent of the evaluator's payload representation. -/

private def canonicalBitVecValue (w : Nat) (x : BitVec w) : SmtValue :=
  SmtValue.Binary (native_nat_to_int w) (x.toNat : Int)

private theorem canonicalBitVecValue_of_payload
    (w : Nat) (n : native_Int) :
    native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true ->
    SmtValue.Binary (native_nat_to_int w) n =
      canonicalBitVecValue w (BitVec.ofInt w n) := by
  intro hCan
  unfold canonicalBitVecValue
  rw [bitvec_ofInt_toNat_int_of_canonical w n hCan]

private theorem eval_bvxor_canonicalBitVecValue
    (w : Nat) (x y : BitVec w) :
    __smtx_model_eval_bvxor
        (canonicalBitVecValue w x) (canonicalBitVecValue w y) =
      canonicalBitVecValue w (x ^^^ y) := by
  simp only [canonicalBitVecValue, __smtx_model_eval_bvxor]
  rw [native_binary_xor_mod_eq_toNat]
  simp [bitvec_ofInt_natCast_toNat]

private theorem eval_bvnot_canonicalBitVecValue
    (w : Nat) (x : BitVec w) :
    __smtx_model_eval_bvnot (canonicalBitVecValue w x) =
      canonicalBitVecValue w (~~~x) := by
  simp only [canonicalBitVecValue, __smtx_model_eval_bvnot]
  rw [native_binary_not_mod_eq_toNat_of_canonical w (x.toNat : Int)
    (bitvec_toNat_canonical w x)]
  simp [bitvec_ofInt_natCast_toNat]

private theorem bitvec_xor_not_self_local
    (w : Nat) (x : BitVec w) :
    x ^^^ ~~~x = BitVec.allOnes w := by
  rw [← BitVec.xor_allOnes (x := x)]
  rw [← BitVec.xor_assoc, BitVec.xor_self]
  simp

/-- Two equal payloads cancel even when separated inside a right-associated
XOR spine. -/
theorem bvxor_cancel_nested_eval
    (w : Nat) (na nx nb nc : native_Int) :
    native_zeq na
        (native_mod_total na (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nb
        (native_mod_total nb (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nc
        (native_mod_total nc (native_int_pow2 (native_nat_to_int w))) = true ->
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) na)
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) nx)
          (__smtx_model_eval_bvxor
            (SmtValue.Binary (native_nat_to_int w) nb)
            (__smtx_model_eval_bvxor
              (SmtValue.Binary (native_nat_to_int w) nx)
              (SmtValue.Binary (native_nat_to_int w) nc)))) =
      __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) na)
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) nb)
          (SmtValue.Binary (native_nat_to_int w) nc)) := by
  intro hA hX hB hC
  rw [canonicalBitVecValue_of_payload w na hA,
    canonicalBitVecValue_of_payload w nx hX,
    canonicalBitVecValue_of_payload w nb hB,
    canonicalBitVecValue_of_payload w nc hC]
  repeat rw [eval_bvxor_canonicalBitVecValue]
  congr 1
  calc
    BitVec.ofInt w na ^^^
          (BitVec.ofInt w nx ^^^
            (BitVec.ofInt w nb ^^^
              (BitVec.ofInt w nx ^^^ BitVec.ofInt w nc))) =
        BitVec.ofInt w na ^^^
          (BitVec.ofInt w nb ^^^
            ((BitVec.ofInt w nx ^^^ BitVec.ofInt w nx) ^^^
              BitVec.ofInt w nc)) := by ac_rfl
    _ = BitVec.ofInt w na ^^^
          (BitVec.ofInt w nb ^^^ BitVec.ofInt w nc) := by simp

/-- An `x`/`bvnot x` pair in a right-associated XOR spine negates the
remaining aggregate. -/
theorem bvxor_not_cancel_nested_eval
    (w : Nat) (na nx nb nc : native_Int) :
    native_zeq na
        (native_mod_total na (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nb
        (native_mod_total nb (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nc
        (native_mod_total nc (native_int_pow2 (native_nat_to_int w))) = true ->
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) na)
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) nx)
          (__smtx_model_eval_bvxor
            (SmtValue.Binary (native_nat_to_int w) nb)
            (__smtx_model_eval_bvxor
              (__smtx_model_eval_bvnot
                (SmtValue.Binary (native_nat_to_int w) nx))
              (SmtValue.Binary (native_nat_to_int w) nc)))) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) na)
          (__smtx_model_eval_bvxor
            (SmtValue.Binary (native_nat_to_int w) nb)
            (SmtValue.Binary (native_nat_to_int w) nc))) := by
  intro hA hX hB hC
  rw [canonicalBitVecValue_of_payload w na hA,
    canonicalBitVecValue_of_payload w nx hX,
    canonicalBitVecValue_of_payload w nb hB,
    canonicalBitVecValue_of_payload w nc hC]
  simp only [eval_bvxor_canonicalBitVecValue,
    eval_bvnot_canonicalBitVecValue]
  congr 1
  calc
    BitVec.ofInt w na ^^^
          (BitVec.ofInt w nx ^^^
            (BitVec.ofInt w nb ^^^
              (~~~(BitVec.ofInt w nx) ^^^ BitVec.ofInt w nc))) =
        (BitVec.ofInt w na ^^^
          (BitVec.ofInt w nb ^^^ BitVec.ofInt w nc)) ^^^
            (BitVec.ofInt w nx ^^^ ~~~(BitVec.ofInt w nx)) := by ac_rfl
    _ = (BitVec.ofInt w na ^^^
          (BitVec.ofInt w nb ^^^ BitVec.ofInt w nc)) ^^^
            BitVec.allOnes w := by
      rw [bitvec_xor_not_self_local]
    _ = ~~~(BitVec.ofInt w na ^^^
          (BitVec.ofInt w nb ^^^ BitVec.ofInt w nc)) := by
      rw [BitVec.xor_allOnes]

/-- The preceding negated-pair identity also holds when `bvnot x` occurs
before `x`. -/
theorem bvxor_not_cancel_nested_eval_rev
    (w : Nat) (na nx nb nc : native_Int) :
    native_zeq na
        (native_mod_total na (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nb
        (native_mod_total nb (native_int_pow2 (native_nat_to_int w))) = true ->
    native_zeq nc
        (native_mod_total nc (native_int_pow2 (native_nat_to_int w))) = true ->
    __smtx_model_eval_bvxor
        (SmtValue.Binary (native_nat_to_int w) na)
        (__smtx_model_eval_bvxor
          (__smtx_model_eval_bvnot
            (SmtValue.Binary (native_nat_to_int w) nx))
          (__smtx_model_eval_bvxor
            (SmtValue.Binary (native_nat_to_int w) nb)
            (__smtx_model_eval_bvxor
              (SmtValue.Binary (native_nat_to_int w) nx)
              (SmtValue.Binary (native_nat_to_int w) nc)))) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int w) na)
          (__smtx_model_eval_bvxor
            (SmtValue.Binary (native_nat_to_int w) nb)
            (SmtValue.Binary (native_nat_to_int w) nc))) := by
  intro hA hX hB hC
  rw [canonicalBitVecValue_of_payload w na hA,
    canonicalBitVecValue_of_payload w nx hX,
    canonicalBitVecValue_of_payload w nb hB,
    canonicalBitVecValue_of_payload w nc hC]
  simp only [eval_bvxor_canonicalBitVecValue,
    eval_bvnot_canonicalBitVecValue]
  congr 1
  calc
    BitVec.ofInt w na ^^^
          (~~~(BitVec.ofInt w nx) ^^^
            (BitVec.ofInt w nb ^^^
              (BitVec.ofInt w nx ^^^ BitVec.ofInt w nc))) =
        (BitVec.ofInt w na ^^^
          (BitVec.ofInt w nb ^^^ BitVec.ofInt w nc)) ^^^
            (BitVec.ofInt w nx ^^^ ~~~(BitVec.ofInt w nx)) := by ac_rfl
    _ = (BitVec.ofInt w na ^^^
          (BitVec.ofInt w nb ^^^ BitVec.ofInt w nc)) ^^^
            BitVec.allOnes w := by
      rw [bitvec_xor_not_self_local]
    _ = ~~~(BitVec.ofInt w na ^^^
          (BitVec.ofInt w nb ^^^ BitVec.ofInt w nc)) := by
      rw [BitVec.xor_allOnes]
