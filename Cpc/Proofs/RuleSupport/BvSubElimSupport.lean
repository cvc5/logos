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

def bvSubElimLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) x) y

def bvSubElimRhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd)
      (Term.Apply (Term.UOp UserOp.bvneg) y))
      (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))

def bvSubElimTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvSubElimLhs x y))
    (bvSubElimRhs x y)

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

theorem bv_sub_elim_args_type_of_bool (x y : Term) :
    __eo_typeof (bvSubElimTerm x y) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  have hLeftNN :
      __eo_typeof (bvSubElimLhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvSubElimLhs x y))
        (__eo_typeof (bvSubElimRhs x y))
        (by exact hTy)
    exact hOperands.1
  have hBvSubNN :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    exact hLeftNN
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hBvSubNN with
    ⟨w, hXTy, hYTy⟩
  refine ⟨w, hXTy, hYTy, ?_⟩
  intro hW
  subst w
  simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite, native_teq,
    native_not, hXTy, hYTy] at hBvSubNN

theorem bv_sub_elim_nil_ne (x y : Term) :
    __eo_typeof (bvSubElimTerm x y) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck := by
  intro hTy
  have hRightNN :
      __eo_typeof (bvSubElimRhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvSubElimLhs x y))
        (__eo_typeof (bvSubElimRhs x y))
        (by exact hTy)
    exact hOperands.2
  intro hNil
  apply hRightNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd)
          (Term.Apply (Term.UOp UserOp.bvneg) y))
          (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof x)
      (__eo_typeof_bvand (__eo_typeof_bvnot (__eo_typeof y)) Term.Stuck) =
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

private theorem smt_typeof_binary_nat_to_int_zero_local (w : native_Nat) :
    __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) 0) =
      SmtType.BitVec w := by
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    simp [SmtEval.native_zleq, Smtm.native_nat_to_int]
  have hMod0 :
      native_mod_total 0 (native_int_pow2 (native_nat_to_int w)) = 0 := by
    simp [SmtEval.native_mod_total]
  have hMod :
      native_zeq 0
          (native_mod_total 0 (native_int_pow2 (native_nat_to_int w))) =
        true := by
    simp [SmtEval.native_zeq, hMod0]
  have hNN :
      __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) 0) ≠
        SmtType.None := by
    unfold __smtx_typeof
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  simpa [SmtEval.native_int_to_nat, Smtm.native_nat_to_int] using
    TranslationProofs.smtx_typeof_binary_of_non_none
      (native_nat_to_int w) 0 hNN

theorem bvAdd_nil_eq_zero_of_type
    {ty : Term} (w : Nat) :
    __eo_to_smt_type ty = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvadd) ty ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvadd) ty =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hTy hNe
  have hTyEq :
      ty =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hTy
  subst ty
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · have hBoundProp : native_nat_to_int w <= 4294967296 := by
      simpa [native_zleq] using hBound
    have hWidthNonneg : 0 <= native_nat_to_int w := by
      simp [native_nat_to_int]
    change
      __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Binary (native_nat_to_int w) 0
    simp [__eo_to_bin, __eo_mk_binary, native_ite, native_zleq,
      hBoundProp, hWidthNonneg, native_mod_total]
  · have hStuck :
        __eo_nil (Term.UOp UserOp.bvadd)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w))) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_nil, __eo_nil_bvadd, __eo_to_bin, hBoundFalse,
        native_ite, native_zleq]
    exact False.elim (hNe hStuck)

theorem smt_typeof_bvadd_nil
    (x : Term) (w : Nat) :
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x))) =
      SmtType.BitVec w := by
  intro hTy hNilNe
  have hEq := bvAdd_nil_eq_zero_of_type w hTy hNilNe
  rw [hEq]
  exact smt_typeof_binary_nat_to_int_zero_local w

theorem smt_eval_bvadd_nil
    (M : SmtModel) (x : Term) (w : Nat) :
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x))) =
      SmtValue.Binary (native_nat_to_int w) 0 := by
  intro hTy hNilNe
  have hEq := bvAdd_nil_eq_zero_of_type w hTy hNilNe
  rw [hEq]
  change __smtx_model_eval M (SmtTerm.Binary (native_nat_to_int w) 0) =
    SmtValue.Binary (native_nat_to_int w) 0
  have hMod0 :
      native_mod_total 0 (native_int_pow2 (native_nat_to_int w)) = 0 := by
    simp [native_mod_total]
  simp [__smtx_model_eval, hMod0]

private theorem bv_sub_context
    (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSubElimTerm x y) = Term.Bool ->
    ∃ w,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ∧
      __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck := by
  intro hXTrans hYTrans hResultTy
  rcases bv_sub_elim_args_type_of_bool x y hResultTy with
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
  exact ⟨native_int_to_nat n, hXSmtTy, hYSmtTy, hXTypeSmt,
    bv_sub_elim_nil_ne x y hResultTy⟩

private theorem smt_typeof_bvsub_lhs
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (bvSubElimLhs x y)) = SmtType.BitVec w := by
  intro hXTy hYTy
  change __smtx_typeof (SmtTerm.bvsub (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.BitVec w
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hYTy, native_nateq, native_ite]

private theorem smt_typeof_bvsub_rhs
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvSubElimRhs x y)) = SmtType.BitVec w := by
  intro hXTy hYTy hXTypeSmt hNilNe
  have hNilTy := smt_typeof_bvadd_nil x w hXTypeSmt hNilNe
  have hNegTy :
      __smtx_typeof (SmtTerm.bvneg (__eo_to_smt y)) = SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_1, hYTy]
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt y))
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))) =
        SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_2, hNegTy, hNilTy, native_nateq, native_ite]
  change __smtx_typeof
      (SmtTerm.bvadd (__eo_to_smt x)
        (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt y))
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x))))) =
    SmtType.BitVec w
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hInnerTy, native_nateq, native_ite]

theorem typed_bv_sub_elim_term (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSubElimTerm x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSubElimTerm x y) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_sub_context x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hNilNe⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvSubElimLhs x y) (bvSubElimRhs x y)
    (by
      rw [smt_typeof_bvsub_lhs x y w hXTy hYTy,
        smt_typeof_bvsub_rhs x y w hXTy hYTy hXTypeSmt hNilNe])
    (by
      rw [smt_typeof_bvsub_lhs x y w hXTy hYTy]
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

private theorem smtx_eval_bvneg_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvneg x) =
      __smtx_model_eval_bvneg (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvadd_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvadd x y) =
      __smtx_model_eval_bvadd (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvsub_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvsub x y) =
      __smtx_model_eval_bvsub (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem bvadd_right_zero_of_canonical (w p : native_Int) :
    native_zeq p (native_mod_total p (native_int_pow2 w)) = true ->
    __smtx_model_eval_bvadd (SmtValue.Binary w p) (SmtValue.Binary w 0) =
      SmtValue.Binary w p := by
  intro hCan
  have hPayloadMod : native_mod_total p (native_int_pow2 w) = p := by
    have hPayloadEq : p = native_mod_total p (native_int_pow2 w) := by
      simpa [native_zeq] using hCan
    exact hPayloadEq.symm
  simp [__smtx_model_eval_bvadd, native_zplus, hPayloadMod]

private theorem bvneg_eval_canonical
    (w ny : native_Int) :
    native_zleq 0 w = true ->
    ∃ p,
      __smtx_model_eval_bvneg (SmtValue.Binary w ny) = SmtValue.Binary w p ∧
      native_zeq p (native_mod_total p (native_int_pow2 w)) = true := by
  intro hWidth
  have hNegTy :
      __smtx_typeof_value (__smtx_model_eval_bvneg (SmtValue.Binary w ny)) =
        SmtType.BitVec (native_int_to_nat w) :=
    typeof_value_model_eval_bvneg_value w ny hWidth
  have hWidthEq : native_nat_to_int (native_int_to_nat w) = w :=
    native_nat_to_int_of_int_to_nat_of_nonneg w hWidth
  rcases bitvec_value_canonical hNegTy with ⟨p, hEval⟩
  have hEval' :
      __smtx_model_eval_bvneg (SmtValue.Binary w ny) = SmtValue.Binary w p := by
    simpa [hWidthEq] using hEval
  have hCanNat :
      native_zeq p
          (native_mod_total p
            (native_int_pow2 (native_nat_to_int (native_int_to_nat w)))) =
        true :=
    bitvec_payload_canonical (by simpa [hEval] using hNegTy)
  have hCan :
      native_zeq p (native_mod_total p (native_int_pow2 w)) = true :=
    by simpa [hWidthEq] using hCanNat
  exact ⟨p, hEval', hCan⟩

private theorem eval_bvsub_matches_bvadd_bvneg_with_zero
    (w : Nat) (nx ny : native_Int) :
    __smtx_model_eval_bvsub
        (SmtValue.Binary (native_nat_to_int w) nx)
        (SmtValue.Binary (native_nat_to_int w) ny) =
      __smtx_model_eval_bvadd
        (SmtValue.Binary (native_nat_to_int w) nx)
        (__smtx_model_eval_bvadd
          (__smtx_model_eval_bvneg
            (SmtValue.Binary (native_nat_to_int w) ny))
          (SmtValue.Binary (native_nat_to_int w) 0)) := by
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, native_nat_to_int]
  rcases bvneg_eval_canonical (native_nat_to_int w) ny hWidth with
    ⟨p, hNegEval, hNegCan⟩
  change __smtx_model_eval_bvadd
      (SmtValue.Binary (native_nat_to_int w) nx)
      (__smtx_model_eval_bvneg (SmtValue.Binary (native_nat_to_int w) ny)) =
    __smtx_model_eval_bvadd
      (SmtValue.Binary (native_nat_to_int w) nx)
      (__smtx_model_eval_bvadd
        (__smtx_model_eval_bvneg (SmtValue.Binary (native_nat_to_int w) ny))
        (SmtValue.Binary (native_nat_to_int w) 0))
  rw [hNegEval]
  rw [bvadd_right_zero_of_canonical (native_nat_to_int w) p hNegCan]

private theorem eval_bv_sub_elim
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSubElimTerm x y) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvSubElimLhs x y)) =
      __smtx_model_eval M (__eo_to_smt (bvSubElimRhs x y)) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_sub_context x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hNilNe⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, _hXCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hYTy with
    ⟨ny, hYEval, _hYCan⟩
  have hNilEval := smt_eval_bvadd_nil M x w hXTypeSmt hNilNe
  change __smtx_model_eval M (SmtTerm.bvsub (__eo_to_smt x) (__eo_to_smt y)) =
    __smtx_model_eval M
      (SmtTerm.bvadd (__eo_to_smt x)
        (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt y))
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))))
  rw [smtx_eval_bvsub_term_eq, smtx_eval_bvadd_term_eq,
    smtx_eval_bvadd_term_eq, smtx_eval_bvneg_term_eq]
  rw [hXEval, hYEval, hNilEval]
  exact eval_bvsub_matches_bvadd_bvneg_with_zero w nx ny

theorem facts_bv_sub_elim_term
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSubElimTerm x y) = Term.Bool ->
    eo_interprets M (bvSubElimTerm x y) true := by
  intro hXTrans hYTrans hResultTy
  have hBool :=
    typed_bv_sub_elim_term x y hXTrans hYTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvSubElimLhs x y)))
      (__smtx_model_eval M (__eo_to_smt (bvSubElimRhs x y)))
    rw [eval_bv_sub_elim M hM x y hXTrans hYTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvSubElimProgram (x y : Term) : Term :=
  __eo_prog_bv_sub_eliminate x y

private def bvSubElimProgramSkeleton (x y : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) (bvSubElimLhs x y))
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvadd) x)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvadd)
        (Term.Apply (Term.UOp UserOp.bvneg) y))
        (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x))))

private theorem bvSubElimProgram_eq_skeleton_of_ne_stuck
    (x y : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    bvSubElimProgram x y = bvSubElimProgramSkeleton x y := by
  intro hXNe hYNe
  cases x <;> cases y <;>
    simp [bvSubElimProgram, bvSubElimProgramSkeleton, __eo_prog_bv_sub_eliminate,
      bvSubElimLhs] at hXNe hYNe ⊢

theorem bvSubElimProgram_eq_term_of_type_bool (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSubElimProgram x y) = Term.Bool ->
    bvSubElimProgram x y = bvSubElimTerm x y := by
  intro hXTrans hYTrans hTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hSkeleton :=
    bvSubElimProgram_eq_skeleton_of_ne_stuck x y hXNe hYNe
  by_cases hNil :
      __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) = Term.Stuck
  · have hProgStuck : bvSubElimProgram x y = Term.Stuck := by
      rw [hSkeleton]
      simp [bvSubElimProgramSkeleton, __eo_mk_apply, hNil]
    rw [hProgStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · rw [hSkeleton]
    simp [bvSubElimProgramSkeleton, bvSubElimTerm, bvSubElimLhs, bvSubElimRhs,
      __eo_mk_apply, hNil]

theorem typed_bv_sub_elim_program (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSubElimProgram x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSubElimProgram x y) := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvSubElimProgram_eq_term_of_type_bool x y hXTrans hYTrans hResultTy
  have hTermTy : __eo_typeof (bvSubElimTerm x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_sub_elim_term x y hXTrans hYTrans hTermTy

theorem facts_bv_sub_elim_program
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSubElimProgram x y) = Term.Bool ->
    eo_interprets M (bvSubElimProgram x y) true := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvSubElimProgram_eq_term_of_type_bool x y hXTrans hYTrans hResultTy
  have hTermTy : __eo_typeof (bvSubElimTerm x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_sub_elim_term M hM x y hXTrans hYTrans hTermTy

def bvCommutativeAddLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y)
      (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))

def bvCommutativeAddRhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x)
      (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y)))

def bvCommutativeAddTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvCommutativeAddLhs x y))
    (bvCommutativeAddRhs x y)

theorem bv_commutative_add_args_type_of_bool (x y : Term) :
    __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      w ≠ Term.Stuck := by
  intro hTy
  have hLeftNN :
      __eo_typeof (bvCommutativeAddLhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvCommutativeAddLhs x y))
        (__eo_typeof (bvCommutativeAddRhs x y))
        (by
          exact hTy)
    exact hOperands.1
  have hOuterNN :
      __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y)
              (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))) ≠
        Term.Stuck := by
    exact hLeftNN
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hOuterNN with
    ⟨w, hXTy, hInnerTy⟩
  have hInnerEq :
      __eo_typeof_bvand (__eo_typeof y)
          (__eo_typeof (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x))) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    exact hInnerTy
  have hInnerNe : __eo_typeof_bvand (__eo_typeof y)
        (__eo_typeof (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x))) ≠
      Term.Stuck := by
    rw [hInnerEq]
    intro hBad
    cases hBad
  rcases eo_typeof_bvand_arg_types_of_ne_stuck_local hInnerNe with
    ⟨v, hYTy, hNilTy⟩
  have hVNe : v ≠ Term.Stuck := by
    intro hV
    subst v
    rw [hYTy, hNilTy] at hInnerNe
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not] at hInnerNe
  have hReduce :
      __eo_typeof_bvand
          (Term.Apply (Term.UOp UserOp.BitVec) v)
          (Term.Apply (Term.UOp UserOp.BitVec) v) =
        Term.Apply (Term.UOp UserOp.BitVec) v := by
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hVNe]
  have hVW : v = w := by
    rw [hYTy, hNilTy] at hInnerEq
    rw [hReduce] at hInnerEq
    cases hInnerEq
    rfl
  subst w
  exact ⟨v, hXTy, hYTy, hVNe⟩

theorem bv_commutative_add_nil_x_ne (x y : Term) :
    __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck := by
  intro hTy hNil
  have hLeftNN :
      __eo_typeof (bvCommutativeAddLhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvCommutativeAddLhs x y))
        (__eo_typeof (bvCommutativeAddRhs x y))
        (by
          exact hTy)
    exact hOperands.1
  apply hLeftNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y)
          (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof x)
      (__eo_typeof_bvand (__eo_typeof y) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

theorem bv_commutative_add_nil_y_ne (x y : Term) :
    __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y) ≠ Term.Stuck := by
  intro hTy hNil
  have hRightNN :
      __eo_typeof (bvCommutativeAddRhs x y) ≠ Term.Stuck := by
    have hOperands :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof (bvCommutativeAddLhs x y))
        (__eo_typeof (bvCommutativeAddRhs x y))
        (by
          exact hTy)
    exact hOperands.2
  apply hRightNN
  change __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x)
          (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y)))) =
    Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof y)
      (__eo_typeof_bvand (__eo_typeof x) Term.Stuck) =
    Term.Stuck
  simp [__eo_typeof_bvand]

private theorem bv_commutative_add_context
    (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool ->
    ∃ w,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ∧
      __eo_to_smt_type (__eo_typeof y) = SmtType.BitVec w ∧
      __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck ∧
      __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y) ≠ Term.Stuck := by
  intro hXTrans hYTrans hResultTy
  rcases bv_commutative_add_args_type_of_bool x y hResultTy with
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
    bv_commutative_add_nil_x_ne x y hResultTy,
    bv_commutative_add_nil_y_ne x y hResultTy⟩

private theorem smt_typeof_bv_comm_add_lhs
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvCommutativeAddLhs x y)) =
      SmtType.BitVec w := by
  intro hXTy hYTy hXTypeSmt hNilXNe
  have hNilTy := smt_typeof_bvadd_nil x w hXTypeSmt hNilXNe
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvadd (__eo_to_smt y)
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))) =
        SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_2, hYTy, hNilTy, native_nateq, native_ite]
  change __smtx_typeof
      (SmtTerm.bvadd (__eo_to_smt x)
        (SmtTerm.bvadd (__eo_to_smt y)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x))))) =
    SmtType.BitVec w
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hInnerTy, native_nateq, native_ite]

private theorem smt_typeof_bv_comm_add_rhs
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __eo_to_smt_type (__eo_typeof y) = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y) ≠ Term.Stuck ->
    __smtx_typeof (__eo_to_smt (bvCommutativeAddRhs x y)) =
      SmtType.BitVec w := by
  intro hXTy hYTy hYTypeSmt hNilYNe
  have hNilTy := smt_typeof_bvadd_nil y w hYTypeSmt hNilYNe
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.bvadd (__eo_to_smt x)
            (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y)))) =
        SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_2, hXTy, hNilTy, native_nateq, native_ite]
  change __smtx_typeof
      (SmtTerm.bvadd (__eo_to_smt y)
        (SmtTerm.bvadd (__eo_to_smt x)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y))))) =
    SmtType.BitVec w
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hYTy, hInnerTy, native_nateq, native_ite]

theorem typed_bv_commutative_add_term (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvCommutativeAddTerm x y) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_commutative_add_context x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hYTypeSmt, hNilXNe, hNilYNe⟩
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvCommutativeAddLhs x y) (bvCommutativeAddRhs x y)
    (by
      rw [smt_typeof_bv_comm_add_lhs x y w hXTy hYTy hXTypeSmt hNilXNe,
        smt_typeof_bv_comm_add_rhs x y w hXTy hYTy hYTypeSmt hNilYNe])
    (by
      rw [smt_typeof_bv_comm_add_lhs x y w hXTy hYTy hXTypeSmt hNilXNe]
      simp)

private theorem bvadd_eval_comm (w : Nat) (nx ny : native_Int) :
    __smtx_model_eval_bvadd
        (SmtValue.Binary (native_nat_to_int w) nx)
        (SmtValue.Binary (native_nat_to_int w) ny) =
      __smtx_model_eval_bvadd
        (SmtValue.Binary (native_nat_to_int w) ny)
        (SmtValue.Binary (native_nat_to_int w) nx) := by
  simp [__smtx_model_eval_bvadd, native_zplus, Int.add_comm]

private theorem eval_bv_commutative_add
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvCommutativeAddLhs x y)) =
      __smtx_model_eval M (__eo_to_smt (bvCommutativeAddRhs x y)) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_commutative_add_context x y hXTrans hYTrans hResultTy with
    ⟨w, hXTy, hYTy, hXTypeSmt, hYTypeSmt, hNilXNe, hNilYNe⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hXTy with
    ⟨nx, hXEval, hXCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hYTy with
    ⟨ny, hYEval, hYCan⟩
  have hNilXEval := smt_eval_bvadd_nil M x w hXTypeSmt hNilXNe
  have hNilYEval := smt_eval_bvadd_nil M y w hYTypeSmt hNilYNe
  change __smtx_model_eval M
      (SmtTerm.bvadd (__eo_to_smt x)
        (SmtTerm.bvadd (__eo_to_smt y)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x))))) =
    __smtx_model_eval M
      (SmtTerm.bvadd (__eo_to_smt y)
        (SmtTerm.bvadd (__eo_to_smt x)
          (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y)))))
  repeat rw [smtx_eval_bvadd_term_eq]
  rw [hXEval, hYEval, hNilXEval, hNilYEval]
  rw [bvadd_right_zero_of_canonical (native_nat_to_int w) ny hYCan,
    bvadd_right_zero_of_canonical (native_nat_to_int w) nx hXCan]
  exact bvadd_eval_comm w nx ny

theorem facts_bv_commutative_add_term
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool ->
    eo_interprets M (bvCommutativeAddTerm x y) true := by
  intro hXTrans hYTrans hResultTy
  have hBool :=
    typed_bv_commutative_add_term x y hXTrans hYTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvCommutativeAddLhs x y)))
      (__smtx_model_eval M (__eo_to_smt (bvCommutativeAddRhs x y)))
    rw [eval_bv_commutative_add M hM x y hXTrans hYTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvCommutativeAddProgram (x y : Term) : Term :=
  __eo_prog_bv_commutative_add x y

private def bvCommutativeAddProgramSkeleton (x y : Term) : Term :=
  let v0 := Term.Apply (Term.UOp UserOp.bvadd) x
  let v1 := Term.Apply (Term.UOp UserOp.bvadd) y
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply v0
        (__eo_mk_apply v1
          (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)))))
    (__eo_mk_apply v1
      (__eo_mk_apply v0
        (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y))))

private theorem bvCommutativeAddProgram_eq_skeleton_of_ne_stuck
    (x y : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    bvCommutativeAddProgram x y = bvCommutativeAddProgramSkeleton x y := by
  intro hXNe hYNe
  cases x <;> cases y <;>
    simp [bvCommutativeAddProgram, bvCommutativeAddProgramSkeleton,
      __eo_prog_bv_commutative_add] at hXNe hYNe ⊢

theorem bvCommutativeAddProgram_eq_term_of_type_bool
    (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeAddProgram x y) = Term.Bool ->
    bvCommutativeAddProgram x y = bvCommutativeAddTerm x y := by
  intro hXTrans hYTrans hTy
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hSkeleton := bvCommutativeAddProgram_eq_skeleton_of_ne_stuck x y hXNe hYNe
  by_cases hNilX : __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) = Term.Stuck
  · have hProgStuck : bvCommutativeAddProgram x y = Term.Stuck := by
      rw [hSkeleton]
      simp [bvCommutativeAddProgramSkeleton, __eo_mk_apply, hNilX]
    rw [hProgStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · by_cases hNilY : __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof y) = Term.Stuck
    · have hProgStuck : bvCommutativeAddProgram x y = Term.Stuck := by
        rw [hSkeleton]
        simp [bvCommutativeAddProgramSkeleton, __eo_mk_apply, hNilX, hNilY]
      rw [hProgStuck] at hTy
      have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
        native_decide
      exact False.elim (hBad hTy)
    · rw [hSkeleton]
      simp [bvCommutativeAddProgramSkeleton, bvCommutativeAddTerm,
        bvCommutativeAddLhs, bvCommutativeAddRhs, __eo_mk_apply, hNilX, hNilY]

theorem typed_bv_commutative_add_program (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeAddProgram x y) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvCommutativeAddProgram x y) := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvCommutativeAddProgram_eq_term_of_type_bool x y hXTrans hYTrans hResultTy
  have hTermTy : __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_commutative_add_term x y hXTrans hYTrans hTermTy

theorem facts_bv_commutative_add_program
    (M : SmtModel) (hM : model_wf M) (x y : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvCommutativeAddProgram x y) = Term.Bool ->
    eo_interprets M (bvCommutativeAddProgram x y) true := by
  intro hXTrans hYTrans hResultTy
  have hEq :=
    bvCommutativeAddProgram_eq_term_of_type_bool x y hXTrans hYTrans hResultTy
  have hTermTy : __eo_typeof (bvCommutativeAddTerm x y) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_commutative_add_term M hM x y hXTrans hYTrans hTermTy
