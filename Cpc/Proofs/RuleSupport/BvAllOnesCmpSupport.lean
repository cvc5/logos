module

public import Cpc.Proofs.RuleSupport.BvSaddoElimSupport
import all Cpc.Proofs.RuleSupport.BvSaddoElimSupport

public section

/-! Shared support for comparison rewrites against an all-ones bit-vector. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def bvAllOnesWidthPrem (x w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)

def bvAllOnesValuePrem (n w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) n)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp.int_pow2) w)) (Term.Numeral 1))

def bvUleMaxValuePrem (x n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) n)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp.int_pow2)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x))) (Term.Numeral 1))

def bvAllOnesConst (n w : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n

def bvUleMaxTerm (x n w : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) x)
        (bvAllOnesConst n w)))
    (Term.Boolean true)

def bvUltOnesList (x n w : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
        (bvAllOnesConst n w))
      (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof x)))

def bvUltOnesDistinct (x n w : Term) : Term :=
  Term.Apply (Term.UOp UserOp.distinct) (bvUltOnesList x n w)

def bvUltOnesTerm (x n w : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x)
        (bvAllOnesConst n w)))
    (bvUltOnesDistinct x n w)

theorem bv_all_ones_const_context
    (n w width : Term) :
    n ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    __eo_typeof (bvAllOnesConst n w) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ width = Term.Numeral W ∧
      native_zleq 0 W = true ∧ __eo_typeof n = Term.UOp UserOp.Int := by
  intro hNNe hWNe hTy
  change __eo_typeof_int_to_bv (__eo_typeof w) w (__eo_typeof n) =
    Term.Apply (Term.UOp UserOp.BitVec) width at hTy
  have hNTy : __eo_typeof n = Term.UOp UserOp.Int := by
    cases hn : __eo_typeof n <;>
      simp [__eo_typeof_int_to_bv, hn, hWNe] at hTy ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_int_to_bv, hn, hWNe] at hTy ⊢
  have hWTy : __eo_typeof w = Term.UOp UserOp.Int := by
    cases hw : __eo_typeof w <;>
      simp [__eo_typeof_int_to_bv, hNTy, hw, hWNe] at hTy ⊢
    case UOp op =>
      cases op <;>
        simp [__eo_typeof_int_to_bv, hNTy, hw, hWNe] at hTy ⊢
  have hReqTy :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
    simpa [__eo_typeof_int_to_bv, hNTy, hWTy, hWNe] using hTy
  have hReqNe :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck := by
    rw [hReqTy]
    intro h
    cases h
  have hGuard :
      __eo_gt w (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReqNe
  have hReqEq :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    simp [__eo_requires, hGuard, native_ite, native_teq, native_not]
  rw [hReqEq] at hReqTy
  have hWidth : width = w := by
    injection hReqTy with _ h
    exact h.symm
  cases w <;> simp [__eo_gt] at hGuard
  case Numeral W =>
    have hW0 : native_zleq 0 W = true := by
      have hsimpa := hGuard
      try simp [SmtEval.native_zlt, SmtEval.native_zleq] at hsimpa ⊢
      exact hsimpa
    exact ⟨W, rfl, hWidth, hW0, hNTy⟩

theorem bv_ule_max_context
    (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvUleMaxTerm x n w) = Term.Bool ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ native_zleq 0 W = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __eo_typeof n = Term.UOp UserOp.Int ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  intro hXTrans hNTrans hWTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult (__eo_typeof x)
        (__eo_typeof (bvAllOnesConst n w))) Term.Bool = Term.Bool at hResultTy
  have hOps := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy
  rcases typeof_bvult_args_of_ne_stuck hOps.1 with
    ⟨width, hXTy, hConstTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width x width
      hXTrans hXTy with ⟨W, hWidth, hW0, hXSmtTy⟩
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hWNe := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases bv_all_ones_const_context n w width hNNe hWNe hConstTy with
    ⟨W', hW, hWidth', hW'0, hNTy⟩
  have hWEq : W' = W := by
    rw [hWidth] at hWidth'
    injection hWidth' with h
    exact h.symm
  subst W'
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hNTy
  subst width
  exact ⟨W, hW, hW0, hXTy, hNTy, hXSmtTy, hNSmtTy⟩

theorem bv_ult_ones_context
    (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvUltOnesTerm x n w) = Term.Bool ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ native_zleq 0 W = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __eo_typeof n = Term.UOp UserOp.Int ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  intro hXTrans hNTrans hWTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult (__eo_typeof x)
        (__eo_typeof (bvAllOnesConst n w)))
      (__eo_typeof (bvUltOnesDistinct x n w)) = Term.Bool at hResultTy
  have hOps := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy
  rcases typeof_bvult_args_of_ne_stuck hOps.1 with
    ⟨width, hXTy, hConstTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width x width
      hXTrans hXTy with ⟨W, hWidth, hW0, hXSmtTy⟩
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hWNe := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases bv_all_ones_const_context n w width hNNe hWNe hConstTy with
    ⟨W', hW, hWidth', _hW'0, hNTy⟩
  have hWEq : W' = W := by
    rw [hWidth] at hWidth'
    injection hWidth' with h
    exact h.symm
  subst W'
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hNTy
  subst width
  exact ⟨W, hW, hW0, hXTy, hNTy, hXSmtTy, hNSmtTy⟩

private theorem smtx_eval_neg_term_eq_local
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_int_pow2_term_eq_local
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.int_pow2 x) =
      __smtx_model_eval_int_pow2 (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq_local
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq_local
    (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem native_nat_to_int_int_to_nat_of_nonneg_local
    (n : native_Int) :
    native_zleq 0 n = true ->
    native_nat_to_int (native_int_to_nat n) = n := by
  intro hNonneg
  have hn : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
    Int.toNat_of_nonneg hn
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem eval_bvsize_num_local
    (M : SmtModel) (x : Term) (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat n) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral n := by
  intro hNonneg hXSmt
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0 (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral n
  have hWidth := native_nat_to_int_int_to_nat_of_nonneg_local n hNonneg
  have hNN :
      native_zleq 0 (native_nat_to_int (native_int_to_nat n)) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int]
  have hSize :
      __eo_to_smt_bv_size (SmtType.BitVec (native_int_to_nat n)) =
        native_nat_to_int (native_int_to_nat n) := rfl
  rw [hXSmt, hSize]
  simp [native_ite, hNN, hNonneg, hWidth, __smtx_model_eval,
    __smtx_model_eval__at_purify]

private theorem eval_bv_all_ones_value_local
    (M : SmtModel) (x : Term) (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat n) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.int_pow2)
              (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
            (Term.Numeral 1))) =
      SmtValue.Numeral (native_int_pow2 n - 1) := by
  intro hNonneg hXSmt
  change __smtx_model_eval M
      (SmtTerm.neg
        (SmtTerm.int_pow2
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
        (SmtTerm.Numeral 1)) =
      SmtValue.Numeral (native_int_pow2 n - 1)
  rw [smtx_eval_neg_term_eq_local, smtx_eval_int_pow2_term_eq_local,
    eval_bvsize_num_local M x n hNonneg hXSmt,
    smtx_eval_numeral_term_eq_local]
  simp [__smtx_model_eval_int_pow2, __smtx_model_eval__, native_zplus,
    native_zneg, Int.sub_eq_add_neg]

private theorem eval_bv_all_ones_literal_local
    (M : SmtModel) (w : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.int_pow2) (Term.Numeral w)))
            (Term.Numeral 1))) =
      SmtValue.Numeral (native_int_pow2 w - 1) := by
  change __smtx_model_eval M
      (SmtTerm.neg (SmtTerm.int_pow2 (SmtTerm.Numeral w))
        (SmtTerm.Numeral 1)) =
    SmtValue.Numeral (native_int_pow2 w - 1)
  rw [smtx_eval_neg_term_eq_local, smtx_eval_int_pow2_term_eq_local,
    smtx_eval_numeral_term_eq_local, smtx_eval_numeral_term_eq_local]
  simp [__smtx_model_eval_int_pow2, __smtx_model_eval__, native_zplus,
    native_zneg, Int.sub_eq_add_neg]

private theorem numeral_rel_eq_local {a b : native_Int} :
    RuleProofs.smt_value_rel (SmtValue.Numeral a) (SmtValue.Numeral b) ->
    a = b := by
  intro hRel
  simpa [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] using hRel

private theorem bitvec_eval_payload_with_width_local
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (n : native_Int) :
    RuleProofs.eo_has_smt_translation t ->
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt t) =
      SmtType.BitVec (native_int_to_nat n) ->
    ∃ p : native_Int,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary n p ∧
      native_zeq p (native_mod_total p (native_int_pow2 n)) = true := by
  intro hTrans hNonneg hTy
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hTrans
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hNN
  rcases bitvec_value_canonical hEvalTy with ⟨p, hEval⟩
  have hWidth := native_nat_to_int_int_to_nat_of_nonneg_local n hNonneg
  have hCanon :
      native_zeq p (native_mod_total p (native_int_pow2 n)) = true := by
    have hRaw := bitvec_payload_canonical (by simpa [hEval] using hEvalTy)
    simpa [hWidth] using hRaw
  exact ⟨p, by simpa [hWidth] using hEval, hCanon⟩

private theorem native_pow2_minus_one_mod_local
    (w : native_Int) :
    native_zleq 0 w = true ->
    native_mod_total (native_int_pow2 w - 1) (native_int_pow2 w) =
      native_int_pow2 w - 1 := by
  intro hW
  have hw : (0 : native_Int) <= w := by
    simpa [SmtEval.native_zleq] using hW
  have hPowPos : 0 < native_int_pow2 w := by
    have hNot : ¬ w < 0 := Int.not_lt_of_ge hw
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, hNot]
    exact Int.pow_pos (by decide)
  have hLo : 0 <= native_int_pow2 w - 1 := by
    exact Int.sub_nonneg.mpr (Int.add_one_le_iff.mpr hPowPos)
  have hHi : native_int_pow2 w - 1 < native_int_pow2 w := by
    exact Int.sub_lt_self _ (by decide : (0 : Int) < 1)
  simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hLo hHi

theorem smt_typeof_bv_const_of_int_type
    (n : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    native_zleq 0 W = true ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n)) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hNTy hW0
  change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
  rw [typeof_int_to_bv_eq, hNTy]
  simp [__smtx_typeof_int_to_bv, native_ite, hW0]

private theorem eval_int_term_local
    (M : SmtModel) (hM : model_wf M) (n : Term) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    ∃ k : native_Int,
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral k := by
  intro hNTy
  have hEvalTy :=
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (by simp [term_has_non_none_type, hNTy])
  exact int_value_canonical (by simpa [hNTy] using hEvalTy)

private theorem eval_bv_const_of_int_eval_local
    (M : SmtModel) (n : Term) (k W : native_Int) :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral k ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n)) =
      SmtValue.Binary W (native_mod_total k (native_int_pow2 W)) := by
  intro hEval
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
  rw [smtx_eval_int_to_bv_term_eq, smtx_eval_numeral_term_eq_local, hEval]
  rfl

/-- An `@bv` term constrained by the standard all-ones premise evaluates to
    the canonical maximum value for its width. -/
theorem eval_bv_all_ones_const_of_prem
    (M : SmtModel) (hM : model_wf M)
    (n w : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    eo_interprets M (bvAllOnesValuePrem n w) true ->
    __smtx_model_eval M (__eo_to_smt (bvAllOnesConst n w)) =
      SmtValue.Binary W (native_int_pow2 W - 1) := by
  intro hNTy hW hW0 hPrem
  subst w
  rcases eval_int_term_local M hM n hNTy with ⟨k, hEvalN⟩
  have hPremRel := RuleProofs.eo_interprets_eq_rel M
    n
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp.int_pow2) (Term.Numeral W)))
      (Term.Numeral 1)) hPrem
  have hK : k = native_int_pow2 W - 1 := by
    apply numeral_rel_eq_local
    simpa [hEvalN,
      eval_bv_all_ones_literal_local M W] using hPremRel
  have hEval := eval_bv_const_of_int_eval_local M n k W hEvalN
  rw [hK, native_pow2_minus_one_mod_local W hW0] at hEval
  simpa [bvAllOnesConst] using hEval

private theorem eo_to_smt_distinct_eq_of_elem_type_ne_none_local
    (xs : Term) :
    __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) =
      __eo_to_smt_distinct xs := by
  intro hElem
  change native_ite
      (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) = __eo_to_smt_distinct xs
  have hGuard :
      native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None =
        false := by
    cases hTy : __eo_to_smt_typed_list_elem_type xs <;>
      simp [hTy, native_Teq] at hElem ⊢
    all_goals rfl
  rw [hGuard]
  simp [native_ite]

theorem typed_bv_ule_max_term
    (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvUleMaxTerm x n w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvUleMaxTerm x n w) := by
  intro hXTrans hNTrans hWTrans hResultTy
  rcases bv_ule_max_context x n w hXTrans hNTrans hWTrans
      hResultTy with
    ⟨W, hW, hW0, _hXTy, _hNTy, hXSmtTy, hNSmtTy⟩
  subst w
  have hConstTy := smt_typeof_bv_const_of_int_type n W hNSmtTy hW0
  have hCmpBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvule) x)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n)) := by
    unfold RuleProofs.eo_has_bool_type
    change __smtx_typeof
        (SmtTerm.bvule (__eo_to_smt x)
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) = SmtType.Bool
    rw [__smtx_typeof.eq_57]
    simp [__smtx_typeof_bv_op_2_ret, hXSmtTy, hConstTy,
      native_nateq, native_ite]
  unfold bvUleMaxTerm
  simp only [bvAllOnesConst]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hCmpBool, RuleProofs.eo_has_bool_type_true])
    (by rw [hCmpBool]; decide)

theorem typed_bv_ult_ones_term
    (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvUltOnesTerm x n w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvUltOnesTerm x n w) := by
  intro hXTrans hNTrans hWTrans hResultTy
  rcases bv_ult_ones_context x n w
      hXTrans hNTrans hWTrans hResultTy with
    ⟨W, hW, hW0, hXTy, _hNTy, hXSmtTy, hNSmtTy⟩
  subst w
  have hXWf :
      __smtx_type_wf (__smtx_typeof (__eo_to_smt x)) = true := by
    rw [hXSmtTy]
    simp [__smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and]
  have hConstTy := smt_typeof_bv_const_of_int_type n W hNSmtTy hW0
  have hConstTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConstTy]
    intro h
    cases h
  have hCmpBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n)) := by
    unfold RuleProofs.eo_has_bool_type
    change __smtx_typeof
        (SmtTerm.bvult (__eo_to_smt x)
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) = SmtType.Bool
    rw [__smtx_typeof.eq_56]
    simp [__smtx_typeof_bv_op_2_ret, hXSmtTy, hConstTy,
      native_nateq, native_ite]
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) x)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x _
      (hXSmtTy.trans hConstTy.symm) hXTrans
  have hEqSmtTy :
      __smtx_typeof
          (SmtTerm.eq (__eo_to_smt x)
            (__eo_to_smt
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) =
        SmtType.Bool := by
    have hsimpa := hEqBool
    try simp [RuleProofs.eo_has_bool_type] at hsimpa ⊢
    exact hsimpa
  have hEqOpTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) =
        SmtType.Bool := by
    simpa [typeof_eq_eq] using hEqSmtTy
  have hTypeMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (__eo_typeof x) (__eo_to_smt x) rfl hXTrans rfl
  have hEoTypeSmt :
      __eo_to_smt_type (__eo_typeof x) =
        SmtType.BitVec (native_int_to_nat W) := by
    rw [← hTypeMatch]
    exact hXSmtTy
  have hTypeWf :
      __smtx_type_wf (__eo_to_smt_type (__eo_typeof x)) = true := by
    rw [← hTypeMatch]
    exact hXWf
  have hBvWf :
      __smtx_type_wf (SmtType.BitVec (native_int_to_nat W)) = true := by
    rw [← hEoTypeSmt]
    exact hTypeWf
  have hTypeNe : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
    rw [← hTypeMatch]
    exact hXTrans
  have hElemNe :
      __eo_to_smt_typed_list_elem_type
          (bvUltOnesList x n (Term.Numeral W)) ≠
        SmtType.None := by
    simp [bvUltOnesList, bvAllOnesConst,
      __eo_to_smt_typed_list_elem_type, hXSmtTy, hConstTy,
      hEoTypeSmt, hTypeWf, hBvWf, hTypeNe, native_ite, native_Teq]
  have hDistinctSmt :
      __eo_to_smt
          (bvUltOnesDistinct x n (Term.Numeral W)) =
        __eo_to_smt_distinct
          (bvUltOnesList x n (Term.Numeral W)) := by
    exact eo_to_smt_distinct_eq_of_elem_type_ne_none_local _ hElemNe
  have hDistinctBool :
      RuleProofs.eo_has_bool_type
        (bvUltOnesDistinct x n (Term.Numeral W)) := by
    unfold RuleProofs.eo_has_bool_type
    rw [hDistinctSmt]
    change __smtx_typeof
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.not
              (SmtTerm.eq (__eo_to_smt x)
                (__eo_to_smt
                  (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))))
            (SmtTerm.Boolean true))
          (SmtTerm.and (SmtTerm.Boolean true) (SmtTerm.Boolean true))) =
      SmtType.Bool
    simp [typeof_and_eq, typeof_not_eq, __smtx_typeof, hEqOpTy,
      native_ite, native_Teq]
  unfold bvUltOnesTerm
  simp only [bvAllOnesConst]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hCmpBool, hDistinctBool])
    (by rw [hCmpBool]; decide)

theorem facts_bv_ule_max_term
    (M : SmtModel) (hM : model_wf M)
    (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation w ->
    eo_interprets M (bvUleMaxValuePrem x n) true ->
    __eo_typeof (bvUleMaxTerm x n w) = Term.Bool ->
    eo_interprets M (bvUleMaxTerm x n w) true := by
  intro hXTrans hNTrans hWTrans hPrem hResultTy
  rcases bv_ule_max_context x n w hXTrans hNTrans hWTrans
      hResultTy with
    ⟨W, hW, hW0, _hXTy, _hNTy, hXSmtTy, hNSmtTy⟩
  subst w
  rcases eval_int_term_local M hM n hNSmtTy with ⟨k, hEvalN⟩
  have hPremRel := RuleProofs.eo_interprets_eq_rel M
    n
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp.int_pow2)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x))) (Term.Numeral 1))
    hPrem
  have hK : k = native_int_pow2 W - 1 := by
    apply numeral_rel_eq_local
    simpa [hEvalN,
      eval_bv_all_ones_value_local M x W hW0 hXSmtTy] using hPremRel
  rcases bitvec_eval_payload_with_width_local M hM x W hXTrans hW0 hXSmtTy with
    ⟨px, hEvalX, hPxCanon⟩
  have hRange := bitvec_payload_range_of_canonical hW0 hPxCanon
  have hPxLe : px <= native_int_pow2 W - 1 :=
    Int.le_sub_one_of_lt hRange.2
  have hMaxMod := native_pow2_minus_one_mod_local W hW0
  have hConstEval := eval_bv_const_of_int_eval_local M n k W hEvalN
  have hCmpEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvule) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M
        (SmtTerm.bvule (__eo_to_smt x)
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) =
      SmtValue.Boolean true
    rw [__smtx_model_eval.eq_57, hEvalX, hConstEval, hK, hMaxMod]
    by_cases hEq : px = native_int_pow2 W - 1
    · subst px
      simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
        __smtx_model_eval_bvugt, __smtx_model_eval_eq,
        __smtx_model_eval_or, native_veq, native_or]
    · have hLt : px < native_int_pow2 W - 1 := by
        rcases Int.lt_or_eq_of_le hPxLe with hLt | hEq'
        · exact hLt
        · exact False.elim (hEq hEq')
      simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
        __smtx_model_eval_bvugt, __smtx_model_eval_eq,
        __smtx_model_eval_or, native_zlt, SmtEval.native_zlt,
        native_veq, native_or, hEq, hLt]
  have hBool := typed_bv_ule_max_term x n (Term.Numeral W)
    hXTrans hNTrans hWTrans hResultTy
  unfold bvUleMaxTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvUleMaxTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvule) x)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))))
      (__smtx_model_eval M (SmtTerm.Boolean true))
    rw [hCmpEval, smtx_eval_boolean_term_eq_local]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_bv_ult_ones_term
    (M : SmtModel) (hM : model_wf M)
    (x n w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation w ->
    eo_interprets M (bvAllOnesValuePrem n w) true ->
    __eo_typeof (bvUltOnesTerm x n w) = Term.Bool ->
    eo_interprets M (bvUltOnesTerm x n w) true := by
  intro hXTrans hNTrans hWTrans hPrem hResultTy
  rcases bv_ult_ones_context x n w
      hXTrans hNTrans hWTrans hResultTy with
    ⟨W, hW, hW0, _hXTy, _hNTy, hXSmtTy, hNSmtTy⟩
  subst w
  have hXWf :
      __smtx_type_wf (__smtx_typeof (__eo_to_smt x)) = true := by
    rw [hXSmtTy]
    simp [__smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and]
  have hConstTy := smt_typeof_bv_const_of_int_type n W hNSmtTy hW0
  have hConstEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n)) =
        SmtValue.Binary W (native_int_pow2 W - 1) := by
    simpa [bvAllOnesConst] using
      (eval_bv_all_ones_const_of_prem M hM n (Term.Numeral W) W
        hNSmtTy rfl hW0 hPrem)
  rcases bitvec_eval_payload_with_width_local M hM x W hXTrans hW0 hXSmtTy with
    ⟨px, hEvalX, hPxCanon⟩
  have hRange := bitvec_payload_range_of_canonical hW0 hPxCanon
  have hPxLe : px <= native_int_pow2 W - 1 :=
    Int.le_sub_one_of_lt hRange.2
  have hTypeMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (__eo_typeof x) (__eo_to_smt x) rfl hXTrans rfl
  have hEoTypeSmt :
      __eo_to_smt_type (__eo_typeof x) =
        SmtType.BitVec (native_int_to_nat W) := by
    rw [← hTypeMatch]
    exact hXSmtTy
  have hTypeWf :
      __smtx_type_wf (__eo_to_smt_type (__eo_typeof x)) = true := by
    rw [← hTypeMatch]
    exact hXWf
  have hBvWf :
      __smtx_type_wf (SmtType.BitVec (native_int_to_nat W)) = true := by
    rw [← hEoTypeSmt]
    exact hTypeWf
  have hTypeNe : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
    rw [← hTypeMatch]
    exact hXTrans
  have hElemNe :
      __eo_to_smt_typed_list_elem_type
          (bvUltOnesList x n (Term.Numeral W)) ≠
        SmtType.None := by
    simp [bvUltOnesList, bvAllOnesConst,
      __eo_to_smt_typed_list_elem_type, hXSmtTy, hConstTy,
      hEoTypeSmt, hTypeWf, hBvWf, hTypeNe, native_ite, native_Teq]
  have hDistinctSmt :
      __eo_to_smt
          (bvUltOnesDistinct x n (Term.Numeral W)) =
        __eo_to_smt_distinct
          (bvUltOnesList x n (Term.Numeral W)) :=
    eo_to_smt_distinct_eq_of_elem_type_ne_none_local _ hElemNe
  have hCmpEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) =
        __smtx_model_eval_bvult
          (SmtValue.Binary W px)
          (SmtValue.Binary W (native_int_pow2 W - 1)) := by
    change __smtx_model_eval M
        (SmtTerm.bvult (__eo_to_smt x)
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) = _
    rw [__smtx_model_eval.eq_56, hEvalX, hConstEval]
  have hDistinctEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvUltOnesDistinct x n (Term.Numeral W))) =
        __smtx_model_eval_not
          (__smtx_model_eval_eq
            (SmtValue.Binary W px)
            (SmtValue.Binary W (native_int_pow2 W - 1))) := by
    rw [hDistinctSmt]
    change __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.not
              (SmtTerm.eq (__eo_to_smt x)
                (__eo_to_smt
                  (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))))
            (SmtTerm.Boolean true))
          (SmtTerm.and (SmtTerm.Boolean true) (SmtTerm.Boolean true))) = _
    rw [smtx_eval_and_term_eq, smtx_eval_and_term_eq,
      smtx_eval_not_term_eq, smtx_eval_eq_term_eq,
      smtx_eval_and_term_eq, hEvalX, hConstEval]
    simp [__smtx_model_eval, __smtx_model_eval_eq,
      __smtx_model_eval_not, __smtx_model_eval_and,
      native_and]
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvUltOnesDistinct x n (Term.Numeral W))) := by
    rw [hCmpEval, hDistinctEval]
    by_cases hEq : px = native_int_pow2 W - 1
    · subst px
      have hNotLt :
          ¬ native_int_pow2 W - 1 < native_int_pow2 W - 1 :=
        Int.lt_irrefl _
      simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
        __smtx_model_eval_eq, __smtx_model_eval_not, native_veq,
        native_not, SmtEval.native_zlt, hNotLt]
    · have hLt : px < native_int_pow2 W - 1 := by
        rcases Int.lt_or_eq_of_le hPxLe with hLt | hEq'
        · exact hLt
        · exact False.elim (hEq hEq')
      simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
        __smtx_model_eval_eq, __smtx_model_eval_not,
        native_zlt, SmtEval.native_zlt, native_veq, native_not,
        hEq, hLt]
  have hBool := typed_bv_ult_ones_term x n (Term.Numeral W)
    hXTrans hNTrans hWTrans hResultTy
  unfold bvUltOnesTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvUltOnesTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral W)) n))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvUltOnesDistinct x n (Term.Numeral W))))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _
