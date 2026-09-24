module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def bvZeroExtendElimRhs (x n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) x)
      (Term.Binary 0 0))

private def bvZeroExtendElimTerm (x n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x))
    (bvZeroExtendElimRhs x n)

private theorem prog_bv_zero_extend_eliminate_eq_of_ne_stuck
    (x n : Term) :
    x ≠ Term.Stuck ->
    n ≠ Term.Stuck ->
    __eo_prog_bv_zero_extend_eliminate x n =
      bvZeroExtendElimTerm x n := by
  intro hX hN
  cases x <;> cases n <;>
    simp [__eo_prog_bv_zero_extend_eliminate, bvZeroExtendElimTerm,
      bvZeroExtendElimRhs] at hX hN ⊢

private theorem eo_typeof_eq_left_stuck (T : Term) :
    __eo_typeof_eq Term.Stuck T = Term.Stuck := by
  cases T <;> rfl

private theorem zero_extend_amount_nonneg_of_guard
    (n : Term) :
    __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true ->
    ∃ i : native_Int, n = Term.Numeral i ∧ native_zleq 0 i = true := by
  intro h
  cases n <;> simp [__eo_gt] at h
  case Numeral i =>
    have hi : (-1 : native_Int) < i := by
      simpa [SmtEval.native_zlt] using h
    have hi0 : (0 : native_Int) <= i := by
      have h := Int.add_one_le_iff.mpr hi
      simpa using h
    exact ⟨i, rfl, by simpa [SmtEval.native_zleq] using hi0⟩

private theorem eo_typeof_zero_extend_arg_bitvec_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_zero_extend A idx C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_zero_extend at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_zero_extend_requires_of_ne_stuck
    {idx w : Term}
    (h :
      __eo_typeof_zero_extend (__eo_typeof idx) idx
          (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck) :
    __eo_requires (__eo_gt idx (Term.Numeral (-1 : native_Int)))
        (Term.Boolean true)
        (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add w idx)) ≠
      Term.Stuck := by
  unfold __eo_typeof_zero_extend at h
  split at h <;> simp_all

private theorem typeof_args_of_bv_zero_extend_elim_term_bool
    (x n : Term) :
    __eo_typeof (bvZeroExtendElimTerm x n) = Term.Bool ->
    ∃ w i,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) w ∧
      n = Term.Numeral i ∧
      native_zleq 0 i = true := by
  intro hTy
  change __eo_typeof_eq
      (__eo_typeof_zero_extend (__eo_typeof n) n (__eo_typeof x))
      (__eo_typeof (bvZeroExtendElimRhs x n)) =
    Term.Bool at hTy
  have hLhsNe :
      __eo_typeof_zero_extend (__eo_typeof n) n (__eo_typeof x) ≠
        Term.Stuck := by
    intro h
    rw [h, eo_typeof_eq_left_stuck] at hTy
    cases hTy
  rcases eo_typeof_zero_extend_arg_bitvec_of_ne_stuck hLhsNe with
    ⟨w, hXTy⟩
  have hReq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add w n)) ≠
        Term.Stuck := by
    exact eo_typeof_zero_extend_requires_of_ne_stuck
      (idx := n) (w := w) (by simpa [hXTy] using hLhsNe)
  have hGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReq
  rcases zero_extend_amount_nonneg_of_guard n hGuard with
    ⟨i, hN, hiNonneg⟩
  exact ⟨w, i, hXTy, hN, hiNonneg⟩

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) := by
  intro hXTrans hXType
  have hSmtType :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type
          (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) w)
      (__eo_to_smt x) rfl hXTrans hXType
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hXTrans hSmtType)

private theorem smt_typeof_bv_const
    (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro hNonneg
  change __smtx_typeof (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral k)) =
    SmtType.BitVec (native_int_to_nat n)
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary n (native_mod_total k (native_int_pow2 n))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total k (native_int_pow2 n))
            (native_mod_total
              (native_mod_total k (native_int_pow2 n))
              (native_int_pow2 n)) =
          true :=
      native_mod_total_canonical n k
    simp [SmtEval.native_and, hNonneg, hMod, native_ite]
  simpa [native_ite, hNonneg] using
    TranslationProofs.smtx_typeof_binary_of_non_none n
      (native_mod_total k (native_int_pow2 n)) hNN

private theorem eval_bv_const
    (M : SmtModel) (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
      SmtValue.Binary n (native_mod_total k (native_int_pow2 n)) := by
  intro hNonneg
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral k)) =
    SmtValue.Binary n (native_mod_total k (native_int_pow2 n))
  simp [native_ite, hNonneg]

private theorem native_nat_to_int_int_to_nat_eq
    (n : native_Int) :
    native_zleq 0 n = true ->
    native_nat_to_int (native_int_to_nat n) = n := by
  intro hNonneg
  have hn : (0 : native_Int) <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
    Int.toNat_of_nonneg hn
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem smt_typeof_concat_empty_right_eq
    (x : Term) (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat w) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x)
            (Term.Binary 0 0))) =
      SmtType.BitVec (native_int_to_nat w) := by
  intro hWNonneg hXSmtTy
  have hRound := native_nat_to_int_int_to_nat_eq w hWNonneg
  have hBinary0Ty :
      __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0 := by
    native_decide
  change __smtx_typeof (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0)) =
    SmtType.BitVec (native_int_to_nat w)
  rw [typeof_concat_eq, hXSmtTy, hBinary0Ty]
  simp [__smtx_typeof_concat, hXSmtTy, __smtx_typeof, hRound,
    SmtEval.native_zplus, native_int_to_nat, native_nat_to_int]
  have hw : (0 : native_Int) <= w := by
    simpa [SmtEval.native_zleq] using hWNonneg
  have hMax : max w 0 = w := by
    by_cases hlt : w < 0
    · exact False.elim ((Int.not_lt_of_ge hw) hlt)
    · simp [max, hlt]
      intro hwle
      exact (Int.le_antisymm hwle hw).symm
  simp [hMax]

private theorem smt_typeof_zero_extend_eq_rhs
    (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvZeroExtendElimTerm x n) = Term.Bool ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x)) =
      __smtx_typeof (__eo_to_smt (bvZeroExtendElimRhs x n)) := by
  intro hXTrans hResultTy
  rcases typeof_args_of_bv_zero_extend_elim_term_bool x n hResultTy with
    ⟨u, i, hXTy, hN, hiNonneg⟩
  subst n
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x u hXTrans hXTy with
    ⟨w, hU, hWNonneg, hXSmtTy⟩
  subst u
  have hRoundI := native_nat_to_int_int_to_nat_eq i hiNonneg
  have hRoundW := native_nat_to_int_int_to_nat_eq w hWNonneg
  have hZeroTy := smt_typeof_bv_const 0 i hiNonneg
  have hInnerTy := smt_typeof_concat_empty_right_eq x w hWNonneg hXSmtTy
  have hInnerTySmt :
      __smtx_typeof (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0)) =
        SmtType.BitVec (native_int_to_nat w) := by
    exact hInnerTy
  have hLhs :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x)) =
        SmtType.BitVec (native_int_to_nat (native_zplus i w)) := by
    change __smtx_typeof
        (SmtTerm.zero_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus i w))
    rw [typeof_zero_extend_eq, hXSmtTy]
    simp [__smtx_typeof_zero_extend, native_ite, hiNonneg, hRoundW]
  have hRhs :
      __smtx_typeof (__eo_to_smt (bvZeroExtendElimRhs x (Term.Numeral i))) =
        SmtType.BitVec (native_int_to_nat (native_zplus i w)) := by
    unfold bvZeroExtendElimRhs
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 0)))
          (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0))) =
      SmtType.BitVec (native_int_to_nat (native_zplus i w))
    rw [typeof_concat_eq, hZeroTy, hInnerTySmt]
    simp [__smtx_typeof_concat, hRoundI, hRoundW]
  rw [hLhs, hRhs]

private theorem typed_bv_zero_extend_elim_term
    (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvZeroExtendElimTerm x n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvZeroExtendElimTerm x n) := by
  intro hXTrans hResultTy
  unfold bvZeroExtendElimTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x)
    (bvZeroExtendElimRhs x n)
    (smt_typeof_zero_extend_eq_rhs x n hXTrans hResultTy)
    (by
      rw [smt_typeof_zero_extend_eq_rhs x n hXTrans hResultTy]
      rcases typeof_args_of_bv_zero_extend_elim_term_bool x n hResultTy with
        ⟨u, i, hXTy, hN, hiNonneg⟩
      subst n
      rcases smt_bitvec_type_of_eo_bitvec_type_with_width x u hXTrans hXTy with
        ⟨w, hU, hWNonneg, hXSmtTy⟩
      subst u
      have hRoundI := native_nat_to_int_int_to_nat_eq i hiNonneg
      have hRoundW := native_nat_to_int_int_to_nat_eq w hWNonneg
      have hZeroTy := smt_typeof_bv_const 0 i hiNonneg
      have hInnerTy := smt_typeof_concat_empty_right_eq x w hWNonneg hXSmtTy
      have hInnerTySmt :
          __smtx_typeof (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0)) =
            SmtType.BitVec (native_int_to_nat w) := by
        exact hInnerTy
      unfold bvZeroExtendElimRhs
      change __smtx_typeof
          (SmtTerm.concat
            (__eo_to_smt
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 0)))
            (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0))) ≠
        SmtType.None
      rw [typeof_concat_eq, hZeroTy, hInnerTySmt]
      simp [__smtx_typeof_concat, hRoundI, hRoundW])

private theorem smtx_eval_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.concat x y) =
      __smtx_model_eval_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_zero_extend_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.zero_extend x y) =
      __smtx_model_eval_zero_extend
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem concat_empty_right_value
    (w payload : native_Int) :
    native_zeq payload
        (native_mod_total payload (native_int_pow2 w)) =
      true ->
    __smtx_model_eval_concat
      (SmtValue.Binary w payload) (SmtValue.Binary 0 0) =
      SmtValue.Binary w payload := by
  intro hCanon
  have hMod :
      native_mod_total payload (native_int_pow2 w) = payload := by
    have hEq : payload =
        native_mod_total payload (native_int_pow2 w) := by
      simpa [SmtEval.native_zeq] using hCanon
    exact hEq.symm
  have hPow0 : native_int_pow2 0 = (1 : native_Int) := by
    native_decide
  simp [__smtx_model_eval_concat, native_binary_concat, SmtEval.native_zplus,
    SmtEval.native_zmult, hPow0, hMod]

private theorem concat_zeros_left_value
    (i w payload : native_Int) :
    native_zeq payload
        (native_mod_total payload (native_int_pow2 (native_zplus i w))) =
      true ->
    __smtx_model_eval_concat
      (SmtValue.Binary i 0) (SmtValue.Binary w payload) =
      SmtValue.Binary (native_zplus i w) payload := by
  intro hCanon
  have hMod :
      native_mod_total payload (native_int_pow2 (native_zplus i w)) =
        payload := by
    have hEq : payload =
        native_mod_total payload (native_int_pow2 (native_zplus i w)) := by
      simpa [SmtEval.native_zeq] using hCanon
    exact hEq.symm
  have hMod' :
      native_mod_total payload (native_int_pow2 (i + w)) = payload := by
    simpa [SmtEval.native_zplus] using hMod
  simp [__smtx_model_eval_concat, native_binary_concat, SmtEval.native_zplus,
    SmtEval.native_zmult, hMod, hMod']

private theorem native_int_pow2_pos_of_nonneg {w : native_Int}
    (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

private theorem native_mod_zero_pow2
    (w : native_Int) :
    native_zleq 0 w = true ->
    native_mod_total 0 (native_int_pow2 w) = 0 := by
  intro hW
  have hw : (0 : native_Int) <= w := by
    simpa [SmtEval.native_zleq] using hW
  have hPowPos := native_int_pow2_pos_of_nonneg hw
  simpa [SmtEval.native_mod_total] using
    Int.emod_eq_of_lt (by decide : (0 : native_Int) <= 0) hPowPos

private theorem eval_zero_extend_matches_concat
    (M : SmtModel) (hM : model_wf M) (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvZeroExtendElimTerm x n) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x)) =
      __smtx_model_eval M (__eo_to_smt (bvZeroExtendElimRhs x n)) := by
  intro hXTrans hResultTy
  rcases typeof_args_of_bv_zero_extend_elim_term_bool x n hResultTy with
    ⟨u, i, hXTy, hN, hiNonneg⟩
  subst n
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x u hXTrans hXTy with
    ⟨w, hU, hWNonneg, hXSmtTy⟩
  subst u
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hXTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX⟩
  have hRoundW := native_nat_to_int_int_to_nat_eq w hWNonneg
  rw [hRoundW] at hEvalX
  have hEvalTyW :
      __smtx_typeof_value (SmtValue.Binary w payload) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hEvalX] using hEvalTy
  have hPayloadCanon :
      native_zeq payload
          (native_mod_total payload (native_int_pow2 w)) =
        true :=
    bitvec_payload_canonical hEvalTyW
  have hPayloadCanonExt :
      native_zeq payload
          (native_mod_total payload
            (native_int_pow2 (native_zplus i w))) =
        true :=
    bitvec_payload_canonical_zero_extend hiNonneg hWNonneg hPayloadCanon
  have hZeroEval := eval_bv_const M 0 i hiNonneg
  have hZeroMod := native_mod_zero_pow2 i hiNonneg
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := by
    change __smtx_model_eval M (SmtTerm.Binary 0 0) =
      SmtValue.Binary 0 0
    simp only [__smtx_model_eval]
  have hInnerEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x)
              (Term.Binary 0 0))) =
        SmtValue.Binary w payload := by
    change __smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0)) =
      SmtValue.Binary w payload
    have hEmptyEvalSmt :
        __smtx_model_eval M (SmtTerm.Binary 0 0) =
          SmtValue.Binary 0 0 := by
      exact hEmptyEval
    rw [smtx_eval_concat_term_eq, hEvalX, hEmptyEvalSmt]
    exact concat_empty_right_value w payload hPayloadCanon
  have hInnerEvalSmt :
      __smtx_model_eval M
          (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0)) =
        SmtValue.Binary w payload := by
    exact hInnerEval
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (bvZeroExtendElimRhs x (Term.Numeral i))) =
        SmtValue.Binary (native_zplus i w) payload := by
    unfold bvZeroExtendElimRhs
    change __smtx_model_eval M
        (SmtTerm.concat
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 0)))
          (SmtTerm.concat (__eo_to_smt x) (SmtTerm.Binary 0 0))) =
      SmtValue.Binary (native_zplus i w) payload
    rw [smtx_eval_concat_term_eq, hZeroEval, hInnerEvalSmt, hZeroMod]
    exact concat_zeros_left_value i w payload hPayloadCanonExt
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral i)) x)) =
        SmtValue.Binary (native_zplus i w) payload := by
    change __smtx_model_eval M
        (SmtTerm.zero_extend (SmtTerm.Numeral i) (__eo_to_smt x)) =
      SmtValue.Binary (native_zplus i w) payload
    rw [smtx_eval_zero_extend_term_eq, smtx_eval_numeral_term_eq, hEvalX]
    rfl
  rw [hLhsEval, hRhsEval]

private theorem facts_bv_zero_extend_elim_term
    (M : SmtModel) (hM : model_wf M) (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvZeroExtendElimTerm x n) = Term.Bool ->
    eo_interprets M (bvZeroExtendElimTerm x n) true := by
  intro hXTrans hResultTy
  have hTermBool := typed_bv_zero_extend_elim_term x n hXTrans hResultTy
  unfold bvZeroExtendElimTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvZeroExtendElimTerm] using hTermBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend n) x)))
      (__smtx_model_eval M (__eo_to_smt (bvZeroExtendElimRhs x n)))
    rw [eval_zero_extend_matches_concat M hM x n hXTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_zero_extend_eliminate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_zero_extend_eliminate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_eliminate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_zero_extend_eliminate args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  change StepRuleProperties M []
                    (__eo_prog_bv_zero_extend_eliminate a1 a2)
                  have hProgLocal :
                      __eo_prog_bv_zero_extend_eliminate a1 a2 ≠ Term.Stuck := by
                    exact hProg
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  change __eo_typeof (__eo_prog_bv_zero_extend_eliminate a1 a2) =
                    Term.Bool at hResultTy
                  have hA1Ne : a1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                  have hA2Ne : a2 ≠ Term.Stuck := by
                    intro h
                    subst a2
                    exact hProgLocal (by
                      cases a1 <;> rfl)
                  have hResultTyCanonical :
                      __eo_typeof (bvZeroExtendElimTerm a1 a2) = Term.Bool := by
                    simpa [prog_bv_zero_extend_eliminate_eq_of_ne_stuck
                      a1 a2 hA1Ne hA2Ne] using hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bv_zero_extend_eliminate a1 a2) true
                    rw [prog_bv_zero_extend_eliminate_eq_of_ne_stuck a1 a2 hA1Ne hA2Ne]
                    exact facts_bv_zero_extend_elim_term M hM a1 a2
                      hA1Trans hResultTyCanonical
                  · rw [prog_bv_zero_extend_eliminate_eq_of_ne_stuck a1 a2 hA1Ne hA2Ne]
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed_bv_zero_extend_elim_term a1 a2 hA1Trans
                        hResultTyCanonical)
