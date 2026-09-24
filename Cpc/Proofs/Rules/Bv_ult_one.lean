module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def bvUltOnePrem (x : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.gt)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        (Term.Numeral 0)))
    (Term.Boolean true)

private def bvUltOneTerm (x n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.bvult) x)
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 1))))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq) x)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0)))

private theorem prog_bv_ult_one_eq_of_ne_stuck (x n : Term) :
    x ≠ Term.Stuck ->
    n ≠ Term.Stuck ->
    __eo_prog_bv_ult_one x n (Proof.pf (bvUltOnePrem x)) =
      bvUltOneTerm x n := by
  intro hX hN
  cases x <;> cases n <;>
    simp [__eo_prog_bv_ult_one, bvUltOnePrem, bvUltOneTerm,
      __eo_requires, __eo_eq, native_ite, native_teq, native_not,
      SmtEval.native_not] at hX hN ⊢

private theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x := by
  intro hProg
  -- v4.33 `simp` unfolds `__eo_eq` under `decide` and desyncs the
  -- `Decidable` instance, so derive the guard by contradiction instead.
  have hEq : __eo_eq x y = Term.Boolean true := by
    apply Classical.byContradiction
    intro hne
    apply hProg
    simp [__eo_requires, native_ite, native_teq, hne]
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at hEq
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at hEq
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using hEq
      simpa [native_teq] using hDec

private theorem eo_typeof_eq_left_stuck (T : Term) :
    __eo_typeof_eq Term.Stuck T = Term.Stuck := by
  cases T <;> rfl

private theorem eo_typeof_eq_right_stuck (T : Term) :
    __eo_typeof_eq T Term.Stuck = Term.Stuck := by
  cases T <;> rfl

private theorem eo_typeof_bvult_stuck_left (T : Term) :
    __eo_typeof_bvult Term.Stuck T = Term.Stuck := by
  cases T <;> rfl

private theorem eo_typeof_bvult_stuck_right (T : Term) :
    __eo_typeof_bvult T Term.Stuck = Term.Stuck := by
  cases T <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

private theorem bv_ult_one_shape_of_ne_stuck (x n P : Term) :
    __eo_prog_bv_ult_one x n (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ n ≠ Term.Stuck ∧
      ∃ px, P = bvUltOnePrem px := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_ult_one.eq_1 n (Proof.pf P))
  have hNNe : n ≠ Term.Stuck := by
    intro hN
    subst n
    exact hProg (__eo_prog_bv_ult_one.eq_2 x (Proof.pf P) hXNe)
  refine ⟨hXNe, hNNe, ?_⟩
  by_cases hShape : ∃ px, P = bvUltOnePrem px
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_ult_one.eq_4 x n (Proof.pf P) hXNe hNNe (by
        intro px hP
        cases hP
        exact hShape ⟨px, rfl⟩)))

private theorem typeof_args_of_bv_ult_one_term_bool (x n : Term) :
    __eo_typeof (bvUltOneTerm x n) = Term.Bool ->
    ∃ w, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      n = w ∧ w ≠ Term.Stuck := by
  intro hTy
  by_cases hX : x = Term.Stuck
  · subst x
    change __eo_typeof_eq
        (__eo_typeof_bvult Term.Stuck
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)))
        (__eo_typeof_eq Term.Stuck
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))) =
      Term.Bool at hTy
    rw [eo_typeof_bvult_stuck_left, eo_typeof_eq_left_stuck] at hTy
    cases hTy
  · by_cases hN : n = Term.Stuck
    · subst n
      change __eo_typeof_eq
          (__eo_typeof_bvult (__eo_typeof x) Term.Stuck)
          (__eo_typeof_eq (__eo_typeof x) Term.Stuck) =
        Term.Bool at hTy
      rw [eo_typeof_bvult_stuck_right, eo_typeof_eq_right_stuck,
        eo_typeof_eq_left_stuck] at hTy
      cases hTy
    · change __eo_typeof_eq
          (__eo_typeof_bvult (__eo_typeof x)
            (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)))
          (__eo_typeof_eq (__eo_typeof x)
            (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))) =
        Term.Bool at hTy
      cases hXTy : __eo_typeof x with
      | Apply f w =>
          cases f with
          | UOp op =>
              cases op
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
              · exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
              · cases hNTy : __eo_typeof n with
                | UOp nop =>
                    cases nop
                    · have hEq : n = w :=
                        bv_width_eq_of_typeof_bvult_at_bv_right_eq_bool
                          w n hN hNTy (by simpa [hXTy] using hTy)
                      subst n
                      exact ⟨w, by simpa [hXTy], rfl, hN⟩
                    all_goals
                      exfalso
                      simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                        __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                        hXTy, hNTy] using hTy
                | _ =>
                    exfalso
                    simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                      __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                      hXTy, hNTy] using hTy
              all_goals
                exfalso
                simpa [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                  __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                  hXTy] using hTy
          | _ =>
              simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
                __eo_requires, __eo_eq, native_ite, native_teq, native_not,
                hXTy] at hTy
      | _ =>
          simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_int_to_bv,
            __eo_requires, __eo_eq, native_ite, native_teq, native_not,
            hXTy] at hTy

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

private theorem native_int_pow2_one_lt_of_pos
    {w : native_Int} (hw : 0 < w) :
    1 < native_int_pow2 w := by
  have hwNonneg : 0 <= w := Int.le_of_lt hw
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hwNonneg
  have hwNatNe : Int.toNat w ≠ 0 := by
    intro hZero
    have hwle : w <= 0 := Int.toNat_eq_zero.mp hZero
    exact (Int.not_le_of_gt hw) hwle
  have hNat : 1 < (2 : Nat) ^ Int.toNat w :=
    Nat.one_lt_pow hwNatNe (by decide : 1 < (2 : Nat))
  rw [native_int_pow2, native_zexp_total]
  simp [hnot]
  exact_mod_cast hNat

private theorem smtx_eval_gt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem bool_of_true_eval
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

private theorem eval_bvsize_eq (M : SmtModel) (x : Term) (n : native_Int)
    (hNonneg : native_zleq 0 n = true)
    (hXSmt : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n)) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral (native_nat_to_int (native_int_to_nat n)) := by
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0 (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) =
    SmtValue.Numeral (native_nat_to_int (native_int_to_nat n))
  have hSize : __eo_to_smt_bv_size (SmtType.BitVec (native_int_to_nat n)) =
      native_nat_to_int (native_int_to_nat n) := rfl
  have hNN :
      native_zleq 0 (native_nat_to_int (native_int_to_nat n)) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int]
  rw [hXSmt, hSize]
  simp [native_ite, hNN]
  simp [__smtx_model_eval, __smtx_model_eval__at_purify]

private theorem bv_ult_one_prem_width_pos
    (M : SmtModel) (x : Term) (n : native_Int) :
    eo_interprets M (bvUltOnePrem x) true ->
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    native_zlt 0 n = true := by
  intro hPrem hNonneg hXSmt
  have hnNonneg : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hWidthEq : native_nat_to_int (native_int_to_nat n) = n := by
    have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
      Int.toNat_of_nonneg hnNonneg
    simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  have hEvalSize := eval_bvsize_eq M x n hNonneg hXSmt
  have hEvalPrem :
      __smtx_model_eval M (__eo_to_smt (bvUltOnePrem x)) =
        SmtValue.Boolean (native_zlt 0 n) := by
    unfold bvUltOnePrem
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.gt
            (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (SmtTerm.Numeral 0))
          (SmtTerm.Boolean true)) =
      SmtValue.Boolean (native_zlt 0 n)
    rw [smtx_eval_eq_term_eq, smtx_eval_gt_term_eq, hEvalSize,
      smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt,
      __smtx_model_eval_eq, native_zlt, SmtEval.native_zlt, native_veq,
      hWidthEq]
  exact bool_of_true_eval hPrem hEvalPrem

private theorem eo_has_bool_type_bvult_one_lhs
    (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvUltOneTerm x n) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.bvult) x)
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 1))) := by
  intro hXTrans hResultTy
  rcases typeof_args_of_bv_ult_one_term_bool x n hResultTy with
    ⟨w, hXType, hN, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x w hXTrans hXType with
    ⟨i, hW, hNonneg, hXSmtTy⟩
  subst w
  subst n
  have hOneTy := smt_typeof_bv_const 1 i hNonneg
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof
      (SmtTerm.bvult (__eo_to_smt x)
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 1)))) =
    SmtType.Bool
  rw [__smtx_typeof.eq_56]
  simp [__smtx_typeof_bv_op_2_ret, hXSmtTy, hOneTy, native_nateq, native_ite]

private theorem eo_has_bool_type_eq_bv_zero
    (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvUltOneTerm x n) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq) x)
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0))) := by
  intro hXTrans hResultTy
  rcases typeof_args_of_bv_ult_one_term_bool x n hResultTy with
    ⟨w, hXType, hN, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x w hXTrans hXType with
    ⟨i, hW, hNonneg, hXSmtTy⟩
  subst w
  subst n
  have hZeroTy := smt_typeof_bv_const 0 i hNonneg
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x
    (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 0))
    (hXSmtTy.trans hZeroTy.symm)
    (by
      rw [hXSmtTy]
      intro hNone
      cases hNone)

private theorem typed_bv_ult_one_term
    (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvUltOneTerm x n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvUltOneTerm x n) := by
  intro hXTrans hResultTy
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvult) x)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 1))) :=
    eo_has_bool_type_bvult_one_lhs x n hXTrans hResultTy
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) x)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0))) :=
    eo_has_bool_type_eq_bv_zero x n hXTrans hResultTy
  unfold bvUltOneTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvult) x)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 1)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq) x)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0)))
    (hLhsBool.trans hRhsBool.symm)
    (by
      rw [hLhsBool]
      decide)

private theorem eval_bvult_one_matches_eq_zero
    (M : SmtModel) (hM : model_wf M) (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    eo_interprets M (bvUltOnePrem x) true ->
    __eo_typeof (bvUltOneTerm x n) = Term.Bool ->
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvult) x)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 1)))) =
      __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) x)
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0)))) := by
  intro hXTrans hPrem hResultTy
  rcases typeof_args_of_bv_ult_one_term_bool x n hResultTy with
    ⟨w, hXType, hN, _hW⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x w hXTrans hXType with
    ⟨i, hW, hNonneg, hXSmtTy⟩
  subst w
  subst n
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat i) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hXTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX⟩
  have hiNonneg : 0 <= i := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hWidthEq : native_nat_to_int (native_int_to_nat i) = i := by
    have hInt : (Int.ofNat (Int.toNat i) : Int) = i :=
      Int.toNat_of_nonneg hiNonneg
    simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  rw [hWidthEq] at hEvalX
  have hEvalTyI :
      __smtx_typeof_value (SmtValue.Binary i payload) =
        SmtType.BitVec (native_int_to_nat i) := by
    simpa [hEvalX] using hEvalTy
  have hPayloadCanon :
      native_zeq payload (native_mod_total payload (native_int_pow2 i)) = true := by
    have hCanon := bitvec_payload_canonical hEvalTyI
    simpa using hCanon
  have hPayloadNonneg :
      0 <= payload :=
    (bitvec_payload_range_of_canonical
      (bitvec_width_nonneg hEvalTyI) hPayloadCanon).1
  have hWidthPosBool := bv_ult_one_prem_width_pos M x i hPrem hNonneg hXSmtTy
  have hiPos : 0 < i := by
    simpa [SmtEval.native_zlt] using hWidthPosBool
  have hOneMod :
      native_mod_total 1 (native_int_pow2 i) = 1 := by
    have hPowGt := native_int_pow2_one_lt_of_pos hiPos
    simpa [SmtEval.native_mod_total] using
      Int.emod_eq_of_lt (by decide : (0 : Int) <= 1) hPowGt
  have hZeroMod :
      native_mod_total 0 (native_int_pow2 i) = 0 := by
    have hPowPos : 0 < native_int_pow2 i :=
      Int.lt_trans (by decide : (0 : Int) < 1) (native_int_pow2_one_lt_of_pos hiPos)
    simpa [SmtEval.native_mod_total] using
      Int.emod_eq_of_lt (by decide : (0 : Int) <= 0) hPowPos
  have hOneEval := eval_bv_const M 1 i hNonneg
  have hZeroEval := eval_bv_const M 0 i hNonneg
  change __smtx_model_eval M
      (SmtTerm.bvult (__eo_to_smt x)
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 1)))) =
    __smtx_model_eval M
      (SmtTerm.eq (__eo_to_smt x)
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 0))))
  rw [__smtx_model_eval.eq_56, smtx_eval_eq_term_eq, hEvalX, hOneEval, hZeroEval]
  by_cases hPayloadZero : payload = 0
  · subst payload
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      __smtx_model_eval_eq, native_zlt, SmtEval.native_zlt, native_veq,
      hOneMod, hZeroMod]
  · have hPayloadPos : 0 < payload := by
      rcases Int.lt_or_gt_of_ne hPayloadZero with hNeg | hPos
      · exact False.elim ((Int.not_lt_of_ge hPayloadNonneg) hNeg)
      · exact hPos
    have hPayloadGeOne : 1 <= payload :=
      Int.add_one_le_iff.mpr hPayloadPos
    have hPayloadNotLtOne : ¬ payload < 1 :=
      Int.not_lt_of_ge hPayloadGeOne
    have hZeroNePayload : ¬0 = payload := by
      intro h
      exact hPayloadZero h.symm
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      __smtx_model_eval_eq, native_zlt, SmtEval.native_zlt, native_veq,
      hOneMod, hZeroMod, hPayloadZero, hPayloadNotLtOne,
      hZeroNePayload]

private theorem facts_bv_ult_one_term
    (M : SmtModel) (hM : model_wf M) (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    eo_interprets M (bvUltOnePrem x) true ->
    __eo_typeof (bvUltOneTerm x n) = Term.Bool ->
    eo_interprets M (bvUltOneTerm x n) true := by
  intro hXTrans hPrem hResultTy
  have hTermBool := typed_bv_ult_one_term x n hXTrans hResultTy
  unfold bvUltOneTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvUltOneTerm] using hTermBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvult) x)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 1)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0)))))
    rw [eval_bvult_one_matches_eq_zero M hM x n hXTrans hPrem hResultTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_ult_one_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ult_one args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_one args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ult_one args premises ≠ Term.Stuck :=
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
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n1 premises =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      let P1 := __eo_state_proven_nth s n1
                      change
                        StepRuleProperties M [P1]
                          (__eo_prog_bv_ult_one a1 a2 (Proof.pf P1))
                      have hProgLocal :
                          __eo_prog_bv_ult_one a1 a2 (Proof.pf P1) ≠ Term.Stuck :=
                        hProg
                      rcases bv_ult_one_shape_of_ne_stuck a1 a2 P1 hProgLocal with
                        ⟨hA1Ne, hA2Ne, px, hP1⟩
                      have hReqNe : __eo_requires (__eo_eq a1 px) (Term.Boolean true)
                            (bvUltOneTerm a1 a2) ≠ Term.Stuck := by
                        have h := hProgLocal
                        rw [hP1] at h
                        unfold bvUltOnePrem at h
                        rw [__eo_prog_bv_ult_one.eq_3 a1 a2 px hA1Ne hA2Ne] at h
                        simpa [bvUltOnePrem, bvUltOneTerm] using h
                      have hPx : px = a1 :=
                        eq_of_requires_eq_true_not_stuck a1 px (bvUltOneTerm a1 a2) hReqNe
                      subst px
                      have hATransPair :
                          RuleProofs.eo_has_smt_translation a1 ∧
                            RuleProofs.eo_has_smt_translation a2 ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                      have hResultTyCanonical :
                          __eo_typeof (bvUltOneTerm a1 a2) = Term.Bool := by
                        have hResultTyLocal := hResultTy
                        change __eo_typeof
                            (__eo_prog_bv_ult_one a1 a2
                              (Proof.pf (__eo_state_proven_nth s n1))) =
                          Term.Bool at hResultTyLocal
                        simpa [P1, hP1, prog_bv_ult_one_eq_of_ne_stuck
                          a1 a2 hA1Ne hA2Ne] using hResultTyLocal
                      refine ⟨?_, ?_⟩
                      · intro hTrue
                        have hPrem :
                            eo_interprets M (bvUltOnePrem a1) true := by
                          simpa [hP1] using hTrue.true_here P1 (by simp)
                        change eo_interprets M
                          (__eo_prog_bv_ult_one a1 a2 (Proof.pf P1)) true
                        rw [hP1, prog_bv_ult_one_eq_of_ne_stuck a1 a2 hA1Ne hA2Ne]
                        exact facts_bv_ult_one_term M hM a1 a2 hA1Trans hPrem
                          hResultTyCanonical
                      · rw [hP1, prog_bv_ult_one_eq_of_ne_stuck a1 a2 hA1Ne hA2Ne]
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed_bv_ult_one_term a1 a2 hA1Trans hResultTyCanonical)
