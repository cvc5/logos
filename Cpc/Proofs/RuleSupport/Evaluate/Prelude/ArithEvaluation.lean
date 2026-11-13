module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Init.Data.Repr
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithComparison
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithComparison

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.eo_eq_numeral_zero_true_eq
    (x : Term) :
    __eo_eq x (Term.Numeral 0) = Term.Boolean true ->
    x = Term.Numeral 0 := by
  cases x <;> intro h <;> simp [__eo_eq, native_teq] at h ⊢
  exact h.symm

theorem EvaluateProofInternal.eo_eq_rational_zero_true_eq
    (x : Term) :
    __eo_eq x (Term.Rational (native_mk_rational 0 1)) =
        Term.Boolean true ->
    x = Term.Rational (native_mk_rational 0 1) := by
  cases x <;> intro h <;> simp [__eo_eq, native_teq] at h ⊢
  case Rational q =>
    exact h.symm

theorem EvaluateProofInternal.eo_to_q_shape
    (x : Term) :
    __eo_to_q x = Term.Stuck ∨
      ∃ q : native_Rat, __eo_to_q x = Term.Rational q := by
  cases x <;> simp [__eo_to_q]

theorem EvaluateProofInternal.native_to_real_zero_eq
    {n : native_Int} :
    native_to_real n = native_mk_rational 0 1 ->
    n = 0 := by
  intro h
  have h' :
      ((n : Rat) / (1 : Rat)) = ((0 : Rat) / (1 : Rat)) := by
    simpa [native_to_real, native_mk_rational] using h
  rw [rat_div_one_intCast n, rat_zero_div_one] at h'
  exact Rat.intCast_inj.mp h'

theorem EvaluateProofInternal.native_mk_rational_zero_den
    (n : native_Int) :
    native_mk_rational n 0 = native_mk_rational 0 1 := by
  unfold native_mk_rational
  change ((n : Rat) / (0 : Rat)) = ((0 : Rat) / (1 : Rat))
  rw [rat_zero_div_one]
  rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]

theorem EvaluateProofInternal.native_qdiv_total_zero
    (q : native_Rat) :
    native_qdiv_total q (native_mk_rational 0 1) =
      native_mk_rational 0 1 := by
  unfold native_qdiv_total
  rw [native_mk_rational_zero]
  change q / (0 : Rat) = (0 : Rat)
  rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]

theorem EvaluateProofInternal.native_qeq_false_ne
    {q1 q2 : native_Rat} :
    native_qeq q1 q2 = false ->
    q1 ≠ q2 := by
  intro h hEq
  unfold native_qeq at h
  simp [hEq] at h

theorem EvaluateProofInternal.native_to_real_qdiv_total_eval
    (n1 n2 : native_Int) :
    native_qdiv_total (native_to_real n1) (native_to_real n2) =
      native_mk_rational n1 n2 := by
  rw [native_qdiv_total, native_to_real, native_to_real, native_mk_rational,
    native_mk_rational, native_mk_rational]
  rw [Rat.div_def]
  have hInv :
      ((↑n2 / ↑(1 : Int) : Rat)⁻¹) =
        ((↑(1 : Int) / ↑n2 : Rat)) := by
    simpa [Rat.divInt_eq_div] using (Rat.inv_divInt n2 1)
  rw [hInv]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 1 (d₁ := 1) (d₂ := n2))

theorem EvaluateProofInternal.eo_ite_guard_cases_of_ne_stuck
    (c x y : Term) :
    __eo_ite c x y ≠ Term.Stuck ->
    c = Term.Boolean true ∨ c = Term.Boolean false := by
  intro h
  by_cases hTrue : native_teq c (Term.Boolean true) = true
  · left
    simpa [native_teq] using hTrue
  · by_cases hFalse : native_teq c (Term.Boolean false) = true
    · right
      simpa [native_teq] using hFalse
    · simp [__eo_ite, hTrue, hFalse, native_ite] at h

theorem EvaluateProofInternal.eo_qdiv_total_to_q_args_shape_of_typeof_real
    (x y : Term) :
    __eo_ite
        (__eo_eq (__eo_to_q y) (Term.Rational (native_mk_rational 0 1)))
        (Term.Rational (native_mk_rational 0 1))
        (__eo_qdiv (__eo_to_q x) (__eo_to_q y)) ≠ Term.Stuck ->
    __eo_typeof
        (__eo_ite
          (__eo_eq (__eo_to_q y) (Term.Rational (native_mk_rational 0 1)))
          (Term.Rational (native_mk_rational 0 1))
          (__eo_qdiv (__eo_to_q x) (__eo_to_q y))) =
      Term.UOp UserOp.Real ->
    ∃ qy : native_Rat, __eo_to_q y = Term.Rational qy ∧
      (qy = native_mk_rational 0 1 ∨
        ∃ qx : native_Rat, __eo_to_q x = Term.Rational qx ∧
          native_qeq (native_mk_rational 0 1) qy = false) := by
  intro hNe hTy
  rcases EvaluateProofInternal.eo_ite_guard_cases_of_ne_stuck
      (__eo_eq (__eo_to_q y) (Term.Rational (native_mk_rational 0 1)))
      (Term.Rational (native_mk_rational 0 1))
      (__eo_qdiv (__eo_to_q x) (__eo_to_q y)) hNe with
    hGuard | hGuard
  · have hY :
        __eo_to_q y = Term.Rational (native_mk_rational 0 1) :=
      EvaluateProofInternal.eo_eq_rational_zero_true_eq (__eo_to_q y) hGuard
    exact ⟨native_mk_rational 0 1, hY, Or.inl rfl⟩
  · have hQDivTy :
        __eo_typeof (__eo_qdiv (__eo_to_q x) (__eo_to_q y)) =
          Term.UOp UserOp.Real := by
      rw [hGuard] at hTy
      have hsimpa := hTy
      try simp [__eo_ite] at hsimpa ⊢
      exact hsimpa
    rcases EvaluateProofInternal.eo_to_q_shape y with hYStuck | ⟨qy, hY⟩
    · rw [hYStuck] at hGuard
      simp [__eo_eq] at hGuard
    · by_cases hQEq :
          native_qeq (native_mk_rational 0 1) qy = true
      · rcases EvaluateProofInternal.eo_to_q_shape x with hXStuck | ⟨qx, hX⟩
        · rw [hXStuck, hY] at hQDivTy
          simp [__eo_qdiv] at hQDivTy
          cases hQDivTy
        · rw [hX, hY] at hQDivTy
          simp [__eo_qdiv, hQEq, native_ite] at hQDivTy
          cases hQDivTy
      · have hQEqFalse :
            native_qeq (native_mk_rational 0 1) qy = false := by
          cases hQ : native_qeq (native_mk_rational 0 1) qy <;>
            simp [hQ] at hQEq ⊢
        rcases EvaluateProofInternal.eo_to_q_shape x with hXStuck | ⟨qx, hX⟩
        · rw [hXStuck, hY] at hQDivTy
          simp [__eo_qdiv] at hQDivTy
          cases hQDivTy
        · exact ⟨qy, hY, Or.inr ⟨qx, hX, hQEqFalse⟩⟩

theorem EvaluateProofInternal.eo_qdiv_to_q_args_shape_of_nonstuck
    (x y : Term) :
    __eo_qdiv (__eo_to_q x) (__eo_to_q y) ≠ Term.Stuck ->
    ∃ qx qy : native_Rat,
      __eo_to_q x = Term.Rational qx ∧
      __eo_to_q y = Term.Rational qy ∧
      native_qeq (native_mk_rational 0 1) qy = false := by
  intro hNe
  rcases EvaluateProofInternal.eo_to_q_shape y with hYStuck | ⟨qy, hY⟩
  · rw [hYStuck] at hNe
    simp [__eo_qdiv] at hNe
  · by_cases hQEq :
        native_qeq (native_mk_rational 0 1) qy = true
    · rcases EvaluateProofInternal.eo_to_q_shape x with hXStuck | ⟨qx, hX⟩
      · rw [hXStuck, hY] at hNe
        simp [__eo_qdiv] at hNe
      · rw [hX, hY] at hNe
        simp [__eo_qdiv, hQEq, native_ite] at hNe
    · have hQEqFalse :
          native_qeq (native_mk_rational 0 1) qy = false := by
        cases hQ : native_qeq (native_mk_rational 0 1) qy <;>
          simp [hQ] at hQEq ⊢
      rcases EvaluateProofInternal.eo_to_q_shape x with hXStuck | ⟨qx, hX⟩
      · rw [hXStuck, hY] at hNe
        simp [__eo_qdiv] at hNe
      · exact ⟨qx, qy, hX, hY, hQEqFalse⟩

theorem EvaluateProofInternal.eo_div_total_args_shape_of_typeof_int
    (x y : Term) :
    __eo_ite (__eo_eq y (Term.Numeral 0))
        (Term.Numeral 0) (__eo_zdiv x y) ≠ Term.Stuck ->
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          (Term.Numeral 0) (__eo_zdiv x y)) =
      Term.UOp UserOp.Int ->
    ∃ ny : native_Int, y = Term.Numeral ny ∧
      (ny = 0 ∨
        ∃ nx : native_Int, x = Term.Numeral nx ∧
          native_zeq 0 ny = false) := by
  intro hNe hTy
  rcases EvaluateProofInternal.eo_ite_guard_cases_of_ne_stuck
      (__eo_eq y (Term.Numeral 0))
      (Term.Numeral 0) (__eo_zdiv x y) hNe with
    hGuard | hGuard
  · have hY : y = Term.Numeral 0 :=
      EvaluateProofInternal.eo_eq_numeral_zero_true_eq y hGuard
    subst y
    exact ⟨0, rfl, Or.inl rfl⟩
  · have hZDivTy :
        __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int := by
      rw [hGuard] at hTy
      have hsimpa := hTy
      try simp [__eo_ite] at hsimpa ⊢
      exact hsimpa
    rcases EvaluateProofInternal.eo_zdiv_args_numeral_of_typeof_int x y hZDivTy with
      ⟨nx, ny, hX, hY, hNZ⟩
    exact ⟨ny, hY, Or.inr ⟨nx, hX, hNZ⟩⟩

theorem EvaluateProofInternal.eo_mod_total_args_shape_of_typeof_int
    (x y : Term) :
    __eo_ite (__eo_eq y (Term.Numeral 0))
        x (__eo_zmod x y) ≠ Term.Stuck ->
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          x (__eo_zmod x y)) =
      Term.UOp UserOp.Int ->
    ∃ ny : native_Int, y = Term.Numeral ny ∧
      (ny = 0 ∨
        ∃ nx : native_Int, x = Term.Numeral nx ∧
          native_zeq 0 ny = false) := by
  intro hNe hTy
  rcases EvaluateProofInternal.eo_ite_guard_cases_of_ne_stuck
      (__eo_eq y (Term.Numeral 0))
      x (__eo_zmod x y) hNe with
    hGuard | hGuard
  · have hY : y = Term.Numeral 0 :=
      EvaluateProofInternal.eo_eq_numeral_zero_true_eq y hGuard
    subst y
    exact ⟨0, rfl, Or.inl rfl⟩
  · have hZModTy :
        __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int := by
      rw [hGuard] at hTy
      have hsimpa := hTy
      try simp [__eo_ite] at hsimpa ⊢
      exact hsimpa
    rcases EvaluateProofInternal.eo_zmod_args_numeral_of_typeof_int x y hZModTy with
      ⟨nx, ny, hX, hY, hNZ⟩
    exact ⟨ny, hY, Or.inr ⟨nx, hX, hNZ⟩⟩

theorem EvaluateProofInternal.eo_typeof_int_pow2_eq_int_arg_eq_int
    (T : Term) :
    __eo_typeof_int_pow2 T = Term.UOp UserOp.Int ->
    T = Term.UOp UserOp.Int := by
  cases T <;> intro h <;> simp [__eo_typeof_int_pow2] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem EvaluateProofInternal.eo_int_pow2_result_arg_typeof_int
    (x : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) x)) =
      Term.UOp UserOp.Int ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  cases x <;> intro h
  case Numeral n =>
    rfl
  all_goals
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_pow, __eo_mk_apply, native_ite, native_teq, native_not] at h
  all_goals
    first
    | cases h
    | exact EvaluateProofInternal.eo_typeof_int_pow2_eq_int_arg_eq_int _ h

theorem EvaluateProofInternal.eo_int_pow2_body_typeof_int
    (x : Term)
    (hTy : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) x)) =
      Term.UOp UserOp.Int := by
  cases x <;>
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_pow, __eo_mk_apply, native_ite, native_teq, native_not,
      native_and] at hTy ⊢
  all_goals
    first
    | rename_i n
      cases hNeg : native_zlt n 0 <;>
        simp [hNeg, __eo_lit_type_Numeral, native_ite]
      all_goals
        change Term.UOp UserOp.Int = Term.UOp UserOp.Int
        rfl
    | change __eo_typeof_int_pow2 (__eo_typeof _) = Term.UOp UserOp.Int
      rw [hTy]
      rfl
    | cases hTy
    | rfl

theorem EvaluateProofInternal.eo_int_pow2_eval_numeral_to_smt
    (n : native_Int) :
    __eo_to_smt
        (__eo_ite (__eo_is_z (Term.Numeral n))
          (__eo_ite (__eo_is_neg (Term.Numeral n)) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) (Term.Numeral n)))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) (Term.Numeral n))) =
      SmtTerm.Numeral (native_int_pow2 n) := by
  by_cases hNeg : n < 0
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_int_pow2,
      native_zexp_total, native_zlt, native_and, native_not, hNeg]
    rfl
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_pow, native_ite, native_teq, native_int_pow2,
      native_zexp_total, native_zlt, native_and, native_not, hNeg]
    rfl

theorem EvaluateProofInternal.native_int_log_rec_two_eq_nat_log2_go
    (fuel remaining : Nat) :
    impl_native_int_log_rec 2 fuel remaining =
      Nat.rec (motive := fun _ => Nat -> Nat) (fun _ => 0)
        (fun _ ih n => Bool.rec 0 (ih (n.div 2)).succ (Nat.ble 2 n))
        fuel remaining := by
  induction fuel generalizing remaining with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [impl_native_int_log_rec, ih]
      by_cases h : remaining < 2
      · cases hBle : Nat.ble 2 remaining
        · simp [h]
        · have hLe : 2 <= remaining := by
            exact Eq.mp Nat.ble_eq hBle
          exact False.elim ((Nat.not_le.mpr h) hLe)
      · cases hBle : Nat.ble 2 remaining
        · have hLe : 2 <= remaining := Nat.le_of_not_gt h
          have hBleTrue : Nat.ble 2 remaining = true :=
            Eq.mpr Nat.ble_eq hLe
          rw [hBle] at hBleTrue
          cases hBleTrue
        · simp [h]
          rw [Nat.add_comm]
          have hDiv : remaining / 2 = remaining.div 2 := rfl
          rw [hDiv]

theorem EvaluateProofInternal.native_int_log_rec_two_eq_nat_log2 (n : Nat) :
    impl_native_int_log_rec 2 n n = Nat.log2 n := by
  unfold Nat.log2
  rw [EvaluateProofInternal.native_int_log_rec_two_eq_nat_log2_go]

theorem EvaluateProofInternal.native_int_log_two_eq_log2 (n : native_Int) :
    native_int_log 2 n = native_int_log2 n := by
  unfold native_int_log native_int_log2
  by_cases h : n.toNat = 0
  · simp [h]
  · simp [h, EvaluateProofInternal.native_int_log_rec_two_eq_nat_log2]

theorem EvaluateProofInternal.native_int_log2_of_neg
    (n : native_Int) (hNeg : n < 0) :
    native_int_log2 n = 0 := by
  unfold native_int_log2
  have hLe : n ≤ 0 := Int.le_of_lt hNeg
  have hToNat : n.toNat = 0 := Int.toNat_eq_zero.mpr hLe
  simp [hToNat, Nat.log2_zero]

theorem EvaluateProofInternal.eo_int_log2_result_arg_typeof_int
    (x : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_log (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_log2) x)) =
      Term.UOp UserOp.Int ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  cases x <;> intro h
  case Numeral n =>
    rfl
  all_goals
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_mk_apply, native_ite, native_teq, native_not] at h
  all_goals
    first
    | cases h
    | exact EvaluateProofInternal.eo_typeof_int_pow2_eq_int_arg_eq_int _ h

theorem EvaluateProofInternal.eo_int_log2_body_typeof_int
    (x : Term)
    (hTy : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_log (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_log2) x)) =
      Term.UOp UserOp.Int := by
  cases x <;>
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_mk_apply, native_ite, native_teq, native_not,
      native_and] at hTy ⊢
  all_goals
    first
    | rename_i n
      cases hNeg : native_zlt n 0 <;>
        simp [hNeg, __eo_lit_type_Numeral, native_ite]
      all_goals
        change Term.UOp UserOp.Int = Term.UOp UserOp.Int
        rfl
    | change __eo_typeof_int_pow2 (__eo_typeof _) = Term.UOp UserOp.Int
      rw [hTy]
      rfl
    | cases hTy
    | rfl

theorem EvaluateProofInternal.eo_int_log2_eval_numeral_to_smt
    (n : native_Int) :
    __eo_to_smt
        (__eo_ite (__eo_is_z (Term.Numeral n))
          (__eo_ite (__eo_is_neg (Term.Numeral n)) (Term.Numeral 0)
            (__eo_log (Term.Numeral 2) (Term.Numeral n)))
          (__eo_mk_apply (Term.UOp UserOp.int_log2) (Term.Numeral n))) =
      SmtTerm.Numeral (native_int_log2 n) := by
  by_cases hNeg : n < 0
  · have hLog0 : native_int_log2 n = 0 :=
      EvaluateProofInternal.native_int_log2_of_neg n hNeg
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_zlt, native_and, native_not,
      hNeg, hLog0]
    rfl
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, native_ite, native_teq, native_zlt, native_and,
      native_not, hNeg, EvaluateProofInternal.native_int_log_two_eq_log2]
    rfl

theorem EvaluateProofInternal.eo_typeof_int_ispow2_eq_bool_arg_eq_int
    (T : Term) :
    __eo_typeof_int_ispow2 T = Term.Bool ->
    T = Term.UOp UserOp.Int := by
  cases T <;> intro h <;> simp [__eo_typeof_int_ispow2] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem EvaluateProofInternal.eo_int_ispow2_result_arg_typeof_int
    (x : Term) :
    __eo_typeof
        (let isNeg := __eo_is_neg x
         let isZ := __eo_is_z x
         __eo_ite isZ
          (__eo_ite isNeg (Term.Boolean false)
            (__eo_eq x
              (__eo_pow (Term.Numeral 2)
                (__eo_ite isZ
                  (__eo_ite isNeg (Term.Numeral 0)
                    (__eo_log (Term.Numeral 2) x))
                  (__eo_mk_apply (Term.UOp UserOp.int_log2) x)))))
          (__eo_mk_apply (Term.UOp UserOp.int_ispow2) x)) =
      Term.Bool ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  cases x <;> intro h
  case Numeral n =>
    rfl
  all_goals
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_pow, __eo_eq, __eo_mk_apply, native_ite,
      native_teq, native_not] at h
  all_goals
    first
    | cases h
    | exact EvaluateProofInternal.eo_typeof_int_ispow2_eq_bool_arg_eq_int _ h

theorem EvaluateProofInternal.eo_int_ispow2_body_typeof_bool
    (x : Term)
    (hTy : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_typeof
        (let isNeg := __eo_is_neg x
         let isZ := __eo_is_z x
         __eo_ite isZ
          (__eo_ite isNeg (Term.Boolean false)
            (__eo_eq x
              (__eo_pow (Term.Numeral 2)
                (__eo_ite isZ
                  (__eo_ite isNeg (Term.Numeral 0)
                    (__eo_log (Term.Numeral 2) x))
                  (__eo_mk_apply (Term.UOp UserOp.int_log2) x)))))
          (__eo_mk_apply (Term.UOp UserOp.int_ispow2) x)) =
      Term.Bool := by
  cases x <;>
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_pow, __eo_eq, __eo_mk_apply, native_ite,
      native_teq, native_not, native_and] at hTy ⊢
  all_goals
    first
    | rename_i n
      cases hNeg : native_zlt n 0 <;>
        simp [hNeg, __eo_lit_type_Numeral, native_ite]
      all_goals
        change Term.Bool = Term.Bool
        rfl
    | change __eo_typeof_int_ispow2 (__eo_typeof _) = Term.Bool
      rw [hTy]
      rfl
    | cases hTy
    | rfl

