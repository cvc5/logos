module

public import Cpc.Proofs.Translation.Inversions
public import Cpc.Proofs.TypePreservation.Full
import all Cpc.Spec
import all Cpc.Logos
import all Cpc.SmtTranslate

/-!
The symbols of the coverings calculus: where one has an SMT translation, its SMT
type is the one its Eunoia type translates to.

A polynomial reaches these symbols as a list of coefficients, and an endpoint of an
interval may be an infinity marker, which has no translation of its own.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

private theorem typeof_at_x :
    __smtx_typeof (SmtTerm.Var (native_string_lit "@x") SmtType.Real) = SmtType.Real := by
  rw [__smtx_typeof.eq_def] <;> simp [__smtx_typeof_guard_wf, __smtx_type_wf, native_ite,
    __smtx_type_wf_component, __smtx_type_wf_rec, native_and]

private theorem typeof_cov_zero :
    __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) = SmtType.Real := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem typeof_exists_eq'
    (s : native_String) (T : SmtType) (t : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem typeof_choice_eq'
    (s : native_String) (T : SmtType) (t : SmtTerm) :
    __smtx_typeof (SmtTerm.choice s T t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool)
        (__smtx_typeof_guard_wf T T)
        SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem native_ite_true {α : Type} (a b : α) : native_ite true a b = a := rfl

private theorem native_ite_bool_of_non_none {A : SmtType} {t : SmtType}
    (h : native_ite (native_Teq A SmtType.Bool) t SmtType.None ≠ SmtType.None) :
    A = SmtType.Bool := by
  by_cases hA : A = SmtType.Bool
  · exact hA
  · simp [native_ite, native_Teq, hA] at h

private theorem typeof_and_parts {a b : SmtTerm}
    (h : __smtx_typeof (SmtTerm.and a b) ≠ SmtType.None) :
    __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool := by
  rw [typeof_and_eq] at h
  have ha := native_ite_bool_of_non_none h
  rw [ha] at h
  refine ⟨ha, native_ite_bool_of_non_none (t := SmtType.Bool) ?_⟩
  simpa [native_ite, native_Teq] using h

private theorem typeof_or_parts {a b : SmtTerm}
    (h : __smtx_typeof (SmtTerm.or a b) ≠ SmtType.None) :
    __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool := by
  rw [typeof_or_eq] at h
  have ha := native_ite_bool_of_non_none h
  rw [ha] at h
  refine ⟨ha, native_ite_bool_of_non_none (t := SmtType.Bool) ?_⟩
  simpa [native_ite, native_Teq] using h

private theorem typeof_not_part {a : SmtTerm}
    (h : __smtx_typeof (SmtTerm.not a) ≠ SmtType.None) :
    __smtx_typeof a = SmtType.Bool := by
  rw [typeof_not_eq] at h
  exact native_ite_bool_of_non_none h

private theorem typeof_exists_part {s : native_String} {T : SmtType} {a : SmtTerm}
    (h : __smtx_typeof (SmtTerm.exists s T a) ≠ SmtType.None) :
    __smtx_typeof a = SmtType.Bool := by
  rw [typeof_exists_eq'] at h
  exact native_ite_bool_of_non_none h

private theorem non_none_of_bool {A : SmtType} (h : A = SmtType.Bool) : A ≠ SmtType.None := by
  rw [h]; simp

private theorem arith_op2_arg_non_none {A B : SmtType}
    (h : __smtx_typeof_arith_overload_op_2 A B ≠ SmtType.None) : B ≠ SmtType.None := by
  intro hB
  subst hB
  cases A <;> simp [__smtx_typeof_arith_overload_op_2] at h

/-- A comparison against a `Real` is only typed if the other side is `Real`. -/
private theorem arith_ret_left_real {A T : SmtType}
    (h : __smtx_typeof_arith_overload_op_2_ret A SmtType.Real T ≠ SmtType.None) :
    A = SmtType.Real := by
  cases A <;> simp_all [__smtx_typeof_arith_overload_op_2_ret]

private theorem arith_ret_right_real {B T : SmtType}
    (h : __smtx_typeof_arith_overload_op_2_ret SmtType.Real B T ≠ SmtType.None) :
    B = SmtType.Real := by
  cases B <;> simp_all [__smtx_typeof_arith_overload_op_2_ret]

private theorem typeof_eq_left_real {t : SmtTerm} {u : SmtTerm}
    (hu : __smtx_typeof u = SmtType.Real)
    (h : __smtx_typeof (SmtTerm.eq t u) ≠ SmtType.None) :
    __smtx_typeof t ≠ SmtType.None := by
  rw [typeof_eq_eq, hu] at h
  intro hN
  apply h
  simp [hN, __smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]

/-- Evaluating coefficients only has a type if they are given as a list. -/
theorem eo_typeof_eq_list_of_coeffs_at_non_none (v : SmtTerm) (q : Term)
    (h : __smtx_typeof (__eo_to_smt_coeffs_at q v) ≠ SmtType.None) :
    __eo_typeof q = Term.__eo_List := by
  induction hn : sizeOf q using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    cases q with
    | __eo_List_nil => rfl
    | Apply f cs =>
        cases f with
        | Apply g c =>
            cases g with
            | __eo_List_cons =>
                cases c with
                | Rational r =>
                    have hEq :
                        __eo_to_smt_coeffs_at
                            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Rational r)) cs) v =
                          SmtTerm.plus (SmtTerm.Rational r)
                            (SmtTerm.mult v (__eo_to_smt_coeffs_at cs v)) := by
                      rw [__eo_to_smt_coeffs_at]
                    rw [hEq, typeof_plus_eq] at h
                    have hMult := arith_op2_arg_non_none h
                    rw [typeof_mult_eq] at hMult
                    have hCs := ih (sizeOf cs) (by simp at hn; omega) cs
                      (arith_op2_arg_non_none hMult) rfl
                    rw [show __eo_typeof (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Rational r)) cs) =
                      __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
                        (__eo_typeof cs) from rfl, hCs]
                    rfl
                | _ => exact False.elim (h (by simp [__eo_to_smt_coeffs_at, __smtx_typeof]))
            | _ => exact False.elim (h (by simp [__eo_to_smt_coeffs_at, __smtx_typeof]))
        | _ => exact False.elim (h (by simp [__eo_to_smt_coeffs_at, __smtx_typeof]))
    | _ => exact False.elim (h (by simp [__eo_to_smt_coeffs_at, __smtx_typeof]))

private theorem is_literal_list_tail {c cs : Term}
    (h : __eo_to_smt_is_literal_list (Term.Apply (Term.Apply Term.__eo_List_cons c) cs) = true) :
    __eo_to_smt_is_literal_list cs = true := by
  cases c <;> simp_all [__eo_to_smt_is_literal_list, native_and]

/-- What `$eo_to_smt_is_literal_list` accepts has the type of a list. -/
theorem eo_typeof_eq_list_of_is_literal_list (s : Term)
    (h : __eo_to_smt_is_literal_list s = true) :
    __eo_typeof s = Term.__eo_List := by
  induction hn : sizeOf s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    cases s with
    | __eo_List_nil => rfl
    | Apply f cs =>
        cases f with
        | Apply g c =>
            cases g with
            | __eo_List_cons =>
                have hCs := ih (sizeOf cs) (by simp at hn; omega) cs (is_literal_list_tail h) rfl
                rw [show __eo_typeof (Term.Apply (Term.Apply Term.__eo_List_cons c) cs) =
                  __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
                    (__eo_typeof cs) from rfl, hCs]
                rfl
            | _ => simp [__eo_to_smt_is_literal_list] at h
        | _ => simp [__eo_to_smt_is_literal_list] at h
    | _ => simp [__eo_to_smt_is_literal_list] at h

/-- A lower endpoint that `cov.x` can be compared against is a marker or has type `Real`. -/
private theorem eo_typeof_real_of_cov_above (l : Term)
    (ih :
      __smtx_typeof (__eo_to_smt l) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt l) = __eo_to_smt_type (__eo_typeof l))
    (h : __smtx_typeof (__eo_to_smt_cov_above l (__eo_to_smt l)) = SmtType.Bool) :
    __eo_typeof l = Term.UOp UserOp.Real := by
  by_cases hl : l = Term.UOp UserOp._at__at_cov_minus_inf
  · subst hl
    rfl
  · have hCases :
        __eo_to_smt_cov_above l (__eo_to_smt l) =
            SmtTerm.gt (SmtTerm.Var (native_string_lit "@x") SmtType.Real) (__eo_to_smt l) ∨
          __eo_to_smt_cov_above l (__eo_to_smt l) = SmtTerm.None := by
      unfold __eo_to_smt_cov_above
      split
      · exact absurd rfl hl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hCases with hEq | hEq
    · rw [hEq, typeof_gt_eq, typeof_at_x] at h
      have hNN : __smtx_typeof_arith_overload_op_2_ret SmtType.Real (__smtx_typeof (__eo_to_smt l))
          SmtType.Bool ≠ SmtType.None := by
        rw [h]; simp
      exact eo_typeof_eq_real_of_smt_real_from_ih l ih (arith_ret_right_real hNN)
    · rw [hEq] at h
      rw [__smtx_typeof.eq_def] at h <;> simp at h

/-- An upper endpoint that `cov.x` can be compared against is a marker or has type `Real`. -/
private theorem eo_typeof_real_of_cov_below (r : Term)
    (ih :
      __smtx_typeof (__eo_to_smt r) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt r) = __eo_to_smt_type (__eo_typeof r))
    (h : __smtx_typeof (__eo_to_smt_cov_below r (__eo_to_smt r)) = SmtType.Bool) :
    __eo_typeof r = Term.UOp UserOp.Real := by
  by_cases hr : r = Term.UOp UserOp._at__at_cov_plus_inf
  · subst hr
    rfl
  · have hCases :
        __eo_to_smt_cov_below r (__eo_to_smt r) =
            SmtTerm.lt (SmtTerm.Var (native_string_lit "@x") SmtType.Real) (__eo_to_smt r) ∨
          __eo_to_smt_cov_below r (__eo_to_smt r) = SmtTerm.None := by
      unfold __eo_to_smt_cov_below
      split
      · exact absurd rfl hr
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hCases with hEq | hEq
    · rw [hEq, typeof_lt_eq, typeof_at_x] at h
      have hNN : __smtx_typeof_arith_overload_op_2_ret SmtType.Real (__smtx_typeof (__eo_to_smt r))
          SmtType.Bool ≠ SmtType.None := by
        rw [h]; simp
      exact eo_typeof_eq_real_of_smt_real_from_ih r ih (arith_ret_right_real hNN)
    · rw [hEq] at h
      rw [__smtx_typeof.eq_def] at h <;> simp at h

/-- `@is_root` has a translation only where its Eunoia type is `Bool`. -/
theorem eo_to_smt_typeof_matches_translation_is_root (y x : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
          (SmtTerm.eq (__eo_to_smt_coeffs_at y (__eo_to_smt x))
            (SmtTerm.Rational (native_mk_rational 0 1)))
          SmtTerm.None := by
    rfl
  rw [hTranslate] at hNonNone ⊢
  by_cases hR : __smtx_typeof (__eo_to_smt x) = SmtType.Real
  · have hIte :
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
            (SmtTerm.eq (__eo_to_smt_coeffs_at y (__eo_to_smt x))
              (SmtTerm.Rational (native_mk_rational 0 1)))
            SmtTerm.None =
          SmtTerm.eq (__eo_to_smt_coeffs_at y (__eo_to_smt x))
            (SmtTerm.Rational (native_mk_rational 0 1)) := by
      simp [native_ite, native_Teq, hR]
    rw [hIte] at hNonNone ⊢
    have hCoeffsNN := typeof_eq_left_real typeof_cov_zero hNonNone
    have hY := eo_typeof_eq_list_of_coeffs_at_non_none _ y hCoeffsNN
    have hXR := eo_typeof_eq_real_of_smt_real_from_ih x ihX hR
    have hEo :
        __eo_typeof (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x) = Term.Bool := by
      rw [show __eo_typeof (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x) =
        __eo_typeof__at_is_root (__eo_typeof y) (__eo_typeof x) from rfl, hY, hXR]
      rfl
    rw [hEo, eo_to_smt_type_bool, typeof_eq_eq, typeof_cov_zero]
    rw [typeof_eq_eq, typeof_cov_zero] at hNonNone
    cases hC : __smtx_typeof (__eo_to_smt_coeffs_at y (__eo_to_smt x)) <;>
      simp_all [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  · exact False.elim (hNonNone (by
      have hIte :
          native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
              (SmtTerm.eq (__eo_to_smt_coeffs_at y (__eo_to_smt x))
                (SmtTerm.Rational (native_mk_rational 0 1)))
              SmtTerm.None = SmtTerm.None := by
        simp [native_ite, native_Teq, hR]
      rw [hIte]
      rw [__smtx_typeof.eq_def] <;> simp only))

/-- `@sgn_inv` has a translation only where its Eunoia type is `Bool`. -/
theorem eo_to_smt_typeof_matches_translation_sgn_inv (z y x : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv z) y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv z) y) x)) =
      __eo_to_smt_type (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv z) y) x) =
        SmtTerm.or
          (__eo_to_smt_cov_throughout
            (SmtTerm.and (__eo_to_smt_cov_above y (__eo_to_smt y))
              (__eo_to_smt_cov_below x (__eo_to_smt x)))
            (SmtTerm.gt (__eo_to_smt_coeffs_at z (SmtTerm.Var (native_string_lit "@x") SmtType.Real))
              (SmtTerm.Rational (native_mk_rational 0 1))))
          (SmtTerm.or
            (__eo_to_smt_cov_throughout
              (SmtTerm.and (__eo_to_smt_cov_above y (__eo_to_smt y))
                (__eo_to_smt_cov_below x (__eo_to_smt x)))
              (SmtTerm.lt (__eo_to_smt_coeffs_at z (SmtTerm.Var (native_string_lit "@x") SmtType.Real))
                (SmtTerm.Rational (native_mk_rational 0 1))))
            (__eo_to_smt_cov_throughout
              (SmtTerm.and (__eo_to_smt_cov_above y (__eo_to_smt y))
                (__eo_to_smt_cov_below x (__eo_to_smt x)))
              (SmtTerm.eq (__eo_to_smt_coeffs_at z (SmtTerm.Var (native_string_lit "@x") SmtType.Real))
                (SmtTerm.Rational (native_mk_rational 0 1))))) := by
    rfl
  rw [hTranslate] at hNonNone ⊢
  have hOr := typeof_or_parts hNonNone
  have hFirst := hOr.1
  -- The first disjunct says everything the Eunoia type asks for.
  simp only [__eo_to_smt_cov_throughout] at hFirst
  have hEx := typeof_not_part (non_none_of_bool hFirst)
  have hBody := typeof_exists_part (non_none_of_bool hEx)
  have hBodyParts := typeof_and_parts (non_none_of_bool hBody)
  have hI := typeof_and_parts (non_none_of_bool hBodyParts.1)
  have hGt := typeof_not_part (non_none_of_bool hBodyParts.2)
  rw [typeof_gt_eq, typeof_cov_zero] at hGt
  have hV := arith_ret_left_real (non_none_of_bool hGt)
  have hZ : __eo_typeof z = Term.__eo_List :=
    eo_typeof_eq_list_of_coeffs_at_non_none _ z (by rw [hV]; simp)
  have hYReal := eo_typeof_real_of_cov_above y ihY hI.1
  have hXReal := eo_typeof_real_of_cov_below x ihX hI.2
  have hEo :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv z) y) x) =
        Term.Bool := by
    rw [show __eo_typeof (Term.Apply (Term.Apply (Term.UOp1 UserOp1._at_sgn_inv z) y) x) =
      __eo_typeof__at_sgn_inv (__eo_typeof z) (__eo_typeof y) (__eo_typeof x) from rfl,
      hZ, hYReal, hXReal]
    rfl
  have hRest := typeof_or_parts (non_none_of_bool hOr.2)
  rw [hEo, eo_to_smt_type_bool, typeof_or_eq, hOr.1, hOr.2]
  simp [native_ite, native_Teq]

/-- `@ran` either has no meaning, or its bounds are rational and its evidence is literal. -/
theorem eo_to_smt_ran_cases (q lo hi s : Term) :
    __eo_to_smt (Term.UOp4 UserOp4._at_ran q lo hi s) = SmtTerm.None ∨
      ∃ rl rh, lo = Term.Rational rl ∧ hi = Term.Rational rh ∧
        __eo_to_smt_is_literal_list s = true ∧
        __eo_to_smt (Term.UOp4 UserOp4._at_ran q lo hi s) =
          SmtTerm.choice (native_string_lit "@x") SmtType.Real
            (SmtTerm.and
              (SmtTerm.eq
                (__eo_to_smt_coeffs_at q (SmtTerm.Var (native_string_lit "@x") SmtType.Real))
                (SmtTerm.Rational (native_mk_rational 0 1)))
              (SmtTerm.and
                (SmtTerm.lt (SmtTerm.Rational rl)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Real))
                (SmtTerm.lt (SmtTerm.Var (native_string_lit "@x") SmtType.Real)
                  (SmtTerm.Rational rh)))) := by
  change __eo_to_smt_ran q lo hi s = SmtTerm.None ∨ _
  cases lo with
  | Rational rl =>
      cases hi with
      | Rational rh =>
          cases hS : __eo_to_smt_is_literal_list s
          · left
            simp [__eo_to_smt_ran, hS, native_ite]
          · right
            exact ⟨rl, rh, rfl, rfl, hS, by
              change __eo_to_smt_ran q _ _ s = _
              simp [__eo_to_smt_ran, hS, native_ite]⟩
      | _ => left; simp [__eo_to_smt_ran]
  | _ => left; simp [__eo_to_smt_ran]

/-- `@ran` has a translation only where its Eunoia type is `Real`. -/
theorem eo_to_smt_typeof_matches_translation_ran (q lo hi s : Term)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.UOp4 UserOp4._at_ran q lo hi s)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.UOp4 UserOp4._at_ran q lo hi s)) =
      __eo_to_smt_type (__eo_typeof (Term.UOp4 UserOp4._at_ran q lo hi s)) := by
  rcases eo_to_smt_ran_cases q lo hi s with h | ⟨rl, rh, rfl, rfl, hS, h⟩
  · rw [h] at hNonNone
    exact False.elim (hNonNone (by rw [__smtx_typeof.eq_def] <;> simp only))
  · rw [h] at hNonNone ⊢
    rw [typeof_choice_eq'] at hNonNone ⊢
    have hF := native_ite_bool_of_non_none hNonNone
    have hParts := typeof_and_parts (non_none_of_bool hF)
    have hCoeffsNN := typeof_eq_left_real typeof_cov_zero (non_none_of_bool hParts.1)
    have hQEo := eo_typeof_eq_list_of_coeffs_at_non_none _ q hCoeffsNN
    have hSEo := eo_typeof_eq_list_of_is_literal_list s hS
    have hEo :
        __eo_typeof (Term.UOp4 UserOp4._at_ran q (Term.Rational rl) (Term.Rational rh) s) =
          Term.UOp UserOp.Real := by
      rw [show __eo_typeof (Term.UOp4 UserOp4._at_ran q (Term.Rational rl) (Term.Rational rh) s) =
        __eo_typeof__at_ran (__eo_typeof q) (__eo_typeof (Term.Rational rl))
          (__eo_typeof (Term.Rational rh)) (__eo_typeof s) from rfl, hQEo, hSEo]
      rfl
    rw [hEo, eo_to_smt_type_real, hF]
    simp [native_ite, native_Teq, __smtx_typeof_guard_wf, __smtx_type_wf,
      __smtx_type_wf_component, __smtx_type_wf_rec, native_and]

/-- A `choice` over `Real` is never of a function type. -/
theorem typeof_choice_real_cases (s : native_String) (F : SmtTerm) :
    __smtx_typeof (SmtTerm.choice s SmtType.Real F) = SmtType.Real ∨
      __smtx_typeof (SmtTerm.choice s SmtType.Real F) = SmtType.None := by
  rw [typeof_choice_eq']
  by_cases hF : __smtx_typeof F = SmtType.Bool
  · left
    simp [hF, native_ite, native_Teq, __smtx_typeof_guard_wf, __smtx_type_wf,
      __smtx_type_wf_component, __smtx_type_wf_rec, native_and]
  · right
    simp [hF, native_ite, native_Teq]

/-- What `@ran` translates to, as far as applying it as a head is concerned. -/
theorem eo_to_smt_ran_head_cases (q lo hi s : Term) :
    __eo_to_smt (Term.UOp4 UserOp4._at_ran q lo hi s) = SmtTerm.None ∨
      ∃ F, __eo_to_smt (Term.UOp4 UserOp4._at_ran q lo hi s) =
        SmtTerm.choice (native_string_lit "@x") SmtType.Real F := by
  rcases eo_to_smt_ran_cases q lo hi s with h | ⟨_, _, _, _, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

/-- What `@is_root` translates to, as far as its head is concerned. -/
theorem eo_to_smt_is_root_cases (y x : Term) :
    __eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x) = SmtTerm.None ∨
      ∃ a b, __eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x) = SmtTerm.eq a b := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_is_root y) x) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
          (SmtTerm.eq (__eo_to_smt_coeffs_at y (__eo_to_smt x))
            (SmtTerm.Rational (native_mk_rational 0 1)))
          SmtTerm.None := by
    rfl
  rw [hTranslate]
  cases native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, rfl⟩

theorem false_of_typeof_at_is_root_eq_dtcapp {a b A B : Term}
    (h : __eo_typeof__at_is_root a b = Term.DtcAppType A B) : False := by
  unfold __eo_typeof__at_is_root at h
  split at h <;> cases h

theorem false_of_typeof_at_sgn_inv_eq_dtcapp {a b c A B : Term}
    (h : __eo_typeof__at_sgn_inv a b c = Term.DtcAppType A B) : False := by
  unfold __eo_typeof__at_sgn_inv at h
  split at h <;> cases h

/-- The type of `@ran` is `Real` or stuck. -/
theorem eo_typeof_at_ran_cases (a b c d : Term) :
    __eo_typeof__at_ran a b c d = Term.UOp UserOp.Real ∨
      __eo_typeof__at_ran a b c d = Term.Stuck := by
  unfold __eo_typeof__at_ran
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `@ran` is never of a function type, so applying it is stuck. -/
theorem eo_typeof_apply_at_ran (a b c d t : Term) :
    __eo_typeof_apply (__eo_typeof__at_ran a b c d) t = Term.Stuck := by
  rcases eo_typeof_at_ran_cases a b c d with h | h <;> rw [h] <;> cases t <;> rfl

theorem eo_typeof_apply_stuck (t : Term) : __eo_typeof_apply Term.Stuck t = Term.Stuck := by
  cases t <;> rfl

/-- `@is_root` is never of a function type, so applying it is stuck. -/
theorem eo_typeof_apply_at_is_root (a b t : Term) :
    __eo_typeof_apply (__eo_typeof__at_is_root a b) t = Term.Stuck := by
  unfold __eo_typeof__at_is_root
  split <;> cases t <;> rfl

end TranslationProofs
