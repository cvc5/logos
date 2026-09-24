module

public import Cpc.Proofs.RuleSupport.BvNegoEliminateSupport
import all Cpc.Proofs.RuleSupport.BvNegoEliminateSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def bvSdivoPremMin (x wm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) wm)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x))
      (Term.Numeral 1))

private def bvSdivoPremWidth (y w : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) w)
    (Term.Apply (Term.UOp UserOp._at_bvsize) y)

private def bvSdivoDivisor (w : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot)
    (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))

private def bvSdivoRhs (x y w wm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) (bvNegoMin wm)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) (bvSdivoDivisor w)))
      (Term.Boolean true))

private def bvSdivoTerm (x y w wm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y))
    (bvSdivoRhs x y w wm)

private theorem eo_and_eq_true_left {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true := by
  intro h
  exact (RuleProofs.eo_and_eq_true_args x y h).1

private theorem eo_and_eq_true_right {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    y = Term.Boolean true := by
  intro h
  exact (RuleProofs.eo_and_eq_true_args x y h).2

private theorem prog_bv_sdivo_eliminate_eq_of_ne_stuck
    (x y w wm : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    wm ≠ Term.Stuck ->
    __eo_prog_bv_sdivo_eliminate x y w wm
        (Proof.pf (bvSdivoPremMin x wm))
        (Proof.pf (bvSdivoPremWidth y w)) =
      bvSdivoTerm x y w wm := by
  intro hX hY hW hWm
  unfold bvSdivoPremMin bvSdivoPremWidth
  rw [__eo_prog_bv_sdivo_eliminate.eq_5 x y w wm wm x w y
    hX hY hW hWm]
  unfold bvSdivoTerm bvSdivoRhs bvSdivoDivisor bvNegoMin
  simp [__eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and, hX, hY, hW, hWm]

private theorem bv_sdivo_shape_of_ne_stuck
    (x y w wm P1 P2 : Term) :
    __eo_prog_bv_sdivo_eliminate x y w wm (Proof.pf P1) (Proof.pf P2) ≠
      Term.Stuck ->
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
      wm ≠ Term.Stuck ∧
      ∃ px pwm py pw,
        P1 = bvSdivoPremMin px pwm ∧
        P2 = bvSdivoPremWidth py pw := by
  intro hProg
  have hx : x ≠ Term.Stuck := by
    intro hx
    subst x
    exact hProg (__eo_prog_bv_sdivo_eliminate.eq_1 y w wm
      (Proof.pf P1) (Proof.pf P2))
  have hy : y ≠ Term.Stuck := by
    intro hy
    subst y
    exact hProg (__eo_prog_bv_sdivo_eliminate.eq_2 x w wm
      (Proof.pf P1) (Proof.pf P2) hx)
  have hw : w ≠ Term.Stuck := by
    intro hw
    subst w
    exact hProg (__eo_prog_bv_sdivo_eliminate.eq_3 x y wm
      (Proof.pf P1) (Proof.pf P2) hx hy)
  have hwm : wm ≠ Term.Stuck := by
    intro hwm
    subst wm
    exact hProg (__eo_prog_bv_sdivo_eliminate.eq_4 x y w
      (Proof.pf P1) (Proof.pf P2) hx hy hw)
  by_cases hShape :
      ∃ pwm px pw py,
        P1 = bvSdivoPremMin px pwm ∧
        P2 = bvSdivoPremWidth py pw
  · rcases hShape with ⟨pwm, px, pw, py, hP1, hP2⟩
    exact ⟨hx, hy, hw, hwm, px, pwm, py, pw, hP1, hP2⟩
  · have hStuck :
        __eo_prog_bv_sdivo_eliminate x y w wm (Proof.pf P1) (Proof.pf P2) =
          Term.Stuck := by
      exact __eo_prog_bv_sdivo_eliminate.eq_6 x y w wm
        (Proof.pf P1) (Proof.pf P2) hx hy hw hwm (by
          intro pwm px pw py hp1 hp2
          cases hp1
          cases hp2
          exact hShape ⟨pwm, px, pw, py, rfl, rfl⟩)
    exact False.elim (hProg hStuck)

private theorem eo_typeof_bvult_args_of_ne_stuck {A B : Term}
    (h : __eo_typeof_bvult A B ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) w ∧ w ≠ Term.Stuck := by
  exact RuleProofs.eo_typeof_bvult_args_of_ne_stuck A B h

private theorem eo_typeof_or_bool_args (A B : Term) :
    __eo_typeof_or A B = Term.Bool -> A = Term.Bool ∧ B = Term.Bool := by
  intro h
  exact RuleProofs.eo_typeof_or_bool_args A B h

private theorem bv_sdivo_divisor_type_inv (w width : Term) :
    __eo_typeof (bvSdivoDivisor w) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    ∃ i, w = Term.Numeral i ∧ native_zleq 0 i = true ∧
      width = Term.Numeral i := by
  intro hDivTy
  unfold bvSdivoDivisor at hDivTy
  change __eo_typeof_bvnot
      (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))) =
    Term.Apply (Term.UOp UserOp.BitVec) width at hDivTy
  have hAtTy :
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0)) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
    cases hAt : __eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0)) <;>
      simp [__eo_typeof_bvnot, hAt] at hDivTy
    case Apply f m =>
      cases f <;> try simp [__eo_typeof_bvnot, hAt] at hDivTy
      case UOp op =>
        cases op <;> simp [__eo_typeof_bvnot, hAt] at hDivTy
        case BitVec =>
          cases hDivTy
          rfl
  change __eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int) =
    Term.Apply (Term.UOp UserOp.BitVec) width at hAtTy
  have hWNe : w ≠ Term.Stuck := by
    intro hW
    subst w
    simp [__eo_typeof_int_to_bv] at hAtTy
  have hWTy : __eo_typeof w = Term.UOp UserOp.Int := by
    cases hTy : __eo_typeof w <;>
      simp [__eo_typeof_int_to_bv, hWNe, hTy] at hAtTy ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_int_to_bv, hWNe, hTy] at hAtTy ⊢
  exact at_bv_type_bitvec_inv w width hWNe hWTy hAtTy

private theorem smtx_typeof_bvsdivo_term_eq (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvsdivo x y) =
      __smtx_typeof_bv_op_2_ret (__smtx_typeof x) (__smtx_typeof y)
        SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smt_typeof_bvsdivo (x y : SmtTerm) (n : Nat) :
    __smtx_typeof x = SmtType.BitVec n ->
    __smtx_typeof y = SmtType.BitVec n ->
    __smtx_typeof (SmtTerm.bvsdivo x y) = SmtType.Bool := by
  intro hX hY
  rw [smtx_typeof_bvsdivo_term_eq]
  simp [__smtx_typeof_bv_op_2_ret, hX, hY, native_nateq, native_ite]

private theorem smt_typeof_bv_sdivo_divisor (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof
        (__eo_to_smt (bvSdivoDivisor (Term.Numeral w))) =
      SmtType.BitVec (native_int_to_nat w) := by
  intro hW
  unfold bvSdivoDivisor
  change __smtx_typeof
      (SmtTerm.bvnot
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral w)) (Term.Numeral 0)))) =
    SmtType.BitVec (native_int_to_nat w)
  rw [smtx_typeof_bvnot_term_eq]
  have hConst := smt_typeof_bv_const 0 w hW
  simp [__smtx_typeof_bv_op_1, hConst]

private theorem smtx_eval_bvsdivo_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvsdivo x y) =
      __smtx_model_eval_bvsdivo
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvnego_term_eq_local
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvnego x) =
      __smtx_model_eval_bvnego (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_sdivo_divisor
    (M : SmtModel) (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_model_eval M
        (__eo_to_smt (bvSdivoDivisor (Term.Numeral w))) =
      __smtx_model_eval_bvnot (SmtValue.Binary w 0) := by
  intro hW
  unfold bvSdivoDivisor
  change __smtx_model_eval M
      (SmtTerm.bvnot
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral w)) (Term.Numeral 0)))) =
    __smtx_model_eval_bvnot (SmtValue.Binary w 0)
  rw [smtx_eval_bvnot_term_eq, eval_bv_const M 0 w hW]
  rw [native_mod_zero_pow2 hW]

private theorem bv_sdivo_context
    (x y w wm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSdivoTerm x y w wm) = Term.Bool ->
    ∃ n,
      native_zleq 0 n = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ∧
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat n) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat n) ∧
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
          (bvNegoMin wm)) = Term.Bool ∧
      __eo_typeof (bvNegoTerm x wm) = Term.Bool ∧
      ∃ i,
        w = Term.Numeral i ∧ native_zleq 0 i = true ∧
        i = n := by
  intro hXTrans hYTrans hResultTy
  have hOperandsNN :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y))
      (__eo_typeof (bvSdivoRhs x y w wm))
      (by exact hResultTy)
  have hLeftNN :
      __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    exact hOperandsNN.1
  rcases eo_typeof_bvult_args_of_ne_stuck hLeftNN with
    ⟨width, hXTy, hYTy, hWidthNe⟩
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y) =
        Term.Bool := by
    change __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool
    rw [hXTy, hYTy]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hWidthNe]
  have hTypeEq :=
    RuleProofs.eo_typeof_eq_bool_operands_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y))
      (__eo_typeof (bvSdivoRhs x y w wm))
      (by exact hResultTy)
  have hRightTy : __eo_typeof (bvSdivoRhs x y w wm) = Term.Bool := by
    rw [← hTypeEq]
    exact hLeftTy
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x width hXTrans hXTy with
    ⟨n, hWidth, hNonneg, hXSmtTy⟩
  subst width
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y (Term.Numeral n)
      hYTrans (by simpa using hYTy) with
    ⟨m, hMWidth, _hMNonneg, hYSmtTy⟩
  cases hMWidth
  have hOuterAnd :
      __eo_typeof_or
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) (bvNegoMin wm)))
        (__eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y)
                (bvSdivoDivisor w)))
            (Term.Boolean true))) = Term.Bool := by
    exact hRightTy
  rcases eo_typeof_or_bool_args _ _ hOuterAnd with ⟨hEqXMinBool, hInnerAndBool⟩
  have hInnerAnd :
      __eo_typeof_or
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y)
            (bvSdivoDivisor w)))
        (__eo_typeof (Term.Boolean true)) = Term.Bool := by
    exact hInnerAndBool
  rcases eo_typeof_or_bool_args _ _ hInnerAnd with ⟨hEqYDivBool, _hTrueBool⟩
  have hBvNegoTermTy : __eo_typeof (bvNegoTerm x wm) = Term.Bool := by
    unfold bvNegoTerm
    change __eo_typeof_eq (__eo_typeof_bvnego (__eo_typeof x))
      (__eo_typeof_eq (__eo_typeof x) (__eo_typeof (bvNegoMin wm))) =
        Term.Bool
    have hEqXMinBool' :
        __eo_typeof_eq (__eo_typeof x) (__eo_typeof (bvNegoMin wm)) =
          Term.Bool := by
      exact hEqXMinBool
    rw [hEqXMinBool', hXTy]
    simp [__eo_typeof_bvnego, __eo_typeof_eq, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not]
  have hYDivTypes :=
    RuleProofs.eo_typeof_eq_bool_operands_eq
      (__eo_typeof y) (__eo_typeof (bvSdivoDivisor w)) hEqYDivBool
  have hDivTy :
      __eo_typeof (bvSdivoDivisor w) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
    rw [← hYDivTypes]
    simpa using hYTy
  rcases bv_sdivo_divisor_type_inv w (Term.Numeral n) hDivTy with
    ⟨i, hW, hINonneg, hWidthI⟩
  have hIWidth : i = n := by
    cases hWidthI
    rfl
  exact ⟨n, hNonneg, hXTy, by simpa using hYTy, hXSmtTy, hYSmtTy,
    hEqXMinBool, hBvNegoTermTy, i, hW, hINonneg, hIWidth⟩

private theorem typed_bv_sdivo_term (x y w wm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSdivoTerm x y w wm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSdivoTerm x y w wm) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_sdivo_context x y w wm hXTrans hYTrans hResultTy with
    ⟨n, _hNonneg, _hXTy, _hYTy, hXSmtTy, hYSmtTy, hEqXMinBool,
      hBvNegoTermTy, i, hW, hINonneg, hIWidth⟩
  subst w
  subst i
  have hLhsBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y) := by
    change __smtx_typeof (SmtTerm.bvsdivo (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.Bool
    exact smt_typeof_bvsdivo (__eo_to_smt x) (__eo_to_smt y)
      (native_int_to_nat n) hXSmtTy hYSmtTy
  have hEqXMinSmt : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) (bvNegoMin wm)) := by
    rcases typeof_args_of_bv_nego_term_bool x wm hXTrans hBvNegoTermTy with
      ⟨j, hWm, hJNonneg, _hXTyJ, hXSmtTyJ⟩
    subst wm
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x
      (bvNegoMin (Term.Numeral j))
      (by
        rw [hXSmtTyJ, smt_typeof_bv_nego_min j hJNonneg])
      (by
        rw [hXSmtTyJ]
        intro h
        cases h)
  have hDivTy := smt_typeof_bv_sdivo_divisor n hINonneg
  have hEqYDivBoolSmt : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y)
        (bvSdivoDivisor (Term.Numeral n))) := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type y
      (bvSdivoDivisor (Term.Numeral n))
      (by
        rw [hYSmtTy, hDivTy])
      (by
        rw [hYSmtTy]
        intro h
        cases h)
  have hInnerBool : RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y)
            (bvSdivoDivisor (Term.Numeral n))))
        (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hEqYDivBoolSmt RuleProofs.eo_has_bool_type_true
  have hRhsBool : RuleProofs.eo_has_bool_type
      (bvSdivoRhs x y (Term.Numeral n) wm) := by
    unfold bvSdivoRhs
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hEqXMinSmt hInnerBool
  unfold bvSdivoTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y)
    (bvSdivoRhs x y (Term.Numeral n) wm)
    (by rw [hLhsBool, hRhsBool])
    (by
      rw [hLhsBool]
      intro h
      cases h)

private theorem eval_bv_sdivo_term
    (M : SmtModel) (hM : model_wf M) (x y w wm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSdivoTerm x y w wm) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y)) =
      __smtx_model_eval M (__eo_to_smt (bvSdivoRhs x y w wm)) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_sdivo_context x y w wm hXTrans hYTrans hResultTy with
    ⟨n, hNonneg, _hXTy, _hYTy, hXSmtTy, _hYSmtTy, _hEqXMinBool,
      hBvNegoTermTy, i, hW, hINonneg, hIWidth⟩
  subst w
  subst i
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by
          simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
            using hXTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX⟩
  have hRound :
      native_nat_to_int (native_int_to_nat n) = n :=
    native_nat_to_int_int_to_nat_eq n hNonneg
  rw [hRound] at hEvalX
  have hSize :
      __smtx_bv_sizeof_value (__smtx_model_eval M (__eo_to_smt x)) = n := by
    rw [hEvalX]
    rfl
  have hNegoEval :=
    eval_bvnego_matches_eq_min M hM x wm hXTrans hBvNegoTermTy
  have hNegoEval' :
      __smtx_model_eval_bvnego (__smtx_model_eval M (__eo_to_smt x)) =
        __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt (bvNegoMin wm))) := by
    change __smtx_model_eval M (SmtTerm.bvnego (__eo_to_smt x)) =
      __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (bvNegoMin wm))) at hNegoEval
    rw [smtx_eval_bvnego_term_eq_local, smtx_eval_eq_term_eq] at hNegoEval
    exact hNegoEval
  have hDivEval := eval_bv_sdivo_divisor M n hINonneg
  unfold bvSdivoRhs
  change __smtx_model_eval M (SmtTerm.bvsdivo (__eo_to_smt x) (__eo_to_smt y)) =
    __smtx_model_eval M
      (SmtTerm.and
        (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (bvNegoMin wm)))
        (SmtTerm.and
          (SmtTerm.eq (__eo_to_smt y)
            (__eo_to_smt (bvSdivoDivisor (Term.Numeral n))))
          (SmtTerm.Boolean true)))
  rw [smtx_eval_bvsdivo_term_eq, smtx_eval_and_term_eq,
    smtx_eval_and_term_eq, smtx_eval_eq_term_eq, smtx_eval_eq_term_eq,
    hDivEval]
  change __smtx_model_eval_and
      (__smtx_model_eval_bvnego (__smtx_model_eval M (__eo_to_smt x)))
      (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval_bvnot
          (SmtValue.Binary
            (__smtx_bv_sizeof_value
              (__smtx_model_eval M (__eo_to_smt x))) 0))) =
    __smtx_model_eval_and
      (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt (bvNegoMin wm))))
      (__smtx_model_eval_and
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt y))
          (__smtx_model_eval_bvnot (SmtValue.Binary n 0)))
        (__smtx_model_eval M (SmtTerm.Boolean true)))
  rw [hSize, hNegoEval']
  cases hEq :
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval_bvnot (SmtValue.Binary n 0)) <;>
    simp [__smtx_model_eval, __smtx_model_eval_and, __smtx_model_eval_eq,
      SmtEval.native_and, native_and] at hEq ⊢

private theorem facts_bv_sdivo_term
    (M : SmtModel) (hM : model_wf M) (x y w wm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSdivoTerm x y w wm) = Term.Bool ->
    eo_interprets M (bvSdivoTerm x y w wm) true := by
  intro hXTrans hYTrans hResultTy
  have hBool := typed_bv_sdivo_term x y w wm hXTrans hYTrans hResultTy
  unfold bvSdivoTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSdivoTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y)))
      (__smtx_model_eval M (__eo_to_smt (bvSdivoRhs x y w wm)))
    rw [eval_bv_sdivo_term M hM x y w wm hXTrans hYTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_sdivo_eliminate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sdivo_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_sdivo_eliminate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sdivo_eliminate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_sdivo_eliminate args premises ≠
      Term.Stuck :=
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
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
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
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons n2 premises =>
                              cases premises with
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | nil =>
                                  let P1 := __eo_state_proven_nth s n1
                                  let P2 := __eo_state_proven_nth s n2
                                  change
                                    StepRuleProperties M [P1, P2]
                                      (__eo_prog_bv_sdivo_eliminate a1 a2 a3 a4
                                        (Proof.pf P1) (Proof.pf P2))
                                  have hProgLocal :
                                      __eo_prog_bv_sdivo_eliminate a1 a2 a3 a4
                                          (Proof.pf P1) (Proof.pf P2) ≠
                                        Term.Stuck := by
                                    exact hProg
                                  rcases bv_sdivo_shape_of_ne_stuck a1 a2 a3 a4
                                      P1 P2 hProgLocal with
                                    ⟨hA1Ne, hA2Ne, hA3Ne, hA4Ne, px, pwm,
                                      py, pw, hP1, hP2⟩
                                  have hReqNe :
                                      __eo_requires
                                          (__eo_and
                                            (__eo_and
                                              (__eo_and (__eo_eq a4 pwm)
                                                (__eo_eq a1 px))
                                              (__eo_eq a3 pw))
                                            (__eo_eq a2 py))
                                          (Term.Boolean true)
                                          (bvSdivoTerm a1 a2 a3 a4) ≠
                                        Term.Stuck := by
                                    have h := hProgLocal
                                    rw [hP1, hP2] at h
                                    simpa [bvSdivoPremMin, bvSdivoPremWidth,
                                      bvSdivoTerm, bvSdivoRhs, bvSdivoDivisor,
                                      bvNegoMin, __eo_prog_bv_sdivo_eliminate,
                                      hA1Ne, hA2Ne, hA3Ne, hA4Ne] using h
                                  have hReqCond :
                                      __eo_and
                                          (__eo_and
                                            (__eo_and (__eo_eq a4 pwm)
                                              (__eo_eq a1 px))
                                            (__eo_eq a3 pw))
                                          (__eo_eq a2 py) =
                                        Term.Boolean true :=
                                    support_eo_requires_cond_eq_of_non_stuck
                                      hReqNe
                                  have hEqA4 : pwm = a4 := by
                                    have hAnd1 :
                                        __eo_eq a4 pwm = Term.Boolean true := by
                                      have hLeft := eo_and_eq_true_left hReqCond
                                      have hLeft2 := eo_and_eq_true_left hLeft
                                      exact eo_and_eq_true_left hLeft2
                                    exact RuleProofs.eq_of_eo_eq_true a4 pwm hAnd1
                                  have hEqA1 : px = a1 := by
                                    have hAnd1 :
                                        __eo_eq a1 px = Term.Boolean true := by
                                      have hLeft := eo_and_eq_true_left hReqCond
                                      have hLeft2 := eo_and_eq_true_left hLeft
                                      exact eo_and_eq_true_right hLeft2
                                    exact RuleProofs.eq_of_eo_eq_true a1 px hAnd1
                                  have hEqA3 : pw = a3 := by
                                    have hAnd1 :
                                        __eo_eq a3 pw = Term.Boolean true := by
                                      have hLeft := eo_and_eq_true_left hReqCond
                                      exact eo_and_eq_true_right hLeft
                                    exact RuleProofs.eq_of_eo_eq_true a3 pw hAnd1
                                  have hEqA2 : py = a2 := by
                                    have hAnd1 :
                                        __eo_eq a2 py = Term.Boolean true :=
                                      eo_and_eq_true_right hReqCond
                                    exact RuleProofs.eq_of_eo_eq_true a2 py hAnd1
                                  subst pwm
                                  subst px
                                  subst pw
                                  subst py
                                  have hATrans :
                                      RuleProofs.eo_has_smt_translation a1 ∧
                                        RuleProofs.eo_has_smt_translation a2 ∧
                                        RuleProofs.eo_has_smt_translation a3 ∧
                                        RuleProofs.eo_has_smt_translation a4 ∧ True := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk]
                                      using hCmdTrans
                                  have hA1Trans := hATrans.1
                                  have hA2Trans := hATrans.2.1
                                  have hResultTyCanonical :
                                      __eo_typeof (bvSdivoTerm a1 a2 a3 a4) =
                                        Term.Bool := by
                                    have h := hResultTy
                                    change __eo_typeof
                                        (__eo_prog_bv_sdivo_eliminate a1 a2 a3 a4
                                          (Proof.pf (__eo_state_proven_nth s n1))
                                          (Proof.pf (__eo_state_proven_nth s n2))) =
                                      Term.Bool at h
                                    simpa [P1, P2, hP1, hP2,
                                      prog_bv_sdivo_eliminate_eq_of_ne_stuck
                                        a1 a2 a3 a4 hA1Ne hA2Ne hA3Ne hA4Ne]
                                      using h
                                  refine ⟨?_, ?_⟩
                                  · intro _hPremises
                                    change eo_interprets M
                                      (__eo_prog_bv_sdivo_eliminate a1 a2 a3 a4
                                        (Proof.pf P1) (Proof.pf P2)) true
                                    rw [hP1, hP2,
                                      prog_bv_sdivo_eliminate_eq_of_ne_stuck
                                        a1 a2 a3 a4 hA1Ne hA2Ne hA3Ne hA4Ne]
                                    exact facts_bv_sdivo_term M hM a1 a2 a3 a4
                                      hA1Trans hA2Trans hResultTyCanonical
                                  · rw [hP1, hP2,
                                      prog_bv_sdivo_eliminate_eq_of_ne_stuck
                                        a1 a2 a3 a4 hA1Ne hA2Ne hA3Ne hA4Ne]
                                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                      (typed_bv_sdivo_term a1 a2 a3 a4
                                        hA1Trans hA2Trans hResultTyCanonical)
