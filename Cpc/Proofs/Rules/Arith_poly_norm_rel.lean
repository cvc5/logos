module

public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_arith_poly_norm_rel_eq_arg_of_typeof_bool_shape
    (r x1 x2 r2 y1 y2 cx x one cy y one2 : Term) :
  __eo_typeof
      (__eo_prog_arith_poly_norm_rel
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply r x1) x2))
          (Term.Apply (Term.Apply r2 y1) y2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one2))))) = Term.Bool ->
  __eo_prog_arith_poly_norm_rel
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply r x1) x2))
        (Term.Apply (Term.Apply r2 y1) y2))
      (Proof.pf
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one2)))) =
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply r x1) x2))
      (Term.Apply (Term.Apply r2 y1) y2)) := by
  intro hTy
  have hProg :
      __eo_prog_arith_poly_norm_rel
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply r x1) x2))
          (Term.Apply (Term.Apply r2 y1) y2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one2)))) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  let guardSame := __eo_and (__eo_eq r r2) (__eo_eq one one2)
  let restOne :=
    __eo_requires (__eo_to_q one) (Term.Rational (native_mk_rational 1 1))
      (__eo_requires (__is_poly_norm_rel_consts (Term.Apply (Term.Apply r cx) cy))
        (Term.Boolean true)
        (__eo_requires
          (__is_eq_maybe_to_real x (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))
          (Term.Boolean true)
          (__eo_requires
            (__is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2))
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply r x1) x2))
              (Term.Apply (Term.Apply r y1) y2)))))
  have hOuter :
      __eo_requires guardSame (Term.Boolean true) restOne ≠ Term.Stuck := by
    simpa [__eo_prog_arith_poly_norm_rel, guardSame, restOne] using hProg
  have hGuardSame : guardSame = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hOuter
  have hRestOne : restOne ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hOuter
  have hSameParts := eo_and_true hGuardSame
  have hr : r = r2 := eo_eq_true_eq hSameParts.1
  subst r2
  have hOne :
      __eo_to_q one = Term.Rational (native_mk_rational 1 1) :=
    eo_requires_arg_eq_of_ne_stuck hRestOne
  have hRestConsts :
      __eo_requires (__is_poly_norm_rel_consts (Term.Apply (Term.Apply r cx) cy))
        (Term.Boolean true)
        (__eo_requires
          (__is_eq_maybe_to_real x (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))
          (Term.Boolean true)
          (__eo_requires
            (__is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2))
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply r x1) x2))
              (Term.Apply (Term.Apply r y1) y2)))) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestOne
  have hConsts :
      __is_poly_norm_rel_consts (Term.Apply (Term.Apply r cx) cy) = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hRestConsts
  have hRestX :
      __eo_requires
          (__is_eq_maybe_to_real x (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))
          (Term.Boolean true)
          (__eo_requires
            (__is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2))
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply r x1) x2))
              (Term.Apply (Term.Apply r y1) y2))) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestConsts
  have hX :
      __is_eq_maybe_to_real x (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2) =
        Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hRestX
  have hRestY :
      __eo_requires
            (__is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2))
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply r x1) x2))
              (Term.Apply (Term.Apply r y1) y2)) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestX
  have hY :
      __is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2) =
        Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hRestY
  simp [__eo_prog_arith_poly_norm_rel, __eo_requires, guardSame, hGuardSame, hOne, hConsts,
    hX, hY, native_teq, native_ite, native_not, SmtEval.native_not]

private theorem prog_arith_poly_norm_rel_eq_arg_of_typeof_bool
    (a1 prem : Term) :
  __eo_typeof (__eo_prog_arith_poly_norm_rel a1 (Proof.pf prem)) = Term.Bool ->
  __eo_prog_arith_poly_norm_rel a1 (Proof.pf prem) = a1 := by
  intro hTy
  have hProg : __eo_prog_arith_poly_norm_rel a1 (Proof.pf prem) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f right =>
      cases f with
      | Apply eqHead left =>
          cases eqHead with
          | UOp op =>
              cases op <;> (try (exfalso; apply hProg; rfl))
              case eq =>
                cases left with
                | Apply lf x2 =>
                    cases lf with
                    | Apply r x1 =>
                        cases right with
                        | Apply rf y2 =>
                            cases rf with
                            | Apply r2 y1 =>
                                cases prem with
                                | Apply pf pright =>
                                    cases pf with
                                    | Apply peqHead pleft =>
                                        cases peqHead with
                                        | UOp pop =>
                                            cases pop <;> (try (exfalso; apply hProg; rfl))
                                            case eq =>
                                              cases pleft with
                                              | Apply plf plarg =>
                                                  cases plf with
                                                  | Apply pmulHead cx =>
                                                      cases pmulHead with
                                                      | UOp pmulOp =>
                                                          cases pmulOp <;> (try (exfalso; apply hProg; rfl))
                                                          case mult =>
                                                            cases plarg with
                                                            | Apply pxf one =>
                                                                cases pxf with
                                                                | Apply pxHead x =>
                                                                    cases pxHead with
                                                                    | UOp pxOp =>
                                                                        cases pxOp <;> (try (exfalso; apply hProg; rfl))
                                                                        case mult =>
                                                                          cases pright with
                                                                          | Apply prf prarg =>
                                                                              cases prf with
                                                                              | Apply prmulHead cy =>
                                                                                  cases prmulHead with
                                                                                  | UOp prmulOp =>
                                                                                      cases prmulOp <;> (try (exfalso; apply hProg; rfl))
                                                                                      case mult =>
                                                                                        cases prarg with
                                                                                        | Apply pyf one2 =>
                                                                                            cases pyf with
                                                                                            | Apply pyHead y =>
                                                                                                cases pyHead with
                                                                                                | UOp pyOp =>
                                                                                                    cases pyOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                    case mult =>
                                                                                                      exact
                                                                                                        prog_arith_poly_norm_rel_eq_arg_of_typeof_bool_shape
                                                                                                          r x1 x2 r2 y1 y2 cx x one cy y one2 hTy
                                                                                                | _ =>
                                                                                                    exact False.elim
                                                                                                      (hProg (by rfl))
                                                                                            | _ =>
                                                                                                exact False.elim
                                                                                                  (hProg (by rfl))
                                                                                        | _ =>
                                                                                            exact False.elim
                                                                                              (hProg (by rfl))
                                                                                  | _ =>
                                                                                      exact False.elim
                                                                                        (hProg (by rfl))
                                                                              | _ =>
                                                                                  exact False.elim
                                                                                    (hProg (by rfl))
                                                                          | _ =>
                                                                              exact False.elim
                                                                                (hProg (by rfl))
                                                                    | _ =>
                                                                        exact False.elim
                                                                          (hProg (by rfl))
                                                                | _ =>
                                                                    exact False.elim
                                                                      (hProg (by rfl))
                                                            | _ =>
                                                                exact False.elim
                                                                  (hProg (by rfl))
                                                      | _ =>
                                                          exact False.elim
                                                            (hProg (by rfl))
                                                  | _ =>
                                                      exact False.elim
                                                        (hProg (by rfl))
                                              | _ =>
                                                  exact False.elim
                                                    (hProg (by rfl))
                                        | _ =>
                                            exact False.elim
                                              (hProg (by rfl))
                                    | _ =>
                                        exact False.elim
                                          (hProg (by rfl))
                                | _ =>
                                    exact False.elim (hProg (by rfl))
                            | _ =>
                                exact False.elim (hProg (by rfl))
                        | _ =>
                            exact False.elim (hProg (by rfl))
                    | _ =>
                        exact False.elim (hProg (by rfl))
                | _ =>
                    exact False.elim (hProg (by rfl))
          | _ =>
              exact False.elim (hProg (by rfl))
      | _ =>
          exact False.elim (hProg (by rfl))
  | _ =>
      exact False.elim (hProg (by rfl))

theorem typed___eo_prog_arith_poly_norm_rel_impl
    (a1 prem : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_arith_poly_norm_rel a1 (Proof.pf prem)) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_arith_poly_norm_rel a1 (Proof.pf prem)) := by
  intro hA1Trans hResultTy
  have hProgEq :
      __eo_prog_arith_poly_norm_rel a1 (Proof.pf prem) = a1 :=
    prog_arith_poly_norm_rel_eq_arg_of_typeof_bool a1 prem hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem facts___eo_prog_arith_poly_norm_rel_impl_shape
    (M : SmtModel) (hM : model_wf M)
    (r x1 x2 r2 y1 y2 cx x one cy y one2 : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply r x1) x2))
      (Term.Apply (Term.Apply r2 y1) y2)) ->
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)))
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one2))) ->
  eo_interprets M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)))
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one2))) true ->
  __eo_typeof
      (__eo_prog_arith_poly_norm_rel
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply r x1) x2))
          (Term.Apply (Term.Apply r2 y1) y2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one2))))) = Term.Bool ->
  eo_interprets M
      (__eo_prog_arith_poly_norm_rel
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply r x1) x2))
          (Term.Apply (Term.Apply r2 y1) y2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one2))))) true := by
  intro hA1Trans hPremBool hPremTrue hResultTy
  have hProgEq :=
    prog_arith_poly_norm_rel_eq_arg_of_typeof_bool_shape
      r x1 x2 r2 y1 y2 cx x one cy y one2 hResultTy
  have hProg :
      __eo_prog_arith_poly_norm_rel
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply r x1) x2))
          (Term.Apply (Term.Apply r2 y1) y2))
        (Proof.pf
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one2)))) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  let guardSame := __eo_and (__eo_eq r r2) (__eo_eq one one2)
  let restOne :=
    __eo_requires (__eo_to_q one) (Term.Rational (native_mk_rational 1 1))
      (__eo_requires (__is_poly_norm_rel_consts (Term.Apply (Term.Apply r cx) cy))
        (Term.Boolean true)
        (__eo_requires
          (__is_eq_maybe_to_real x (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))
          (Term.Boolean true)
          (__eo_requires
            (__is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2))
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply r x1) x2))
              (Term.Apply (Term.Apply r y1) y2)))))
  have hOuter :
      __eo_requires guardSame (Term.Boolean true) restOne ≠ Term.Stuck := by
    simpa [__eo_prog_arith_poly_norm_rel, guardSame, restOne] using hProg
  have hGuardSame : guardSame = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hOuter
  have hRestOne : restOne ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hOuter
  have hSameParts := eo_and_true hGuardSame
  have hr : r = r2 := eo_eq_true_eq hSameParts.1
  have hOneSame : one = one2 := eo_eq_true_eq hSameParts.2
  subst r2
  subst one2
  have hOne :
      __eo_to_q one = Term.Rational (native_mk_rational 1 1) :=
    eo_requires_arg_eq_of_ne_stuck hRestOne
  have hRestConsts :
      __eo_requires (__is_poly_norm_rel_consts (Term.Apply (Term.Apply r cx) cy))
        (Term.Boolean true)
        (__eo_requires
          (__is_eq_maybe_to_real x (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))
          (Term.Boolean true)
          (__eo_requires
            (__is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2))
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply r x1) x2))
              (Term.Apply (Term.Apply r y1) y2)))) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestOne
  have hConsts :
      __is_poly_norm_rel_consts (Term.Apply (Term.Apply r cx) cy) = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hRestConsts
  have hRestX :
      __eo_requires
          (__is_eq_maybe_to_real x (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2))
          (Term.Boolean true)
          (__eo_requires
            (__is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2))
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply r x1) x2))
              (Term.Apply (Term.Apply r y1) y2))) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestConsts
  have hX :
      __is_eq_maybe_to_real x (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x1) x2) =
        Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hRestX
  have hRestY :
      __eo_requires
            (__is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2))
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply r x1) x2))
              (Term.Apply (Term.Apply r y1) y2)) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hRestX
  have hY :
      __is_eq_maybe_to_real y (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y1) y2) =
        Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hRestY
  let lhs :=
    Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)
  let rhs :=
    Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one)
  have hPremTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) := by
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ (by simpa [lhs, rhs] using hPremBool)
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation lhs rhs hPremTrans with
    ⟨hLhsRhsTy, hLhsNN⟩
  have hRhsNN : __smtx_typeof (__eo_to_smt rhs) ≠ SmtType.None := by
    intro hNone
    exact hLhsNN (by rw [hLhsRhsTy, hNone])
  have hLhsArith :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one))) =
          SmtType.Int ∨
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cx)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one))) =
          SmtType.Real := by
    exact mult_term_arith_type_of_non_none cx
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) one)
      (by simpa [lhs] using hLhsNN)
  have hRhsArith :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one))) =
          SmtType.Int ∨
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.mult) cy)
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one))) =
          SmtType.Real := by
    exact mult_term_arith_type_of_non_none cy
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) one)
      (by simpa [rhs] using hRhsNN)
  have hXMaybe := is_eq_maybe_to_real_true hX
  have hYMaybe := is_eq_maybe_to_real_true hY
  have hDiffXTy :=
    diff_arith_type_of_scaled_factor cx x one x1 x2 hLhsArith hXMaybe
  have hDiffYTy :=
    diff_arith_type_of_scaled_factor cy y one y1 y2 hRhsArith hYMaybe
  rcases arith_rel_eval_bools_of_diff_type M hM x1 x2 hDiffXTy with
    ⟨qx, hDiffXDen, hLtX, hLeX, hEqX, hGtX, hGeX⟩
  rcases arith_rel_eval_bools_of_diff_type M hM y1 y2 hDiffYTy with
    ⟨qy, hDiffYDen, hLtY, hLeY, hEqY, hGtY, hGeY⟩
  have hXDen : arith_atom_denote_real M x = SmtValue.Rational qx := by
    rcases hXMaybe with hXd | hXTo
    · rw [hXd]
      exact hDiffXDen
    · have hLhsArith' := hLhsArith
      rw [hXTo] at hLhsArith'
      have hXInt := diff_int_type_of_scaled_factor_to_real cx one x1 x2 hLhsArith'
      rw [hXTo, arith_atom_denote_real_of_to_real M hM _ hXInt]
      exact hDiffXDen
  have hYDen : arith_atom_denote_real M y = SmtValue.Rational qy := by
    rcases hYMaybe with hYd | hYTo
    · rw [hYd]
      exact hDiffYDen
    · have hRhsArith' := hRhsArith
      rw [hYTo] at hRhsArith'
      have hYInt := diff_int_type_of_scaled_factor_to_real cy one y1 y2 hRhsArith'
      rw [hYTo, arith_atom_denote_real_of_to_real M hM _ hYInt]
      exact hDiffYDen
  rcases is_poly_norm_rel_consts_true_info r cx cy hConsts with
    ⟨c, d, hCxQ, hCyQ, hc0, hd0, hConstsRel⟩
  have hCxDen := arith_atom_denote_real_of_to_q M cx c hCxQ
  have hCyDen := arith_atom_denote_real_of_to_q M cy d hCyQ
  have hOneDen :=
    arith_atom_denote_real_of_to_q M one (native_mk_rational 1 1) hOne
  have hPremRel := RuleProofs.eo_interprets_eq_rel M lhs rhs (by simpa [lhs, rhs] using hPremTrue)
  have hAtomsEq := arith_atom_denote_real_eq_of_smt_value_rel M lhs rhs hPremRel
  have hLhsScaled :
      arith_atom_denote_real M lhs =
        SmtValue.Rational (native_qmult c qx) := by
    simpa [lhs] using
      arith_atom_denote_real_of_scaled_factor M hM cx x one c qx
        hLhsArith hCxDen hXDen hOneDen
  have hRhsScaled :
      arith_atom_denote_real M rhs =
        SmtValue.Rational (native_qmult d qy) := by
    simpa [rhs] using
      arith_atom_denote_real_of_scaled_factor M hM cy y one d qy
        hRhsArith hCyDen hYDen hOneDen
  have hScaled : native_qmult c qx = native_qmult d qy := by
    have h :
        SmtValue.Rational (native_qmult c qx) =
          SmtValue.Rational (native_qmult d qy) := by
      rw [← hLhsScaled, ← hRhsScaled]
      exact hAtomsEq
    injection h with hRat
  have hOutBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply r x1) x2))
          (Term.Apply (Term.Apply r y1) y2)) := by
    have hProgBool :=
      typed___eo_prog_arith_poly_norm_rel_impl
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply r x1) x2))
          (Term.Apply (Term.Apply r y1) y2))
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs)
        (by simpa using hA1Trans)
        (by simpa [lhs, rhs] using hResultTy)
    simpa [hProgEq, lhs, rhs] using hProgBool
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply r x1) x2)
    (Term.Apply (Term.Apply r y1) y2)
    hOutBool
    (arith_rel_smt_value_rel_of_scaled M r cx cy x1 x2 y1 y2 c d qx qy
      hCxQ hCyQ hc0 hd0 hConstsRel hScaled
      hLtX hLeX hEqX hGtX hGeX hLtY hLeY hEqY hGtY hGeY)

private theorem facts___eo_prog_arith_poly_norm_rel_impl
    (M : SmtModel) (hM : model_wf M) (a1 prem : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  RuleProofs.eo_has_bool_type prem ->
  eo_interprets M prem true ->
  __eo_typeof (__eo_prog_arith_poly_norm_rel a1 (Proof.pf prem)) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_poly_norm_rel a1 (Proof.pf prem)) true := by
  intro hA1Trans hPremBool hPremTrue hResultTy
  have hProg : __eo_prog_arith_poly_norm_rel a1 (Proof.pf prem) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases a1 with
  | Apply f right =>
      cases f with
      | Apply eqHead left =>
          cases eqHead with
          | UOp op =>
              cases op <;> (try (exfalso; apply hProg; rfl))
              case eq =>
                cases left with
                | Apply lf x2 =>
                    cases lf with
                    | Apply r x1 =>
                        cases right with
                        | Apply rf y2 =>
                            cases rf with
                            | Apply r2 y1 =>
                                cases prem with
                                | Apply pf pright =>
                                    cases pf with
                                    | Apply peqHead pleft =>
                                        cases peqHead with
                                        | UOp pop =>
                                            cases pop <;> (try (exfalso; apply hProg; rfl))
                                            case eq =>
                                              cases pleft with
                                              | Apply plf plarg =>
                                                  cases plf with
                                                  | Apply pmulHead cx =>
                                                      cases pmulHead with
                                                      | UOp pmulOp =>
                                                          cases pmulOp <;> (try (exfalso; apply hProg; rfl))
                                                          case mult =>
                                                            cases plarg with
                                                            | Apply pxf one =>
                                                                cases pxf with
                                                                | Apply pxHead x =>
                                                                    cases pxHead with
                                                                    | UOp pxOp =>
                                                                        cases pxOp <;> (try (exfalso; apply hProg; rfl))
                                                                        case mult =>
                                                                          cases pright with
                                                                          | Apply prf prarg =>
                                                                              cases prf with
                                                                              | Apply prmulHead cy =>
                                                                                  cases prmulHead with
                                                                                  | UOp prmulOp =>
                                                                                      cases prmulOp <;> (try (exfalso; apply hProg; rfl))
                                                                                      case mult =>
                                                                                        cases prarg with
                                                                                        | Apply pyf one2 =>
                                                                                            cases pyf with
                                                                                            | Apply pyHead y =>
                                                                                                cases pyHead with
                                                                                                | UOp pyOp =>
                                                                                                    cases pyOp <;> (try (exfalso; apply hProg; rfl))
                                                                                                    case mult =>
                                                                                                      exact
                                                                                                        facts___eo_prog_arith_poly_norm_rel_impl_shape
                                                                                                          M hM r x1 x2 r2 y1 y2 cx x one cy y one2
                                                                                                          hA1Trans hPremBool hPremTrue hResultTy
                                                                                                | _ =>
                                                                                                    exact False.elim
                                                                                                      (hProg (by rfl))
                                                                                            | _ =>
                                                                                                exact False.elim
                                                                                                  (hProg (by rfl))
                                                                                        | _ =>
                                                                                            exact False.elim
                                                                                              (hProg (by rfl))
                                                                                  | _ =>
                                                                                      exact False.elim
                                                                                        (hProg (by rfl))
                                                                              | _ =>
                                                                                  exact False.elim
                                                                                    (hProg (by rfl))
                                                                          | _ =>
                                                                              exact False.elim
                                                                                (hProg (by rfl))
                                                                    | _ =>
                                                                        exact False.elim
                                                                          (hProg (by rfl))
                                                                | _ =>
                                                                    exact False.elim
                                                                      (hProg (by rfl))
                                                            | _ =>
                                                                exact False.elim
                                                                  (hProg (by rfl))
                                                      | _ =>
                                                          exact False.elim
                                                            (hProg (by rfl))
                                                  | _ =>
                                                      exact False.elim
                                                        (hProg (by rfl))
                                              | _ =>
                                                  exact False.elim
                                                    (hProg (by rfl))
                                        | _ =>
                                            exact False.elim
                                              (hProg (by rfl))
                                    | _ =>
                                        exact False.elim
                                          (hProg (by rfl))
                                | _ =>
                                    exact False.elim (hProg (by rfl))
                            | _ =>
                                exact False.elim (hProg (by rfl))
                        | _ =>
                            exact False.elim (hProg (by rfl))
                    | _ =>
                        exact False.elim (hProg (by rfl))
                | _ =>
                    exact False.elim (hProg (by rfl))
          | _ =>
              exact False.elim (hProg (by rfl))
      | _ =>
          exact False.elim (hProg (by rfl))
  | _ =>
      exact False.elim (hProg (by rfl))

public theorem cmd_step_arith_poly_norm_rel_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_poly_norm_rel args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_poly_norm_rel args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_poly_norm_rel args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_poly_norm_rel args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  let A1 := a1
                  let P := __eo_state_proven_nth s n1
                  have hArgsTrans :
                      cArgListTranslationOk (CArgList.cons A1 CArgList.nil) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation A1 := by
                    simpa [cArgListTranslationOk] using hArgsTrans
                  have hPremBool : RuleProofs.eo_has_bool_type P :=
                    hPremisesBool P (by simp [P, premiseTermList])
                  change
                    __eo_typeof (__eo_prog_arith_poly_norm_rel A1 (Proof.pf P)) =
                      Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hPremTrue : eo_interprets M P true :=
                      hTrue P (by simp [P, premiseTermList])
                    change eo_interprets M
                      (__eo_prog_arith_poly_norm_rel A1 (Proof.pf P)) true
                    exact facts___eo_prog_arith_poly_norm_rel_impl
                      M hM A1 P hA1Trans hPremBool hPremTrue hResultTy
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arith_poly_norm_rel A1 (Proof.pf P))
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                      (__eo_prog_arith_poly_norm_rel A1 (Proof.pf P))
                      (typed___eo_prog_arith_poly_norm_rel_impl
                        A1 P hA1Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
