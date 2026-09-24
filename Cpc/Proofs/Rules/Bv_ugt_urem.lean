module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_eq_true_eq {x y : Term} :
    __eo_eq x y = Term.Boolean true ->
    y = x := by
  intro h
  exact RuleProofs.eq_of_eo_eq_true x y h

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

private theorem requires_eq_true_stuck_of_ne (x y B : Term) :
    x ≠ y ->
    __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck := by
  intro hNe
  by_cases hReq : __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck
  · exact hReq
  · have hEqTrue : __eo_eq x y = Term.Boolean true :=
      eo_requires_arg_eq_of_ne_stuck hReq
    have hYX : y = x := eo_eq_true_eq hEqTrue
    exact False.elim (hNe hYX.symm)

private theorem bv_ugt_urem_shape_of_ne_stuck (y x w P : Term) :
    __eo_prog_bv_ugt_urem y x w (Proof.pf P) ≠ Term.Stuck ->
    y ≠ Term.Stuck ∧ x ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
    ∃ pw px,
      P = Term.Apply (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px) := by
  intro hProg
  have hy : y ≠ Term.Stuck := by
    intro hy
    subst y
    exact hProg (__eo_prog_bv_ugt_urem.eq_1 x w (Proof.pf P))
  have hx : x ≠ Term.Stuck := by
    intro hx
    subst x
    exact hProg (__eo_prog_bv_ugt_urem.eq_2 y w (Proof.pf P) hy)
  have hw : w ≠ Term.Stuck := by
    intro hw
    subst w
    exact hProg (__eo_prog_bv_ugt_urem.eq_3 y x (Proof.pf P) hy hx)
  refine ⟨hy, hx, hw, ?_⟩
  by_cases hShape : ∃ pw px,
      P = Term.Apply (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px)
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_ugt_urem.eq_5 y x w (Proof.pf P) hy hx hw (by
        intro pw px hP
        cases hP
        exact hShape ⟨pw, px, rfl⟩)))

private theorem bv_ugt_urem_guard_eqs_of_ne_stuck
    {y w pw px body : Term} :
    __eo_requires (__eo_and (__eo_eq w pw) (__eo_eq y px))
        (Term.Boolean true) body ≠ Term.Stuck ->
    pw = w ∧ px = y := by
  intro hReq
  have hGuard :
      __eo_and (__eo_eq w pw) (__eo_eq y px) = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReq
  exact ⟨eo_eq_true_eq (eo_and_eq_true_left hGuard),
    eo_eq_true_eq (eo_and_eq_true_right hGuard)⟩

private theorem prog_bv_ugt_urem_canonical_eq_of_ne_stuck (y x w : Term) :
    y ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    __eo_prog_bv_ugt_urem y x w
        (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) y))) =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
            (Term.Boolean true))) := by
  intro hy hx hw
  rw [__eo_prog_bv_ugt_urem.eq_4 y x w w y hy hx hw]
  rw [RuleProofs.eo_eq_self_of_ne_stuck w hw,
    RuleProofs.eo_eq_self_of_ne_stuck y hy]
  simp [__eo_and, __eo_requires, native_ite, native_teq, native_and,
    native_not, SmtEval.native_not]

private theorem typeof_bvand_ne_stuck_inv :
    (A B : Term) ->
    __eo_typeof_bvand A B ≠ Term.Stuck ->
    ∃ bw, A = Term.Apply (Term.UOp UserOp.BitVec) bw ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) bw
  | A, B, hNe => by
      cases A <;> try simp [__eo_typeof_bvand] at hNe
      case Apply f a =>
        cases f <;> try simp [__eo_typeof_bvand] at hNe
        case UOp op =>
          cases op <;> try simp [__eo_typeof_bvand] at hNe
          case BitVec =>
            cases B <;> try simp [__eo_typeof_bvand] at hNe
            case Apply g b =>
              cases g <;> try simp [__eo_typeof_bvand] at hNe
              case UOp op' =>
                cases op' <;> try simp [__eo_typeof_bvand] at hNe
                case BitVec =>
                  by_cases hEq : a = b
                  · subst b
                    exact ⟨a, rfl, rfl⟩
                  · exfalso
                    apply hNe
                    simpa [__eo_typeof_bvand] using
                      requires_eq_true_stuck_of_ne a b
                        (Term.Apply (Term.UOp UserOp.BitVec) a) hEq

private theorem typeof_bvult_ne_stuck_inv :
    (A B : Term) ->
    __eo_typeof_bvult A B ≠ Term.Stuck ->
    ∃ bw, A = Term.Apply (Term.UOp UserOp.BitVec) bw ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) bw
  | A, B, hNe => by
      cases A <;> try simp [__eo_typeof_bvult] at hNe
      case Apply f a =>
        cases f <;> try simp [__eo_typeof_bvult] at hNe
        case UOp op =>
          cases op <;> try simp [__eo_typeof_bvult] at hNe
          case BitVec =>
            cases B <;> try simp [__eo_typeof_bvult] at hNe
            case Apply g b =>
              cases g <;> try simp [__eo_typeof_bvult] at hNe
              case UOp op' =>
                cases op' <;> try simp [__eo_typeof_bvult] at hNe
                case BitVec =>
                  by_cases hEq : a = b
                  · subst b
                    exact ⟨a, rfl, rfl⟩
                  · exfalso
                    apply hNe
                    simpa [__eo_typeof_bvult] using
                      requires_eq_true_stuck_of_ne a b Term.Bool hEq

private theorem typeof_or_bool_inv {A B : Term} :
    __eo_typeof_or A B = Term.Bool ->
    A = Term.Bool ∧ B = Term.Bool := by
  intro h
  unfold __eo_typeof_or at h
  split at h
  · exact ⟨rfl, rfl⟩
  · cases h

private theorem width_eq_of_typeof_eq_bitvec_at_bv (u w : Term) :
    w ≠ Term.Stuck ->
    __eo_typeof_eq (Term.Apply (Term.UOp UserOp.BitVec) u)
        (__eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int)) =
      Term.Bool ->
    w = u := by
  intro hW hTy
  cases hWTy : __eo_typeof w with
  | UOp nop =>
      cases nop
      · -- Int width type
        have hTy' :
            __eo_typeof_eq
                (Term.Apply (Term.UOp UserOp.BitVec) u)
                (__eo_requires
                  (__eo_gt w (Term.Numeral (-1 : native_Int)))
                  (Term.Boolean true)
                  (Term.Apply (Term.UOp UserOp.BitVec) w)) =
              Term.Bool := by
          simpa [__eo_typeof_int_to_bv, hWTy, hW] using hTy
        have hOpEq :=
          support_eo_typeof_eq_bool_operands_eq _ _ hTy'
        have hReqNN :
            __eo_requires
                (__eo_gt w (Term.Numeral (-1 : native_Int)))
                (Term.Boolean true)
                (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
              Term.Stuck := by
          rw [← hOpEq]
          intro h
          cases h
        have hGuard :=
          support_eo_requires_cond_eq_of_non_stuck hReqNN
        have hReqEq :
            __eo_requires
                (__eo_gt w (Term.Numeral (-1 : native_Int)))
                (Term.Boolean true)
                (Term.Apply (Term.UOp UserOp.BitVec) w) =
              Term.Apply (Term.UOp UserOp.BitVec) w := by
          simp [__eo_requires, hGuard, native_ite, native_teq,
            native_not]
        have hBv :
            Term.Apply (Term.UOp UserOp.BitVec) u =
              Term.Apply (Term.UOp UserOp.BitVec) w :=
          hOpEq.trans hReqEq
        injection hBv with _ hUW
        exact hUW.symm
      all_goals
        exfalso
        simpa [__eo_typeof_eq, __eo_typeof_int_to_bv, __eo_requires,
          __eo_eq, native_ite, native_teq, native_not, hWTy] using hTy
  | _ =>
      exfalso
      simpa [__eo_typeof_eq, __eo_typeof_int_to_bv, __eo_requires,
        __eo_eq, native_ite, native_teq, native_not, hWTy] using hTy

private theorem typeof_args_of_ugt_urem_body_bool (y x w : Term) :
    w ≠ Term.Stuck ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
              (Term.Boolean true)))) = Term.Bool ->
    ∃ u, __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) u ∧
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) u ∧ w = u := by
  intro hW hTy
  change __eo_typeof_eq
      (__eo_typeof_bvult
        (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x))
        (__eo_typeof x))
      (__eo_typeof_or
        (__eo_typeof_eq (__eo_typeof x)
          (__eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int)))
        (__eo_typeof_or
          (__eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int)))
          Term.Bool)) =
    Term.Bool at hTy
  have hANe :
      __eo_typeof_bvult
          (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x))
          (__eo_typeof x) ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hTy
    simp [__eo_typeof_eq] at hTy
  rcases typeof_bvult_ne_stuck_inv _ _ hANe with ⟨m, hBvand, hXTy⟩
  have hBvandNe :
      __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x) ≠ Term.Stuck := by
    rw [hBvand]
    intro h
    cases h
  rcases typeof_bvand_ne_stuck_inv _ _ hBvandNe with ⟨bw, hYTy, hXTy2⟩
  have hbwm : bw = m := by
    simpa using hXTy2.symm.trans hXTy
  subst hbwm
  have hMNe : bw ≠ Term.Stuck := by
    intro hM
    subst hM
    apply hANe
    rw [hBvand, hXTy]
    simp [__eo_typeof_bvult, __eo_eq, __eo_requires, native_ite,
      native_teq]
  have hABool :
      __eo_typeof_bvult
          (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x))
          (__eo_typeof x) = Term.Bool := by
    rw [hBvand, hXTy]
    simp [__eo_typeof_bvult, RuleProofs.eo_eq_self_of_ne_stuck bw hMNe,
      __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not]
  rw [hABool] at hTy
  have hOpEq := support_eo_typeof_eq_bool_operands_eq _ _ hTy
  rcases typeof_or_bool_inv hOpEq.symm with ⟨hC, _hD⟩
  rw [hXTy] at hC
  have hWM := width_eq_of_typeof_eq_bitvec_at_bv bw w hW hC
  exact ⟨bw, hYTy, hXTy, hWM⟩

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x1 w : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_typeof x1 = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x1) = SmtType.BitVec (native_int_to_nat n) := by
  intro hX1Trans hX1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt x1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x1) rfl
      hX1Trans hX1Type
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hX1Trans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hX1Trans hSmtType)

private theorem smt_typeof_bv_const
    (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
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
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
      SmtValue.Binary n (native_mod_total k (native_int_pow2 n)) := by
  intro hNonneg
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral k)) =
    SmtValue.Binary n (native_mod_total k (native_int_pow2 n))
  simp [native_ite, hNonneg]

private theorem eo_to_smt_eq_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
      SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_and_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) =
      SmtTerm.and (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_bvurem_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b) =
      SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_bvugt_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) a) b) =
      SmtTerm.bvugt (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_boolean (b : Bool) :
    __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b := by
  rfl

private theorem smt_typeof_eq_same_non_none
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

private theorem smt_typeof_and_bool
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.Bool ->
    __smtx_typeof b = SmtType.Bool ->
    __smtx_typeof (SmtTerm.and a b) = SmtType.Bool := by
  intro ha hb
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [ha, hb, native_ite]

private theorem smt_typeof_boolean (b : Bool) :
    __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smt_typeof_bvurem_same
    (a b : SmtTerm) (n : native_Int) :
    __smtx_typeof a = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof b = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (SmtTerm.bvurem a b) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro ha hb
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, ha, hb, native_nateq, native_ite]

private theorem smt_typeof_bvugt_bool
    (a b : SmtTerm) (n : native_Int) :
    __smtx_typeof a = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof b = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (SmtTerm.bvugt a b) = SmtType.Bool := by
  intro ha hb
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2_ret, ha, hb, native_nateq, native_ite]

private theorem smt_typeof_ugt_urem_lhs_bool (y x : Term) (n : native_Int) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x)) =
      SmtType.Bool := by
  intro hY hX
  rw [eo_to_smt_bvugt_term, eo_to_smt_bvurem_term]
  exact smt_typeof_bvugt_bool _ _ n
    (smt_typeof_bvurem_same _ _ n hY hX) hX

private theorem smt_typeof_ugt_urem_rhs_bool (y x : Term) (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))
              (Term.Boolean true)))) =
      SmtType.Bool := by
  intro hNonneg hY hX
  have hZeroTy := smt_typeof_bv_const 0 n hNonneg
  rw [eo_to_smt_and_term, eo_to_smt_eq_term, eo_to_smt_and_term,
    eo_to_smt_bvugt_term, eo_to_smt_boolean]
  apply smt_typeof_and_bool
  · exact smt_typeof_eq_same_non_none _ _ (SmtType.BitVec (native_int_to_nat n))
      hX hZeroTy (by intro h; cases h)
  · apply smt_typeof_and_bool
    · exact smt_typeof_bvugt_bool _ _ n hY hZeroTy
    · exact smt_typeof_boolean true

private theorem eval_smt_eq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) =
      __smtx_model_eval_eq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_and (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.and a b) =
      __smtx_model_eval_and (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_bvurem (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvurem a b) =
      __smtx_model_eval_bvurem (__smtx_model_eval M a)
        (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_bvugt (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvugt a b) =
      __smtx_model_eval_bvugt (__smtx_model_eval M a)
        (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_boolean (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_ugt_urem_sides_eq
    (M : SmtModel) (hM : model_wf M) (y x : Term) (n : native_Int) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation x ->
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))
              (Term.Boolean true)))) := by
  intro hYTrans hXTrans hNonneg hYSmtTy hXSmtTy
  have hWidthEq : native_nat_to_int (native_int_to_nat n) = n := by
    have hnNonneg : 0 <= n := by
      simpa [SmtEval.native_zleq] using hNonneg
    have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
      Int.toNat_of_nonneg hnNonneg
    simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      native_nat_to_int, native_int_to_nat] using hInt
  have hEvalTyY :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hYTrans)
  have hEvalTyX :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hXTrans)
  rcases bitvec_value_canonical hEvalTyY with ⟨py, hEvalY⟩
  rcases bitvec_value_canonical hEvalTyX with ⟨px, hEvalX⟩
  rw [hWidthEq] at hEvalY hEvalX
  have hEvalTyYN :
      __smtx_typeof_value (SmtValue.Binary n py) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hEvalY] using hEvalTyY
  have hEvalTyXN :
      __smtx_typeof_value (SmtValue.Binary n px) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hEvalX] using hEvalTyX
  have hPyCanon :
      native_zeq py (native_mod_total py (native_int_pow2 n)) = true :=
    bitvec_payload_canonical hEvalTyYN
  have hPxCanon :
      native_zeq px (native_mod_total px (native_int_pow2 n)) = true :=
    bitvec_payload_canonical hEvalTyXN
  have hPyRange := bitvec_payload_range_of_canonical hNonneg hPyCanon
  have hPxRange := bitvec_payload_range_of_canonical hNonneg hPxCanon
  have hPyMod : py % native_int_pow2 n = py := by
    have h : py = py % native_int_pow2 n :=
      of_decide_eq_true hPyCanon
    exact h.symm
  have hZeroEval := eval_bv_const M 0 n hNonneg
  have hZeroPayload : native_mod_total 0 (native_int_pow2 n) = 0 := by
    simp [SmtEval.native_mod_total]
  rw [hZeroPayload] at hZeroEval
  rw [eo_to_smt_bvugt_term, eo_to_smt_bvurem_term, eo_to_smt_and_term,
    eo_to_smt_eq_term, eo_to_smt_and_term, eo_to_smt_bvugt_term,
    eo_to_smt_boolean]
  rw [eval_smt_bvugt, eval_smt_bvurem, eval_smt_and, eval_smt_eq,
    eval_smt_and, eval_smt_bvugt, eval_smt_boolean]
  rw [hEvalY, hEvalX, hZeroEval]
  by_cases hpx : px = 0
  · subst hpx
    simp [__smtx_model_eval_bvurem, __smtx_model_eval_bvugt,
      __smtx_model_eval_and, __smtx_model_eval_eq, SmtEval.native_zeq,
      SmtEval.native_zlt, native_zlt, native_veq, SmtEval.native_and,
      native_ite, SmtEval.native_mod_total, hPyMod]
  · have hPxPos : 0 < px := by
      rcases Int.lt_or_eq_of_le hPxRange.1 with hlt | heq
      · exact hlt
      · exact False.elim (hpx heq.symm)
    have hModNonneg : 0 <= py % px := Int.emod_nonneg py hpx
    have hModLtPx : py % px < px := Int.emod_lt_of_pos py hPxPos
    have hModLtPow : py % px < native_int_pow2 n :=
      Int.lt_trans hModLtPx hPxRange.2
    have hModMod : (py % px) % native_int_pow2 n = py % px :=
      Int.emod_eq_of_lt hModNonneg hModLtPow
    have hNotLt : ¬ px < py % px :=
      Int.not_lt.mpr (Int.le_of_lt hModLtPx)
    simp [__smtx_model_eval_bvurem, __smtx_model_eval_bvugt,
      __smtx_model_eval_and, __smtx_model_eval_eq, SmtEval.native_zeq,
      SmtEval.native_zlt, native_zlt, native_veq, SmtEval.native_and,
      native_ite, SmtEval.native_mod_total, hpx, hModMod, hNotLt]

private theorem typed_bv_ugt_urem_body (y x w : Term) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation x ->
    w ≠ Term.Stuck ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
              (Term.Boolean true)))) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
            (Term.Boolean true)))) := by
  intro hYTrans hXTrans hW hTy
  rcases typeof_args_of_ugt_urem_body_bool y x w hW hTy with
    ⟨u, hYType, hXType, hWU⟩
  subst hWU
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y w hYTrans hYType with
    ⟨n, hU, hNonneg, hYSmtTy⟩
  subst hU
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x (Term.Numeral n)
      hXTrans hXType with
    ⟨nx, hNx, _hXNonneg, hXSmtTyRaw⟩
  cases hNx
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    ((smt_typeof_ugt_urem_lhs_bool y x n hYSmtTy hXSmtTyRaw).trans
      (smt_typeof_ugt_urem_rhs_bool y x n hNonneg hYSmtTy hXSmtTyRaw).symm)
    (by
      rw [smt_typeof_ugt_urem_lhs_bool y x n hYSmtTy hXSmtTyRaw]
      intro h
      cases h)

private theorem facts_bv_ugt_urem_body
    (M : SmtModel) (hM : model_wf M) (y x w : Term) :
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation x ->
    w ≠ Term.Stuck ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
              (Term.Boolean true)))) = Term.Bool ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
            (Term.Boolean true)))) true := by
  intro hYTrans hXTrans hW hTy
  have hTyped := typed_bv_ugt_urem_body y x w hYTrans hXTrans hW hTy
  rcases typeof_args_of_ugt_urem_body_bool y x w hW hTy with
    ⟨u, hYType, hXType, hWU⟩
  subst hWU
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width y w hYTrans hYType with
    ⟨n, hU, hNonneg, hYSmtTy⟩
  subst hU
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x (Term.Numeral n)
      hXTrans hXType with
    ⟨nx, hNx, _hXNonneg, hXSmtTyRaw⟩
  cases hNx
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hTyped
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x)))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))
              (Term.Boolean true)))))
    rw [eval_ugt_urem_sides_eq M hM y x n hYTrans hXTrans hNonneg
      hYSmtTy hXSmtTyRaw]
    exact RuleProofs.smt_value_rel_refl _

private theorem trusted_bv_ugt_urem_canonical_properties
    (M : SmtModel) (hM : model_wf M) (y x w : Term) :
    cArgListTranslationOk
      (CArgList.cons y (CArgList.cons x (CArgList.cons w CArgList.nil))) ->
    __eo_typeof
        (__eo_prog_bv_ugt_urem y x w
          (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
            (Term.Apply (Term.UOp UserOp._at_bvsize) y)))) = Term.Bool ->
    StepRuleProperties M
      [Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
        (Term.Apply (Term.UOp UserOp._at_bvsize) y)]
      (__eo_prog_bv_ugt_urem y x w
        (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) y)))) := by
  intro hArgsTrans hResultTy
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [cArgListTranslationOk, eoHasSmtTranslation,
      RuleProofs.eo_has_smt_translation] using hArgsTrans.1
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [cArgListTranslationOk, eoHasSmtTranslation,
      RuleProofs.eo_has_smt_translation] using hArgsTrans.2.1
  have hWTrans : RuleProofs.eo_has_smt_translation w := by
    simpa [cArgListTranslationOk, eoHasSmtTranslation,
      RuleProofs.eo_has_smt_translation] using hArgsTrans.2.2.1
  have hyNe : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hwNe : w ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  have hProgEq := prog_bv_ugt_urem_canonical_eq_of_ne_stuck y x w hyNe hxNe hwNe
  have hBodyTy :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) x))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
                (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
              (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y)
                  (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))
                (Term.Boolean true)))) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  refine ⟨?_, ?_⟩
  · intro _hPrem
    exact facts_bv_ugt_urem_body M hM y x w hYTrans hXTrans hwNe hBodyTy
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (typed_bv_ugt_urem_body y x w hYTrans hXTrans hwNe hBodyTy)

public theorem cmd_step_bv_ugt_urem_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ugt_urem args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ugt_urem args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ugt_urem args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ugt_urem args premises ≠ Term.Stuck :=
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
                          change StepRuleProperties M [P1]
                            (__eo_prog_bv_ugt_urem a1 a2 a3 (Proof.pf P1))
                          have hProgLocal :
                              __eo_prog_bv_ugt_urem a1 a2 a3 (Proof.pf P1) ≠
                                Term.Stuck := by
                            exact hProg
                          rcases bv_ugt_urem_shape_of_ne_stuck a1 a2 a3 P1
                              hProgLocal with
                            ⟨ha1, ha2, ha3, pw, px, hP1⟩
                          subst P1
                          have hReqNe := by
                            have h := hProgLocal
                            rw [hP1] at h
                            rw [__eo_prog_bv_ugt_urem.eq_4 a1 a2 a3 pw px
                              ha1 ha2 ha3] at h
                            exact h
                          rcases bv_ugt_urem_guard_eqs_of_ne_stuck hReqNe with
                            ⟨hpw, hpx⟩
                          subst pw
                          subst px
                          have hArgsTrans :
                              cArgListTranslationOk
                                (CArgList.cons a1
                                  (CArgList.cons a2
                                    (CArgList.cons a3 CArgList.nil))) := by
                            simpa [cmdTranslationOk] using hCmdTrans
                          have hResultTyCanonical :
                              __eo_typeof
                                  (__eo_prog_bv_ugt_urem a1 a2 a3
                                    (Proof.pf
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.eq) a3)
                                        (Term.Apply
                                          (Term.UOp UserOp._at_bvsize) a1)))) =
                                Term.Bool := by
                            have h := hResultTy
                            change __eo_typeof
                                (__eo_prog_bv_ugt_urem a1 a2 a3
                                  (Proof.pf (__eo_state_proven_nth s n1))) =
                              Term.Bool at h
                            simpa [hP1] using h
                          simpa [hP1] using
                            trusted_bv_ugt_urem_canonical_properties M hM a1 a2 a3
                              hArgsTrans hResultTyCanonical
