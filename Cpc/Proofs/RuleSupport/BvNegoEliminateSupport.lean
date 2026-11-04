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

def bvNegoPrem (x n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) n)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x))
      (Term.Numeral 1))

def bvNegoMin (n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat)
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat)
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0)))
      (Term.Binary 0 0))

def bvNegoTerm (x n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.bvnego) x))
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) (bvNegoMin n))

theorem prog_bv_nego_eliminate_eq_of_ne_stuck (x n : Term) :
    x ≠ Term.Stuck ->
    n ≠ Term.Stuck ->
    __eo_prog_bv_nego_eliminate x n (Proof.pf (bvNegoPrem x n)) =
      bvNegoTerm x n := by
  intro hX hN
  unfold bvNegoPrem
  rw [__eo_prog_bv_nego_eliminate.eq_3 x n n x hX hN]
  unfold bvNegoTerm bvNegoMin
  cases x <;> cases n <;>
    simp [__eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
      native_not, SmtEval.native_not, SmtEval.native_and] at hX hN ⊢

theorem bv_nego_shape_of_ne_stuck (x n P : Term) :
    __eo_prog_bv_nego_eliminate x n (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ n ≠ Term.Stuck ∧
      ∃ px pn, P = bvNegoPrem px pn := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_nego_eliminate.eq_1 n (Proof.pf P))
  have hNNe : n ≠ Term.Stuck := by
    intro hN
    subst n
    exact hProg (__eo_prog_bv_nego_eliminate.eq_2 x (Proof.pf P) hXNe)
  refine ⟨hXNe, hNNe, ?_⟩
  by_cases hShape : ∃ px pn, P = bvNegoPrem px pn
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_nego_eliminate.eq_4 x n (Proof.pf P) hXNe hNNe (by
        intro pn px hP
        cases hP
        exact hShape ⟨px, pn, rfl⟩)))

private theorem mk_apply_bitvec_eq_inv (x m : Term)
    (h : __eo_mk_apply (Term.UOp UserOp.BitVec) x =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    x = m := by
  cases x <;> simp [__eo_mk_apply] at h ⊢ <;> exact h

private theorem concat_type_bitvec_inv (A B m : Term)
    (h : __eo_typeof_concat A B = Term.Apply (Term.UOp UserOp.BitVec) m) :
    ∃ a b, A = Term.Apply (Term.UOp UserOp.BitVec) a ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) b ∧ __eo_add a b = m := by
  cases A with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_concat, __eo_mk_apply] at h
          case BitVec =>
            cases B with
            | Apply g b =>
                cases g with
                | UOp op2 =>
                    cases op2 <;> simp [__eo_typeof_concat, __eo_mk_apply] at h
                    case BitVec =>
                      have hAdd : __eo_add a b = m := by
                        change __eo_mk_apply (Term.UOp UserOp.BitVec)
                          (__eo_add a b) =
                          Term.Apply (Term.UOp UserOp.BitVec) m at h
                        exact mk_apply_bitvec_eq_inv (__eo_add a b) m h
                      exact ⟨a, b, rfl, rfl, hAdd⟩
                | _ => simp [__eo_typeof_concat] at h
            | _ => simp [__eo_typeof_concat] at h
      | _ => simp [__eo_typeof_concat] at h
  | _ => simp [__eo_typeof_concat] at h

theorem at_bv_type_bitvec_inv (n m : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (h : __eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    ∃ i, n = Term.Numeral i ∧ native_zleq 0 i = true ∧
      m = Term.Numeral i := by
  have h' :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) m := by
    simpa [__eo_typeof_int_to_bv, hN, hNTy] using h
  have hReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    rw [h']
    intro hc
    cases hc
  have hGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReqNN
  cases n <;> simp [__eo_gt] at hGuard h'
  case Numeral i =>
    cases hPos : native_zlt (-1 : native_Int) i <;>
      simp [__eo_requires, __eo_gt, native_ite, native_teq, native_not,
        SmtEval.native_not, hPos] at h'
    have hi : (0 : native_Int) <= i := by
      have hLt : (-1 : native_Int) < i := by
        simpa [SmtEval.native_zlt] using hPos
      have hStep : (-1 : native_Int) + 1 <= i := (Int.add_one_le_iff).2 hLt
      simpa using hStep
    exact ⟨i, rfl, by simpa [SmtEval.native_zleq] using hi, h'.symm⟩

theorem bv_nego_min_type_inv (n w : Term) :
    __eo_typeof (bvNegoMin n) = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ i, n = Term.Numeral i ∧ native_zleq 0 i = true ∧
      w = Term.Numeral (native_zplus 1 i) := by
  intro hTy
  unfold bvNegoMin at hTy
  change __eo_typeof_concat
      (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
      (__eo_typeof_concat
        (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0)))
        (__eo_typeof (Term.Binary 0 0))) =
    Term.Apply (Term.UOp UserOp.BitVec) w at hTy
  have hOneTy :
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    native_decide
  have hEmptyTy :
      __eo_typeof (Term.Binary 0 0) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0) := by
    rfl
  rw [hOneTy, hEmptyTy] at hTy
  rcases concat_type_bitvec_inv _ _ _ hTy with
    ⟨a, b, hA, hInnerTy, hAddOuter⟩
  cases hA
  rcases concat_type_bitvec_inv _ _ _ hInnerTy with
    ⟨c, d, hAt0Ty, hD, hAddInner⟩
  cases hD
  change __eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int) =
    Term.Apply (Term.UOp UserOp.BitVec) c at hAt0Ty
  have hNNe : n ≠ Term.Stuck := by
    intro hN
    subst n
    change __eo_typeof_int_to_bv Term.Stuck Term.Stuck (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) c at hAt0Ty
    simp [__eo_typeof_int_to_bv] at hAt0Ty
  have hNTy : __eo_typeof n = Term.UOp UserOp.Int := by
    cases hNT : __eo_typeof n <;>
      simp [__eo_typeof_int_to_bv, hNNe, hNT] at hAt0Ty ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_int_to_bv, hNNe, hNT] at hAt0Ty ⊢
  rcases at_bv_type_bitvec_inv n c hNNe hNTy hAt0Ty with
    ⟨i, hN, hNonneg, hC⟩
  subst n
  subst c
  have hB : b = Term.Numeral i := by
    simp [__eo_add, SmtEval.native_zplus] at hAddInner
    exact hAddInner.symm
  subst b
  refine ⟨i, rfl, hNonneg, ?_⟩
  simp [__eo_add, SmtEval.native_zplus] at hAddOuter
  exact hAddOuter.symm

private theorem eo_typeof_eq_bool_left_ne_stuck (A B : Term) :
    __eo_typeof_eq A B = Term.Bool -> A ≠ Term.Stuck := by
  intro h hA
  subst A
  simp [__eo_typeof_eq] at h

private theorem typeof_bvnego_ne_stuck_inv (A : Term) :
    __eo_typeof_bvnego A ≠ Term.Stuck ->
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w := by
  intro h
  cases A <;> try simp [__eo_typeof_bvnego] at h
  case Apply f w =>
    cases f <;> try simp [__eo_typeof_bvnego] at h
    case UOp op =>
      cases op <;> try simp [__eo_typeof_bvnego] at h
      case BitVec => exact ⟨w, rfl⟩

theorem smt_bitvec_type_of_eo_bitvec_type_with_width
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
    cases hNonneg : native_zleq 0 n <;>
      simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hXTrans hSmtType)

theorem smt_typeof_bv_const
    (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral k))) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro hNonneg
  change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral k)) =
    SmtType.BitVec (native_int_to_nat n)
  have hk : __smtx_typeof (SmtTerm.Numeral k) = SmtType.Int := by
    rw [__smtx_typeof.eq_def]
  rw [typeof_int_to_bv_eq, hk]
  simp [__smtx_typeof_int_to_bv, native_ite, hNonneg]

theorem eval_bv_const
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
  simp [__smtx_model_eval, __smtx_model_eval_int_to_bv]

theorem native_nat_to_int_int_to_nat_eq
    (n : native_Int) :
    native_zleq 0 n = true ->
    native_nat_to_int (native_int_to_nat n) = n := by
  intro hNonneg
  have hnNonneg : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
    Int.toNat_of_nonneg hnNonneg
  simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem native_int_to_nat_one_plus
    (i : native_Int) :
    native_zleq 0 i = true ->
    native_int_to_nat (native_zplus 1 i) =
      native_int_to_nat 1 + native_int_to_nat i := by
  intro hi
  have hi0 : (0 : native_Int) <= i := by
    simpa [SmtEval.native_zleq] using hi
  simp [native_int_to_nat, SmtEval.native_zplus]
  exact Int.toNat_add (by decide) hi0

theorem smt_typeof_bv_nego_min (i : native_Int) :
    native_zleq 0 i = true ->
    __smtx_typeof (__eo_to_smt (bvNegoMin (Term.Numeral i))) =
      SmtType.BitVec (native_int_to_nat (native_zplus 1 i)) := by
  intro hi
  unfold bvNegoMin
  change __smtx_typeof
      (SmtTerm.concat
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
        (SmtTerm.concat
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 0)))
          (SmtTerm.Binary 0 0))) =
    SmtType.BitVec (native_int_to_nat (native_zplus 1 i))
  rw [typeof_concat_eq, typeof_concat_eq]
  have hOneTy : __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1))) =
      SmtType.BitVec (native_int_to_nat 1) :=
    smt_typeof_bv_const 1 1 (by decide)
  have hZeroTy : __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 0))) =
      SmtType.BitVec (native_int_to_nat i) :=
    smt_typeof_bv_const 0 i hi
  have hEmptyTy : __smtx_typeof (SmtTerm.Binary 0 0) =
      SmtType.BitVec (native_int_to_nat 0) := by
    native_decide
  rw [hOneTy, hZeroTy, hEmptyTy]
  have hRoundI := native_nat_to_int_int_to_nat_eq i hi
  have hRound0 : native_nat_to_int (native_int_to_nat 0) = (0 : native_Int) := by
    native_decide
  have hRound1 : native_nat_to_int (native_int_to_nat 1) = (1 : native_Int) := by
    native_decide
  have hWidth := native_int_to_nat_one_plus i hi
  simp [__smtx_typeof_concat, hRoundI, hRound0, hRound1, hWidth,
    SmtEval.native_zplus]

private theorem smtx_eval_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.concat x y) =
      __smtx_model_eval_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_int_pow2_succ_pred
    {w : native_Int} (hwpos : 0 < w) :
    native_int_pow2 w = 2 * native_int_pow2 (w - 1) := by
  have hw0 : 0 <= w := Int.le_of_lt hwpos
  have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
  have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
  have hnotW : ¬ w < 0 := Int.not_lt_of_ge hw0
  have hnotP : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
  have hNat : w.toNat = (w - 1).toNat + 1 := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.natCast_one]
    rw [Int.toNat_of_nonneg hw0, Int.toNat_of_nonneg hwp0]
    omega
  rw [native_int_pow2, native_int_pow2, native_zexp_total,
    native_zexp_total]
  simp [hnotW, hnotP]
  rw [hNat]
  have hSub : (w - 1).toNat + 1 - 1 = (w - 1).toNat :=
    Nat.add_sub_cancel (w - 1).toNat 1
  rw [hSub]
  rw [← Nat.succ_eq_add_one]
  rw [Int.pow_succ]
  rw [Int.mul_comm]

private theorem native_int_pow2_pos_of_nonneg
    {w : native_Int} (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

theorem native_mod_zero_pow2
    {w : native_Int} (hw : native_zleq 0 w = true) :
    native_mod_total 0 (native_int_pow2 w) = 0 := by
  have hw0 : (0 : native_Int) <= w := by
    simpa [SmtEval.native_zleq] using hw
  have hPowPos : 0 < native_int_pow2 w := native_int_pow2_pos_of_nonneg hw0
  change (0 : Int) % native_int_pow2 w = 0
  exact Int.emod_eq_of_lt (by decide : (0 : Int) <= 0) hPowPos

private theorem native_mod_pow2_self_in_succ
    {i : native_Int} (hi : native_zleq 0 i = true) :
    native_mod_total (native_int_pow2 i) (native_int_pow2 (native_zplus 1 i)) =
      native_int_pow2 i := by
  have hi0 : (0 : native_Int) <= i := by
    simpa [SmtEval.native_zleq] using hi
  have hPowPos : 0 < native_int_pow2 i := native_int_pow2_pos_of_nonneg hi0
  have hSuccPos : 0 < native_zplus 1 i := by
    simpa [SmtEval.native_zplus] using
      Int.add_pos_of_pos_of_nonneg (by decide : (0 : Int) < 1) hi0
  have hPowSucc : native_int_pow2 (native_zplus 1 i) =
      2 * native_int_pow2 i := by
    have h := native_int_pow2_succ_pred (w := native_zplus 1 i) hSuccPos
    have hSub : (1 + i) - 1 = i := by
      rw [Int.add_comm 1 i]
      exact Int.add_sub_cancel i 1
    simpa [SmtEval.native_zplus, hSub] using h
  have hLt : native_int_pow2 i < native_int_pow2 (native_zplus 1 i) := by
    rw [hPowSucc]
    rw [Int.two_mul]
    exact Int.lt_add_of_pos_right (native_int_pow2 i) hPowPos
  change native_int_pow2 i % native_int_pow2 (native_zplus 1 i) =
    native_int_pow2 i
  exact Int.emod_eq_of_lt (Int.le_of_lt hPowPos) hLt

theorem eval_bv_nego_min
    (M : SmtModel) (i : native_Int) :
    native_zleq 0 i = true ->
    __smtx_model_eval M (__eo_to_smt (bvNegoMin (Term.Numeral i))) =
      SmtValue.Binary (native_zplus 1 i) (native_int_pow2 i) := by
  intro hi
  unfold bvNegoMin
  change __smtx_model_eval M
      (SmtTerm.concat
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)))
        (SmtTerm.concat
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) (Term.Numeral 0)))
          (SmtTerm.Binary 0 0))) =
    SmtValue.Binary (native_zplus 1 i) (native_int_pow2 i)
  rw [smtx_eval_concat_term_eq, smtx_eval_concat_term_eq]
  have hOne := eval_bv_const M 1 1 (by decide)
  have hZero := eval_bv_const M 0 i hi
  have hEmpty : __smtx_model_eval M (SmtTerm.Binary 0 0) =
      SmtValue.Binary 0 0 := by
    simp only [__smtx_model_eval]
  rw [hOne, hZero, hEmpty]
  have hOneMod : native_mod_total 1 (native_int_pow2 1) = 1 := by
    native_decide
  have hZeroMod : native_mod_total 0 (native_int_pow2 i) = 0 :=
    native_mod_zero_pow2 hi
  have hInnerZero : native_mod_total 0
      (native_int_pow2 (native_zplus i 0)) = 0 := by
    have hi' : native_zleq 0 (native_zplus i 0) = true := by
      simpa [SmtEval.native_zplus] using hi
    exact native_mod_zero_pow2 hi'
  have hPowMod := native_mod_pow2_self_in_succ hi
  have hPowMod' :
      native_mod_total (native_int_pow2 i) (native_int_pow2 (1 + i)) =
        native_int_pow2 i := by
    simpa [SmtEval.native_zplus] using hPowMod
  simp [__smtx_model_eval_concat, hOneMod, hZeroMod, hInnerZero,
    hPowMod', SmtEval.native_zplus, SmtEval.native_zmult,
    native_binary_concat]

theorem smt_typeof_bvnego (a : SmtTerm) (n : native_Int) :
    __smtx_typeof a = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (SmtTerm.bvnego a) = SmtType.Bool := by
  intro h
  rw [__smtx_typeof.eq_72]
  simp [__smtx_typeof_bv_op_1_ret, h]

theorem typeof_args_of_bv_nego_term_bool (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvNegoTerm x n) = Term.Bool ->
    ∃ i,
      n = Term.Numeral i ∧
      native_zleq 0 i = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_zplus 1 i)) ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat (native_zplus 1 i)) := by
  intro hXTrans hTy
  change __eo_typeof_eq
      (__eo_typeof_bvnego (__eo_typeof x))
      (__eo_typeof_eq (__eo_typeof x) (__eo_typeof (bvNegoMin n))) =
    Term.Bool at hTy
  have hLeftNN :
      __eo_typeof_bvnego (__eo_typeof x) ≠ Term.Stuck :=
    eo_typeof_eq_bool_left_ne_stuck _ _ hTy
  rcases typeof_bvnego_ne_stuck_inv (__eo_typeof x) hLeftNN with ⟨w, hXTy⟩
  have hInnerBool :
      __eo_typeof_eq (__eo_typeof x) (__eo_typeof (bvNegoMin n)) =
        Term.Bool := by
    have hEq := support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof_bvnego (__eo_typeof x))
      (__eo_typeof_eq (__eo_typeof x) (__eo_typeof (bvNegoMin n))) hTy
    rw [hXTy] at hEq
    simp [__eo_typeof_bvnego] at hEq
    rw [hXTy]
    exact hEq.symm
  have hTypeEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof x) (__eo_typeof (bvNegoMin n)) hInnerBool
  have hMinTy : __eo_typeof (bvNegoMin n) =
      Term.Apply (Term.UOp UserOp.BitVec) w := by
    rw [← hTypeEq, hXTy]
  rcases bv_nego_min_type_inv n w hMinTy with ⟨i, hN, hNonneg, hW⟩
  subst n
  subst w
  have hXTy' :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus 1 i)) := by
    simpa using hXTy
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x
      (Term.Numeral (native_zplus 1 i)) hXTrans hXTy' with
    ⟨j, hJ, _hWidthNonneg, hXSmtTy⟩
  cases hJ
  exact ⟨i, rfl, hNonneg, hXTy', hXSmtTy⟩

theorem typed_bv_nego_term (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvNegoTerm x n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvNegoTerm x n) := by
  intro hXTrans hResultTy
  rcases typeof_args_of_bv_nego_term_bool x n hXTrans hResultTy with
    ⟨i, hN, hNonneg, _hXTy, hXSmtTy⟩
  subst n
  have hLhsBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.UOp UserOp.bvnego) x) := by
    change __smtx_typeof (SmtTerm.bvnego (__eo_to_smt x)) = SmtType.Bool
    exact smt_typeof_bvnego (__eo_to_smt x) (native_zplus 1 i) hXSmtTy
  have hMinSmtTy := smt_typeof_bv_nego_min i hNonneg
  have hRhsBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
        (bvNegoMin (Term.Numeral i))) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type x (bvNegoMin (Term.Numeral i))
      (hXSmtTy.trans hMinSmtTy.symm)
      (by
        rw [hXSmtTy]
        intro h
        cases h)
  unfold bvNegoTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp UserOp.bvnego) x)
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
      (bvNegoMin (Term.Numeral i)))
    (hLhsBool.trans hRhsBool.symm)
    (by
      rw [hLhsBool]
      intro h
      cases h)

private theorem smtx_eval_bvnego_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvnego x) =
      __smtx_model_eval_bvnego (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem eval_bvnego_matches_eq_min
    (M : SmtModel) (hM : model_wf M) (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvNegoTerm x n) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnego) x)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) (bvNegoMin n))) := by
  intro hXTrans hResultTy
  rcases typeof_args_of_bv_nego_term_bool x n hXTrans hResultTy with
    ⟨i, hN, hNonneg, _hXTy, hXSmtTy⟩
  subst n
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat (native_zplus 1 i)) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by
          simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
            using hXTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX⟩
  have hWidthNonneg : native_zleq 0 (native_zplus 1 i) = true := by
    have hi0 : (0 : native_Int) <= i := by
      simpa [SmtEval.native_zleq] using hNonneg
    have hpos : (0 : native_Int) < native_zplus 1 i := by
      simpa [SmtEval.native_zplus] using
        Int.add_pos_of_pos_of_nonneg (by decide : (0 : Int) < 1) hi0
    have hle : (0 : native_Int) <= native_zplus 1 i := Int.le_of_lt hpos
    simpa [SmtEval.native_zleq] using hle
  have hWidthRound :
      native_nat_to_int (native_int_to_nat (native_zplus 1 i)) =
        native_zplus 1 i :=
    native_nat_to_int_int_to_nat_eq (native_zplus 1 i) hWidthNonneg
  rw [hWidthRound] at hEvalX
  change __smtx_model_eval M (SmtTerm.bvnego (__eo_to_smt x)) =
    __smtx_model_eval M
      (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (bvNegoMin (Term.Numeral i))))
  rw [smtx_eval_bvnego_term_eq, smtx_eval_eq_term_eq, hEvalX,
    eval_bv_nego_min M i hNonneg]
  have hSub : native_zplus (native_zplus 1 i) (native_zneg 1) = i := by
    simp [SmtEval.native_zplus, SmtEval.native_zneg]
    rw [Int.add_comm 1 i]
    exact Int.add_sub_cancel i 1
  simp [__smtx_model_eval_bvnego, __smtx_model_eval_eq, native_veq,
    hSub, SmtEval.native_zeq]

theorem facts_bv_nego_term
    (M : SmtModel) (hM : model_wf M) (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvNegoTerm x n) = Term.Bool ->
    eo_interprets M (bvNegoTerm x n) true := by
  intro hXTrans hResultTy
  have hTermBool := typed_bv_nego_term x n hXTrans hResultTy
  unfold bvNegoTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvNegoTerm] using hTermBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnego) x)))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) (bvNegoMin n))))
    rw [eval_bvnego_matches_eq_min M hM x n hXTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _
