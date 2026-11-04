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

private abbrev intToBvTerm (w t : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv w) t

private abbrev ubvToIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.ubv_to_int) t

private abbrev zeroBvTerm (n : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv n) (Term.Numeral 0)

private abbrev concatTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b

private abbrev ufBv2natInt2bvExtendConclusion (w t n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (intToBvTerm w (ubvToIntTerm t)))
    (concatTerm (zeroBvTerm n) (concatTerm t (Term.Binary 0 0)))

private abbrev ufBv2natInt2bvExtendType (w t n : Term) : Term :=
  __eo_typeof_eq
    (__eo_typeof_int_to_bv (__eo_typeof w) w
      (__eo_typeof__at_bvsize (__eo_typeof t)))
    (__eo_typeof_concat
      (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))
      (__eo_typeof_concat (__eo_typeof t)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0))))

private theorem typeof_ufBv2natInt2bvExtendConclusion_eq (w t n : Term) :
    __eo_typeof (ufBv2natInt2bvExtendConclusion w t n) =
      ufBv2natInt2bvExtendType w t n := by
  rfl

private theorem prog_uf_bv2nat_int2bv_extend_eq
    (w1 t1 n1 lw2 lt2 ln2 lw3 lt3 : Term)
    (hW : w1 ≠ Term.Stuck) (hT : t1 ≠ Term.Stuck) (hN : n1 ≠ Term.Stuck) :
    __eo_prog_uf_bv2nat_int2bv_extend w1 t1 n1
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.gt) lw2)
              (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
          (Term.Boolean true)))
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) ln2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg) lw3)
            (Term.Apply (Term.UOp UserOp._at_bvsize) lt3)))) =
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq w1 lw2) (__eo_eq t1 lt2))
              (__eo_eq n1 ln2))
            (__eo_eq w1 lw3))
          (__eo_eq t1 lt3))
        (Term.Boolean true) (ufBv2natInt2bvExtendConclusion w1 t1 n1) := by
  cases w1 <;> cases t1 <;> cases n1 <;>
    simp [__eo_prog_uf_bv2nat_int2bv_extend, ufBv2natInt2bvExtendConclusion,
      intToBvTerm, ubvToIntTerm, zeroBvTerm, concatTerm] at hW hT hN ⊢

private theorem args_ne_stuck_of_prog_not_stuck
    (w1 t1 n1 p1 p2 : Term)
    (h : __eo_prog_uf_bv2nat_int2bv_extend w1 t1 n1
      (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    w1 ≠ Term.Stuck ∧ t1 ≠ Term.Stuck ∧ n1 ≠ Term.Stuck := by
  constructor
  · intro hW
    subst w1
    simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
  constructor
  · intro hT
    subst t1
    cases w1 <;> simp [__eo_prog_uf_bv2nat_int2bv_extend] at h
  · intro hN
    subst n1
    cases w1 <;> cases t1 <;> simp [__eo_prog_uf_bv2nat_int2bv_extend] at h

private theorem shape_of_prog_uf_bv2nat_int2bv_extend_not_stuck
    (w1 t1 n1 p1 p2 : Term)
    (hW : w1 ≠ Term.Stuck) (hT : t1 ≠ Term.Stuck) (hN : n1 ≠ Term.Stuck)
    (h : __eo_prog_uf_bv2nat_int2bv_extend w1 t1 n1
      (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    ∃ lw2 lt2 ln2 lw3 lt3 : Term,
      p1 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.gt) lw2)
              (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
          (Term.Boolean true) ∧
      p2 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) ln2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg) lw3)
            (Term.Apply (Term.UOp UserOp._at_bvsize) lt3)) := by
  unfold __eo_prog_uf_bv2nat_int2bv_extend at h
  split at h
  · exact absurd rfl hW
  · exact absurd rfl hT
  · exact absurd rfl hN
  · rename_i _ _ _ _ _ _ _ _ lw2 lt2 ln2 lw3 lt3 _ _ _ heq1 heq2
    injection heq1 with heq1
    injection heq2 with heq2
    exact ⟨lw2, lt2, ln2, lw3, lt3, heq1, heq2⟩
  · exact absurd rfl h

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  exact support_eq_of_eo_eq_true x y h

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem eo_and_eq_true_left {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true := by
  cases x <;> cases y <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean b c =>
    cases b <;> cases c <;> simp [__eo_and, native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    unfold __eo_requires at h
    cases hEq : native_teq (Term.Numeral w1) (Term.Numeral w2) <;>
      simp [native_ite, hEq] at h
    cases hOk : native_not (native_teq (Term.Numeral w1) Term.Stuck) <;>
      simp [native_ite, hOk] at h

private theorem eo_and_eq_true_right {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    y = Term.Boolean true := by
  cases x <;> cases y <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean b c =>
    cases b <;> cases c <;> simp [__eo_and, native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    unfold __eo_requires at h
    cases hEq : native_teq (Term.Numeral w1) (Term.Numeral w2) <;>
      simp [native_ite, hEq] at h
    cases hOk : native_not (native_teq (Term.Numeral w1) Term.Stuck) <;>
      simp [native_ite, hOk] at h

private theorem eqs_of_requires5_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 B : Term) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
              (__eo_eq x3 y3))
            (__eo_eq x4 y4))
          (__eo_eq x5 y5))
        (Term.Boolean true) B ≠ Term.Stuck ->
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 ∧ y5 = x5 := by
  intro hProg
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
              (__eo_eq x3 y3))
            (__eo_eq x4 y4))
          (__eo_eq x5 y5) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hProg
  have h1234 : __eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) = Term.Boolean true :=
    eo_and_eq_true_left hGuard
  have h5 : __eo_eq x5 y5 = Term.Boolean true :=
    eo_and_eq_true_right hGuard
  have h123 : __eo_and
          (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
          (__eo_eq x3 y3) = Term.Boolean true :=
    eo_and_eq_true_left h1234
  have h4 : __eo_eq x4 y4 = Term.Boolean true :=
    eo_and_eq_true_right h1234
  have h12 : __eo_and (__eo_eq x1 y1) (__eo_eq x2 y2) = Term.Boolean true :=
    eo_and_eq_true_left h123
  have h3 : __eo_eq x3 y3 = Term.Boolean true :=
    eo_and_eq_true_right h123
  have h1 : __eo_eq x1 y1 = Term.Boolean true :=
    eo_and_eq_true_left h12
  have h2 : __eo_eq x2 y2 = Term.Boolean true :=
    eo_and_eq_true_right h12
  exact ⟨eq_of_eo_eq_true x1 y1 h1, eq_of_eo_eq_true x2 y2 h2,
    eq_of_eo_eq_true x3 y3 h3, eq_of_eo_eq_true x4 y4 h4,
    eq_of_eo_eq_true x5 y5 h5⟩

private theorem requires5_and_eq_self_true_body
    (w t n body : Term)
    (hWNotStuck : w ≠ Term.Stuck)
    (hTNotStuck : t ≠ Term.Stuck)
    (hNNotStuck : n ≠ Term.Stuck) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq w w) (__eo_eq t t))
              (__eo_eq n n))
            (__eo_eq w w))
          (__eo_eq t t))
        (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and, eo_eq_self_true_of_ne_stuck w hWNotStuck,
    eo_eq_self_true_of_ne_stuck t hTNotStuck,
    eo_eq_self_true_of_ne_stuck n hNNotStuck, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

private theorem typeof_int_to_bv_stuck_of_width_ty_ne_int (A w B : Term)
    (hA : A ≠ Term.UOp UserOp.Int) :
    __eo_typeof_int_to_bv A w B = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

private theorem int_to_bv_type_bitvec_inv (A w m : Term)
    (h : __eo_typeof_int_to_bv A w (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    A = Term.UOp UserOp.Int ∧
      ∃ n, w = Term.Numeral n ∧ native_zlt (-1 : native_Int) n = true ∧
        m = Term.Numeral n := by
  by_cases hA : A = Term.UOp UserOp.Int
  · subst A
    refine ⟨rfl, ?_⟩
    cases hw : w <;> rw [hw] at h <;>
      first
      | (rename_i n
         have hRed :
             __eo_typeof_int_to_bv (Term.UOp UserOp.Int) (Term.Numeral n)
                 (Term.UOp UserOp.Int) =
               native_ite (native_zlt (-1 : native_Int) n)
                 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n)) Term.Stuck := by
           simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
             native_teq, native_not, SmtEval.native_not]
         rw [hRed] at h
         cases hPos : native_zlt (-1 : native_Int) n <;>
           simp [native_ite, hPos] at h
         exact ⟨n, rfl, hPos, h.symm⟩)
      | (exfalso
         simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
           native_teq, native_not, SmtEval.native_not] at h)
  · exfalso
    rw [typeof_int_to_bv_stuck_of_width_ty_ne_int A w (Term.UOp UserOp.Int) hA] at h
    simp at h

private theorem typeof_eq_bool_inv (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    B = A := by
  exact (support_eo_typeof_eq_bool_operands_eq A B h).symm

private theorem at_bv_type_bitvec_inv (n m : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (h : __eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    ∃ i, n = Term.Numeral i ∧ native_zleq 0 i = true ∧ m = Term.Numeral i := by
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

private theorem concat_type_ne_stuck_inv (A B : Term)
    (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    ∃ a b, A = Term.Apply (Term.UOp UserOp.BitVec) a ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) b ∧
      __eo_typeof_concat A B =
        Term.Apply (Term.UOp UserOp.BitVec) (__eo_add a b) := by
  cases A with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_concat] at h
          case BitVec =>
            cases B with
            | Apply g b =>
                cases g with
                | UOp op2 =>
                    cases op2 <;> simp [__eo_typeof_concat] at h
                    case BitVec =>
                      refine ⟨a, b, rfl, rfl, ?_⟩
                      cases hAdd : __eo_add a b <;>
                        simp [__eo_typeof_concat, __eo_mk_apply, hAdd] at h ⊢
                | _ => simp [__eo_typeof_concat] at h
            | _ => simp [__eo_typeof_concat] at h
      | _ => simp [__eo_typeof_concat] at h
  | _ => simp [__eo_typeof_concat] at h

private theorem typeof_args_of_extend_conclusion_bool (w t n : Term) :
    __eo_typeof (ufBv2natInt2bvExtendConclusion w t n) = Term.Bool ->
    ∃ wi ti ni,
      w = Term.Numeral wi ∧ n = Term.Numeral ni ∧
      native_zleq 0 wi = true ∧ native_zleq 0 ni = true ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral ti) ∧
      wi = native_zplus ni ti := by
  intro hTy
  rw [typeof_ufBv2natInt2bvExtendConclusion_eq] at hTy
  simp only [ufBv2natInt2bvExtendType] at hTy
  have hEqTy :
      __eo_typeof_concat
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))
          (__eo_typeof_concat (__eo_typeof t)
            (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0))) =
        __eo_typeof_int_to_bv (__eo_typeof w) w
          (__eo_typeof__at_bvsize (__eo_typeof t)) :=
    typeof_eq_bool_inv _ _ hTy
  let lhs :=
    __eo_typeof_int_to_bv (__eo_typeof w) w
      (__eo_typeof__at_bvsize (__eo_typeof t))
  let rhs :=
    __eo_typeof_concat
      (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))
      (__eo_typeof_concat (__eo_typeof t)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)))
  have hEqTy' : rhs = lhs := by
    simpa [lhs, rhs] using hEqTy
  have hRhsNN : rhs ≠ Term.Stuck := by
    intro hRhs
    have hLhs : lhs = Term.Stuck := hEqTy'.symm.trans hRhs
    have hTy' := hTy
    change __eo_typeof_eq lhs rhs = Term.Bool at hTy'
    rw [hRhs, hLhs] at hTy'
    simp [__eo_typeof_eq] at hTy'
  rcases concat_type_ne_stuck_inv _ _ hRhsNN with
    ⟨nm, innerM, hZeroTy, hInnerTy, hRhsEq⟩
  have hLhsBv :
      lhs = Term.Apply (Term.UOp UserOp.BitVec) (__eo_add nm innerM) := by
    have hRhsEq' : rhs = Term.Apply (Term.UOp UserOp.BitVec) (__eo_add nm innerM) := by
      simpa [rhs] using hRhsEq
    exact hEqTy'.symm.trans hRhsEq'
  have hBvsizeInt : __eo_typeof__at_bvsize (__eo_typeof t) = Term.UOp UserOp.Int := by
    have hInnerNN :
        __eo_typeof_concat (__eo_typeof t)
            (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) ≠
          Term.Stuck := by
      rw [hInnerTy]
      intro hc
      cases hc
    rcases concat_type_ne_stuck_inv _ _ hInnerNN with
      ⟨tm, z, hTTy, _hZeroWidth, _hInnerEq⟩
    rw [hTTy]
    rfl
  change __eo_typeof_int_to_bv (__eo_typeof w) w
      (__eo_typeof__at_bvsize (__eo_typeof t)) =
    Term.Apply (Term.UOp UserOp.BitVec) (__eo_add nm innerM) at hLhsBv
  rw [hBvsizeInt] at hLhsBv
  rcases int_to_bv_type_bitvec_inv (__eo_typeof w) w (__eo_add nm innerM) hLhsBv with
    ⟨_hWTy, wi, hW, hWiPos, hWm⟩
  subst w
  have hWNonneg : native_zleq 0 wi = true := by
    have hLt : (-1 : native_Int) < wi := by
      simpa [SmtEval.native_zlt] using hWiPos
    have hStep : (-1 : native_Int) + 1 <= wi :=
      (Int.add_one_le_iff).2 hLt
    simpa [SmtEval.native_zleq] using hStep
  have hNNe : n ≠ Term.Stuck := by
    intro hN
    subst n
    simp [__eo_typeof_int_to_bv] at hZeroTy
  have hNTy : __eo_typeof n = Term.UOp UserOp.Int := by
    cases hNT : __eo_typeof n <;>
      simp [__eo_typeof_int_to_bv, hNNe, hNT] at hZeroTy ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_int_to_bv, hNNe, hNT] at hZeroTy ⊢
  rcases at_bv_type_bitvec_inv n nm hNNe hNTy hZeroTy with
    ⟨ni, hN, hNiNonneg, hNm⟩
  subst n
  subst nm
  rcases concat_type_bitvec_inv _ _ innerM hInnerTy with
    ⟨tm, z, hTTy, hZeroWidth, hInnerWidthEq⟩
  cases z <;> simp [__eo_add] at hInnerWidthEq hZeroWidth
  case Numeral zval =>
    subst zval
    cases tm <;> simp [__eo_add, SmtEval.native_zplus] at hInnerWidthEq
    case Numeral ti =>
      subst innerM
      simp [__eo_add, SmtEval.native_zplus] at hWm
      exact ⟨wi, ti, ni, rfl, rfl, hWNonneg, hNiNonneg, hTTy,
        hWm.symm⟩
    all_goals
      subst innerM
      simp [__eo_add] at hWm

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

private theorem width_nat_to_int_eq
    (n : native_Int) (hNonneg : native_zleq 0 n = true) :
    native_nat_to_int (native_int_to_nat n) = n := by
  have hnNonneg : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
    Int.toNat_of_nonneg hnNonneg
  simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem smt_typeof_lhs_eq
    (wi ti : native_Int) (t : Term) :
    native_zleq 0 wi = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat ti) ->
    __smtx_typeof
        (__eo_to_smt (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))) =
      SmtType.BitVec (native_int_to_nat wi) := by
  intro hWiNonneg hTSmtTy
  change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral wi)
        (SmtTerm.ubv_to_int (__eo_to_smt t))) =
    SmtType.BitVec (native_int_to_nat wi)
  rw [smtx_typeof_int_to_bv_term_eq, smtx_typeof_ubv_to_int_term_eq]
  simp [__smtx_typeof_int_to_bv, __smtx_typeof_bv_op_1_ret, native_ite,
    hTSmtTy, hWiNonneg]

private theorem smt_typeof_bv_zero
    (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt (zeroBvTerm (Term.Numeral n))) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro hNonneg
  change __smtx_typeof (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral 0)) =
    SmtType.BitVec (native_int_to_nat n)
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary n (native_mod_total 0 (native_int_pow2 n))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total 0 (native_int_pow2 n))
            (native_mod_total
              (native_mod_total 0 (native_int_pow2 n))
              (native_int_pow2 n)) =
          true :=
      native_mod_total_canonical n 0
    simp [SmtEval.native_and, hNonneg, hMod, native_ite]
  simpa [native_ite, hNonneg] using
    TranslationProofs.smtx_typeof_binary_of_non_none n
      (native_mod_total 0 (native_int_pow2 n)) hNN

private theorem smt_typeof_concat_zero_right
    (t : Term) (ti : native_Int) :
    native_zleq 0 ti = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat ti) ->
    __smtx_typeof (__eo_to_smt (concatTerm t (Term.Binary 0 0))) =
      SmtType.BitVec (native_int_to_nat ti) := by
  intro hTiNonneg hTSmtTy
  change __smtx_typeof (SmtTerm.concat (__eo_to_smt t) (SmtTerm.Binary 0 0)) =
    SmtType.BitVec (native_int_to_nat ti)
  rw [__smtx_typeof.eq_def] <;> simp only
  have hBin0Ty : __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0 := by
    simp [__smtx_typeof, SmtEval.native_and, SmtEval.native_zleq,
      SmtEval.native_zeq, SmtEval.native_mod_total, SmtEval.native_int_pow2,
      SmtEval.native_zexp_total, native_ite, native_int_to_nat]
  rw [hTSmtTy, hBin0Ty]
  have hNatIntNat :
      native_int_to_nat (native_nat_to_int (native_int_to_nat ti)) =
        native_int_to_nat ti := by
    have hTiNonnegInt : (0 : native_Int) <= ti := by
      simpa [SmtEval.native_zleq] using hTiNonneg
    have hMax : max ti 0 = ti := Int.max_eq_left hTiNonnegInt
    simp [native_int_to_nat, native_nat_to_int, SmtEval.native_int_to_nat,
      SmtEval.native_nat_to_int, hMax]
  have hNatIntNat' :
      native_int_to_nat ((native_int_to_nat ti : native_Nat) : native_Int) =
        native_int_to_nat ti := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hNatIntNat
  simp [__smtx_typeof_concat, SmtEval.native_and, SmtEval.native_zleq,
    SmtEval.native_zeq, SmtEval.native_mod_total, SmtEval.native_int_pow2,
    SmtEval.native_zexp_total, width_nat_to_int_eq ti hTiNonneg,
    SmtEval.native_zplus, SmtEval.native_nat_to_int, native_nat_to_int,
    hNatIntNat, hNatIntNat']

private theorem smt_typeof_rhs_eq
    (wi ti ni : native_Int) (t : Term) :
    wi = native_zplus ni ti ->
    native_zleq 0 ni = true ->
    native_zleq 0 ti = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat ti) ->
    __smtx_typeof
        (__eo_to_smt
          (concatTerm (zeroBvTerm (Term.Numeral ni))
            (concatTerm t (Term.Binary 0 0)))) =
      SmtType.BitVec (native_int_to_nat wi) := by
  intro hWi hNiNonneg hTiNonneg hTSmtTy
  have hZeroTy := smt_typeof_bv_zero ni hNiNonneg
  have hInnerTy := smt_typeof_concat_zero_right t ti hTiNonneg hTSmtTy
  change __smtx_typeof
      (SmtTerm.concat
        (__eo_to_smt (zeroBvTerm (Term.Numeral ni)))
        (__eo_to_smt (concatTerm t (Term.Binary 0 0)))) =
    SmtType.BitVec (native_int_to_nat wi)
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hZeroTy, hInnerTy]
  simp [__smtx_typeof_concat, width_nat_to_int_eq ni hNiNonneg,
    width_nat_to_int_eq ti hTiNonneg, hWi]

private theorem typed_conclusion_impl
    (w t n : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (ufBv2natInt2bvExtendConclusion w t n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (ufBv2natInt2bvExtendConclusion w t n) := by
  intro hTTrans hResultTy
  rcases typeof_args_of_extend_conclusion_bool w t n hResultTy with
    ⟨wi, ti, ni, hW, hN, hWiNonneg, hNiNonneg, hTType, hWi⟩
  subst w
  subst n
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t (Term.Numeral ti)
      hTTrans hTType with
    ⟨ti', hTieq, hTiNonneg', hTSmtTy⟩
  injection hTieq with hti
  subst hti
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))) =
        SmtType.BitVec (native_int_to_nat wi) :=
    smt_typeof_lhs_eq wi ti t hWiNonneg hTSmtTy
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (concatTerm (zeroBvTerm (Term.Numeral ni))
              (concatTerm t (Term.Binary 0 0)))) =
        SmtType.BitVec (native_int_to_nat wi) :=
    smt_typeof_rhs_eq wi ti ni t hWi hNiNonneg hTiNonneg' hTSmtTy
  refine RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))
    (concatTerm (zeroBvTerm (Term.Numeral ni))
      (concatTerm t (Term.Binary 0 0)))
    ?_ ?_
  · rw [hLhsTy, hRhsTy]
  · rw [hLhsTy]
    intro hc
    cases hc

private theorem eval_lhs_extend
    (M : SmtModel) (hM : model_wf M)
    (wi ti ni : native_Int) (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    wi = native_zplus ni ti ->
    native_zleq 0 wi = true ->
    native_zleq 0 ni = true ->
    native_zleq 0 ti = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat ti) ->
    ∃ payload,
      __smtx_model_eval M
          (__eo_to_smt (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))) =
        SmtValue.Binary wi payload ∧
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary ti payload := by
  intro hTTrans hWi hWiNonneg hNiNonneg hTiNonneg hTSmtTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec (native_int_to_nat ti) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hTTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalT⟩
  rw [width_nat_to_int_eq ti hTiNonneg] at hEvalT
  have hCanonOrig :
      native_zeq payload (native_mod_total payload (native_int_pow2 ti)) = true :=
    bitvec_payload_canonical (by simpa [hEvalT] using hEvalTy)
  have hCanonNew :
      native_zeq payload (native_mod_total payload (native_int_pow2 wi)) = true := by
    have hCanon :=
      bitvec_payload_canonical_zero_extend
        (i := ni) (w := ti) (n := payload)
        hNiNonneg hTiNonneg hCanonOrig
    simpa [hWi] using hCanon
  have hPayloadMod :
      native_mod_total payload (native_int_pow2 wi) = payload := by
    have hEq : payload = native_mod_total payload (native_int_pow2 wi) := by
      simpa [SmtEval.native_zeq] using hCanonNew
    exact hEq.symm
  refine ⟨payload, ?_, hEvalT⟩
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral wi)
        (SmtTerm.ubv_to_int (__eo_to_smt t))) =
    SmtValue.Binary wi payload
  rw [smtx_eval_int_to_bv_term_eq, smtx_eval_ubv_to_int_term_eq, hEvalT]
  have hEvalW :
      __smtx_model_eval M (SmtTerm.Numeral wi) = SmtValue.Numeral wi := by
    rw [__smtx_model_eval.eq_2]
  rw [hEvalW]
  simp [__smtx_model_eval_ubv_to_int, __smtx_model_eval_int_to_bv, hPayloadMod]

private theorem eval_rhs_extend
    (M : SmtModel) (hM : model_wf M)
    (wi ti ni payload : native_Int) (t : Term) :
    wi = native_zplus ni ti ->
    native_zleq 0 ni = true ->
    native_zleq 0 ti = true ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary ti payload ->
    __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
      SmtType.BitVec (native_int_to_nat ti) ->
    __smtx_model_eval M
        (__eo_to_smt
          (concatTerm (zeroBvTerm (Term.Numeral ni))
            (concatTerm t (Term.Binary 0 0)))) =
      SmtValue.Binary wi payload := by
  intro hWi hNiNonneg hTiNonneg hEvalT hEvalTy
  have hCanonOrig :
      native_zeq payload (native_mod_total payload (native_int_pow2 ti)) = true :=
    bitvec_payload_canonical (by simpa [hEvalT] using hEvalTy)
  have hCanonNew :
      native_zeq payload
          (native_mod_total payload (native_int_pow2 (native_zplus ni ti))) =
        true :=
    bitvec_payload_canonical_zero_extend
      (i := ni) (w := ti) (n := payload) hNiNonneg hTiNonneg hCanonOrig
  have hPayloadModOrig :
      native_mod_total payload (native_int_pow2 ti) = payload := by
    have hEq : payload = native_mod_total payload (native_int_pow2 ti) := by
      simpa [SmtEval.native_zeq] using hCanonOrig
    exact hEq.symm
  have hPayloadModNew :
      native_mod_total payload (native_int_pow2 (native_zplus ni ti)) = payload := by
    have hEq :
        payload =
          native_mod_total payload (native_int_pow2 (native_zplus ni ti)) := by
      simpa [SmtEval.native_zeq] using hCanonNew
    exact hEq.symm
  have hZeroPayload :
      native_mod_total 0 (native_int_pow2 ni) = 0 := by
    simp [SmtEval.native_mod_total]
  change __smtx_model_eval M
      (SmtTerm.concat
        (__eo_to_smt (zeroBvTerm (Term.Numeral ni)))
        (SmtTerm.concat (__eo_to_smt t) (SmtTerm.Binary 0 0))) =
    SmtValue.Binary wi payload
  rw [show __smtx_model_eval M
        (SmtTerm.concat
          (__eo_to_smt (zeroBvTerm (Term.Numeral ni)))
          (SmtTerm.concat (__eo_to_smt t) (SmtTerm.Binary 0 0))) =
      __smtx_model_eval_concat
        (__smtx_model_eval M (__eo_to_smt (zeroBvTerm (Term.Numeral ni))))
        (__smtx_model_eval M
          (SmtTerm.concat (__eo_to_smt t) (SmtTerm.Binary 0 0))) by
        rw [__smtx_model_eval.eq_def] <;> simp only]
  have hZeroEval :
      __smtx_model_eval M (__eo_to_smt (zeroBvTerm (Term.Numeral ni))) =
        SmtValue.Binary ni 0 := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral ni) (SmtTerm.Numeral 0)) =
      SmtValue.Binary ni 0
    simp [native_ite, hNiNonneg, hZeroPayload]
  have hInnerEval :
      __smtx_model_eval M
          (SmtTerm.concat (__eo_to_smt t) (SmtTerm.Binary 0 0)) =
        SmtValue.Binary ti payload := by
    rw [show __smtx_model_eval M
          (SmtTerm.concat (__eo_to_smt t) (SmtTerm.Binary 0 0)) =
        __smtx_model_eval_concat
          (__smtx_model_eval M (__eo_to_smt t))
          (__smtx_model_eval M (SmtTerm.Binary 0 0)) by
          rw [__smtx_model_eval.eq_def] <;> simp only]
    rw [hEvalT]
    have hBin0Eval :
        __smtx_model_eval M (SmtTerm.Binary 0 0) = SmtValue.Binary 0 0 := by
      rw [__smtx_model_eval.eq_5]
    rw [hBin0Eval]
    change
      SmtValue.Binary (native_zplus ti 0)
          (native_mod_total (native_binary_concat ti payload 0 0)
            (native_int_pow2 (native_zplus ti 0))) =
        SmtValue.Binary ti payload
    have hWidth : native_zplus ti 0 = ti := by
      simp [SmtEval.native_zplus]
    have hConcat : native_binary_concat ti payload 0 0 = payload := by
      simp [SmtEval.native_binary_concat, SmtEval.native_zplus,
        SmtEval.native_zmult, SmtEval.native_int_pow2, SmtEval.native_zexp_total]
    rw [hWidth, hConcat, hPayloadModOrig]
  rw [hZeroEval, hInnerEval]
  change
    SmtValue.Binary (native_zplus ni ti)
        (native_mod_total (native_binary_concat ni 0 ti payload)
          (native_int_pow2 (native_zplus ni ti))) =
      SmtValue.Binary wi payload
  have hConcat : native_binary_concat ni 0 ti payload = payload := by
    simp [SmtEval.native_binary_concat, SmtEval.native_zmult,
      SmtEval.native_zplus]
  rw [hConcat, hPayloadModNew, hWi]

private theorem facts_conclusion_impl
    (M : SmtModel) (hM : model_wf M) (w t n : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (ufBv2natInt2bvExtendConclusion w t n) = Term.Bool ->
    eo_interprets M (ufBv2natInt2bvExtendConclusion w t n) true := by
  intro hTTrans hResultTy
  rcases typeof_args_of_extend_conclusion_bool w t n hResultTy with
    ⟨wi, ti, ni, hW, hN, hWiNonneg, hNiNonneg, hTType, hWi⟩
  subst w
  subst n
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t (Term.Numeral ti)
      hTTrans hTType with
    ⟨ti', hTieq, hTiNonneg', hTSmtTy⟩
  injection hTieq with hti
  subst hti
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (ufBv2natInt2bvExtendConclusion (Term.Numeral wi) t (Term.Numeral ni)) :=
    typed_conclusion_impl (Term.Numeral wi) t (Term.Numeral ni) hTTrans hResultTy
  rcases eval_lhs_extend M hM wi ti ni t hTTrans hWi hWiNonneg hNiNonneg
      hTiNonneg' hTSmtTy with
    ⟨payload, hLhsEval, hTEval⟩
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec (native_int_to_nat ti) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hTTrans)
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (concatTerm (zeroBvTerm (Term.Numeral ni))
              (concatTerm t (Term.Binary 0 0)))) =
        SmtValue.Binary wi payload :=
    eval_rhs_extend M hM wi ti ni payload t hWi hNiNonneg hTiNonneg'
      hTEval hEvalTy
  apply RuleProofs.eo_interprets_eq_of_rel M
    (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))
    (concatTerm (zeroBvTerm (Term.Numeral ni))
      (concatTerm t (Term.Binary 0 0))) hProgBool
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))))
    (__smtx_model_eval M
      (__eo_to_smt
        (concatTerm (zeroBvTerm (Term.Numeral ni))
          (concatTerm t (Term.Binary 0 0)))))
  rw [hLhsEval, hRhsEval]
  exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_uf_bv2nat_int2bv_extend_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv_extend args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises ≠ Term.Stuck :=
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
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons p1 premises =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons p2 premises =>
                          cases premises with
                          | nil =>
                              let P1 := __eo_state_proven_nth s p1
                              let P2 := __eo_state_proven_nth s p2
                              have hATransPair :
                                  RuleProofs.eo_has_smt_translation a1 ∧
                                    RuleProofs.eo_has_smt_translation a2 ∧
                                    RuleProofs.eo_has_smt_translation a3 ∧ True := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                              have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                                hATransPair.2.1
                              change __eo_typeof
                                  (__eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2)) =
                                Term.Bool at hResultTy
                              have hProgArg :
                                  __eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              obtain ⟨hA1NS, hA2NS, hA3NS⟩ :=
                                args_ne_stuck_of_prog_not_stuck a1 a2 a3 P1 P2 hProgArg
                              rcases shape_of_prog_uf_bv2nat_int2bv_extend_not_stuck
                                  a1 a2 a3 P1 P2 hA1NS hA2NS hA3NS hProgArg with
                                ⟨lw2, lt2, ln2, lw3, lt3, hP1, hP2⟩
                              rw [hP1, hP2] at hProgArg hResultTy
                              have hProgEq :
                                  __eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3
                                    (Proof.pf
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.eq)
                                          (Term.Apply
                                            (Term.Apply (Term.UOp UserOp.gt) lw2)
                                            (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
                                        (Term.Boolean true)))
                                    (Proof.pf
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.eq) ln2)
                                        (Term.Apply
                                          (Term.Apply (Term.UOp UserOp.neg) lw3)
                                          (Term.Apply (Term.UOp UserOp._at_bvsize) lt3)))) =
                                    __eo_requires
                                      (__eo_and
                                        (__eo_and
                                          (__eo_and
                                            (__eo_and (__eo_eq a1 lw2) (__eo_eq a2 lt2))
                                            (__eo_eq a3 ln2))
                                          (__eo_eq a1 lw3))
                                        (__eo_eq a2 lt3))
                                      (Term.Boolean true)
                                      (ufBv2natInt2bvExtendConclusion a1 a2 a3) :=
                                prog_uf_bv2nat_int2bv_extend_eq a1 a2 a3
                                  lw2 lt2 ln2 lw3 lt3 hA1NS hA2NS hA3NS
                              rw [hProgEq] at hProgArg hResultTy
                              have hAlign :
                                  lw2 = a1 ∧ lt2 = a2 ∧ ln2 = a3 ∧
                                    lw3 = a1 ∧ lt3 = a2 :=
                                eqs_of_requires5_and_eq_true_not_stuck
                                  a1 lw2 a2 lt2 a3 ln2 a1 lw3 a2 lt3
                                  (ufBv2natInt2bvExtendConclusion a1 a2 a3)
                                  hProgArg
                              obtain ⟨hLw2, hLt2, hLn2, hLw3, hLt3⟩ := hAlign
                              subst lw2
                              subst lt2
                              subst ln2
                              subst lw3
                              subst lt3
                              rw [requires5_and_eq_self_true_body a1 a2 a3
                                (ufBv2natInt2bvExtendConclusion a1 a2 a3)
                                hA1NS hA2NS hA3NS] at hResultTy
                              have hStepEq :
                                  __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend
                                      (CArgList.cons a1
                                        (CArgList.cons a2
                                          (CArgList.cons a3 CArgList.nil)))
                                      (CIndexList.cons p1
                                        (CIndexList.cons p2 CIndexList.nil)) =
                                    ufBv2natInt2bvExtendConclusion a1 a2 a3 := by
                                change __eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2) =
                                  ufBv2natInt2bvExtendConclusion a1 a2 a3
                                rw [hP1, hP2, hProgEq,
                                  requires5_and_eq_self_true_body a1 a2 a3
                                    (ufBv2natInt2bvExtendConclusion a1 a2 a3)
                                    hA1NS hA2NS hA3NS]
                              rw [hStepEq]
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                exact facts_conclusion_impl M hM a1 a2 a3
                                  hA2Trans hResultTy
                              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (typed_conclusion_impl a1 a2 a3 hA2Trans hResultTy)
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
