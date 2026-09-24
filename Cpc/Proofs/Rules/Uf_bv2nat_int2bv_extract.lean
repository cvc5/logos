module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

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

private abbrev extractTerm (hi lo t : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract hi lo) t

private abbrev ufBv2natInt2bvExtractConclusion (w t wm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (intToBvTerm w (ubvToIntTerm t))) (extractTerm wm (Term.Numeral 0) t)

private abbrev ufBv2natInt2bvExtractType (w t wm : Term) : Term :=
  __eo_typeof_eq
    (__eo_typeof_int_to_bv (__eo_typeof w) w
      (__eo_typeof__at_bvsize (__eo_typeof t)))
    (__eo_typeof_extract (__eo_typeof wm) wm
      (Term.UOp UserOp.Int) (Term.Numeral 0) (__eo_typeof t))

private theorem typeof_ufBv2natInt2bvExtractConclusion_eq (w t wm : Term) :
    __eo_typeof (ufBv2natInt2bvExtractConclusion w t wm) =
      ufBv2natInt2bvExtractType w t wm := by
  rfl

private theorem prog_uf_bv2nat_int2bv_extract_eq
    (w t wm lw2 lt2 lwm2 lw3 : Term)
    (hW : w ≠ Term.Stuck) (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck) :
    __eo_prog_uf_bv2nat_int2bv_extract w t wm
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.lt) lw2)
              (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
          (Term.Boolean true)))
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) lwm2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lw3) (Term.Numeral 1)))) =
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq w lw2) (__eo_eq t lt2))
            (__eo_eq wm lwm2))
          (__eo_eq w lw3))
        (Term.Boolean true) (ufBv2natInt2bvExtractConclusion w t wm) := by
  unfold __eo_prog_uf_bv2nat_int2bv_extract
  split
  · exact absurd rfl hW
  · exact absurd rfl hT
  · exact absurd rfl hWm
  · rename_i heq1 heq2
    injection heq1 with heq1
    injection heq2 with heq2
    simp only [Term.Apply.injEq, true_and, and_true] at heq1 heq2
    obtain ⟨hw2, ht2⟩ := heq1
    obtain ⟨hwm2, hw3⟩ := heq2
    subst lw2
    subst lt2
    subst lwm2
    subst lw3
    rfl
  · rename_i hcontra
    exact (hcontra lw2 lt2 lwm2 lw3 rfl rfl).elim

private theorem args_ne_stuck_of_prog_not_stuck
    (w t wm p1 p2 : Term)
    (h : __eo_prog_uf_bv2nat_int2bv_extract w t wm
      (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    w ≠ Term.Stuck ∧ t ≠ Term.Stuck ∧ wm ≠ Term.Stuck := by
  constructor
  · intro hW
    subst w
    simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
  constructor
  · intro hT
    subst t
    cases w <;> simp [__eo_prog_uf_bv2nat_int2bv_extract] at h
  · intro hWm
    subst wm
    cases w <;> cases t <;> simp [__eo_prog_uf_bv2nat_int2bv_extract] at h

private theorem shape_of_prog_uf_bv2nat_int2bv_extract_not_stuck
    (w t wm p1 p2 : Term)
    (hW : w ≠ Term.Stuck) (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck)
    (h : __eo_prog_uf_bv2nat_int2bv_extract w t wm
      (Proof.pf p1) (Proof.pf p2) ≠ Term.Stuck) :
    ∃ lw2 lt2 lwm2 lw3 : Term,
      p1 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.lt) lw2)
              (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
          (Term.Boolean true) ∧
      p2 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) lwm2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lw3) (Term.Numeral 1)) := by
  unfold __eo_prog_uf_bv2nat_int2bv_extract at h
  split at h
  · exact absurd rfl hW
  · exact absurd rfl hT
  · exact absurd rfl hWm
  · rename_i _ _ _ _ _ _ _ lw2 lt2 lwm2 lw3 _ _ _ heq1 heq2
    injection heq1 with heq1
    injection heq2 with heq2
    exact ⟨lw2, lt2, lwm2, lw3, heq1, heq2⟩
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
  exact (RuleProofs.eo_and_eq_true_args x y h).1

private theorem eo_and_eq_true_right {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    y = Term.Boolean true := by
  exact (RuleProofs.eo_and_eq_true_args x y h).2

private theorem eqs_of_requires4_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 B : Term) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4))
        (Term.Boolean true) B ≠ Term.Stuck ->
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  intro hProg
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hProg
  have h123 : __eo_and
          (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
          (__eo_eq x3 y3) = Term.Boolean true :=
    eo_and_eq_true_left hGuard
  have h4 : __eo_eq x4 y4 = Term.Boolean true :=
    eo_and_eq_true_right hGuard
  have h12 : __eo_and (__eo_eq x1 y1) (__eo_eq x2 y2) = Term.Boolean true :=
    eo_and_eq_true_left h123
  have h3 : __eo_eq x3 y3 = Term.Boolean true :=
    eo_and_eq_true_right h123
  have h1 : __eo_eq x1 y1 = Term.Boolean true :=
    eo_and_eq_true_left h12
  have h2 : __eo_eq x2 y2 = Term.Boolean true :=
    eo_and_eq_true_right h12
  exact ⟨eq_of_eo_eq_true x1 y1 h1, eq_of_eo_eq_true x2 y2 h2,
    eq_of_eo_eq_true x3 y3 h3, eq_of_eo_eq_true x4 y4 h4⟩

private theorem requires4_and_eq_self_true_body
    (w t wm body : Term)
    (hW : w ≠ Term.Stuck) (hT : t ≠ Term.Stuck) (hWm : wm ≠ Term.Stuck) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq w w) (__eo_eq t t))
            (__eo_eq wm wm))
          (__eo_eq w w))
        (Term.Boolean true) body = body := by
  have hEqW : __eo_eq w w = Term.Boolean true :=
    eo_eq_self_true_of_ne_stuck w hW
  have hEqT : __eo_eq t t = Term.Boolean true :=
    eo_eq_self_true_of_ne_stuck t hT
  have hEqWm : __eo_eq wm wm = Term.Boolean true :=
    eo_eq_self_true_of_ne_stuck wm hWm
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and (__eo_eq w w) (__eo_eq t t))
            (__eo_eq wm wm))
          (__eo_eq w w) =
        Term.Boolean true := by
    simp [__eo_and, hEqW, hEqT, hEqWm, native_and, SmtEval.native_and]
  rw [hGuard]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

private theorem typeof_eq_bool_inv (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    B = A := by
  have hNeStuck : __eo_typeof_eq A B ≠ Term.Stuck := by
    rw [h]; intro hc; cases hc
  by_cases hAStuck : A = Term.Stuck
  · subst A; simp [__eo_typeof_eq] at hNeStuck
  · by_cases hBStuck : B = Term.Stuck
    · subst B
      cases A <;> simp [__eo_typeof_eq] at hNeStuck
    · have hReqEq : __eo_typeof_eq A B =
          __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool := by
        cases A <;> cases B <;> simp_all [__eo_typeof_eq]
      rw [hReqEq] at hNeStuck
      have hReq' := hNeStuck
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hReq'
      exact eq_of_eo_eq_true A B hReq'.1

private theorem typeof_int_to_bv_stuck_of_width_ty_ne_int (A w B : Term)
    (hA : A ≠ Term.UOp UserOp.Int) :
    __eo_typeof_int_to_bv A w B = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

private theorem typeof_int_to_bv_stuck_of_arg_ty_ne_int (A w B : Term)
    (hB : B ≠ Term.UOp UserOp.Int) :
    __eo_typeof_int_to_bv A w B = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

private theorem int_to_bv_type_nonstuck_inv (A w B : Term)
    (h : __eo_typeof_int_to_bv A w B ≠ Term.Stuck) :
    ∃ n : native_Int,
      A = Term.UOp UserOp.Int ∧ w = Term.Numeral n ∧
      B = Term.UOp UserOp.Int ∧
      native_zlt (-1 : native_Int) n = true ∧
      __eo_typeof_int_to_bv A w B =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
  by_cases hW : w = Term.Stuck
  · subst w
    simp [__eo_typeof_int_to_bv] at h
  by_cases hA : A = Term.UOp UserOp.Int
  · subst A
    by_cases hB : B = Term.UOp UserOp.Int
    · subst B
      cases hw : w <;> rw [hw] at h <;>
        first
        | (rename_i n
           cases hPos : native_zlt (-1 : native_Int) n
           · simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
               native_teq, native_not, SmtEval.native_not, hPos] at h
           · exact ⟨n, rfl, rfl, rfl, hPos, by
               simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
                 native_teq, native_not, SmtEval.native_not, hPos]⟩)
        | (exfalso
           simp [__eo_typeof_int_to_bv, __eo_requires, __eo_gt, native_ite,
             native_teq, native_not, SmtEval.native_not] at h)
    · rw [typeof_int_to_bv_stuck_of_arg_ty_ne_int (Term.UOp UserOp.Int) w B hB] at h
      exact False.elim (h rfl)
  · rw [typeof_int_to_bv_stuck_of_width_ty_ne_int A w B hA] at h
    exact False.elim (h rfl)

private theorem bvsize_int_inv (T : Term)
    (h : __eo_typeof__at_bvsize T = Term.UOp UserOp.Int) :
    ∃ m, T = Term.Apply (Term.UOp UserOp.BitVec) m := by
  cases T with
  | Apply f m =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof__at_bvsize] at h ⊢
      | _ => simp [__eo_typeof__at_bvsize] at h
  | _ => simp [__eo_typeof__at_bvsize] at h

private theorem typeof_extract_zero_numeral (wmv tw : native_Int) :
    __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmv)
        (Term.UOp UserOp.Int) (Term.Numeral 0)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral tw))
      =
        native_ite (native_zlt wmv tw)
          (native_ite (native_zlt 0 (native_zplus wmv 1))
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_zplus wmv 1)))
            Term.Stuck)
          Term.Stuck := by
  rw [__eo_typeof_extract.eq_3]
  have hLo : native_zlt (-1 : native_Int) (0 : native_Int) = true := by
    simp [native_zlt, SmtEval.native_zlt]
  simp [__eo_mk_apply, __eo_requires, __eo_gt, __eo_add, __eo_neg,
    native_ite, native_teq, native_not, SmtEval.native_not, native_zplus,
    SmtEval.native_zplus, native_zneg, SmtEval.native_zneg, hLo]
  · by_cases hHi : native_zlt wmv tw = true
    · by_cases hWidth : native_zlt 0 (wmv + 1) = true
      · simp [native_ite, hHi, hWidth]
      · simp [native_ite, hHi, hWidth]
    · simp [native_ite, hHi]
  · simp
  · simp

private theorem extract_zero_width_stuck_of_high_not_numeral (wm : Term)
    (hNot : ∀ i : native_Int, wm ≠ Term.Numeral i) :
    __eo_add (__eo_add wm (__eo_neg (Term.Numeral 0))) (Term.Numeral 1) =
      Term.Stuck := by
  cases wm <;> simp [__eo_add, __eo_neg] at hNot ⊢

private theorem typeof_extract_zero_stuck_of_high_not_numeral (wm t : Term)
    (hNot : ∀ i : native_Int, wm ≠ Term.Numeral i) :
    __eo_typeof_extract (__eo_typeof wm) wm
        (Term.UOp UserOp.Int) (Term.Numeral 0) (__eo_typeof t) =
      Term.Stuck := by
  have hWidth := extract_zero_width_stuck_of_high_not_numeral wm hNot
  unfold __eo_typeof_extract
  split <;> simp [hWidth, __eo_mk_apply, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

private theorem typeof_extract_zero_stuck_of_arg_not_bitvec_numeral
    (wmv : native_Int) (t : Term)
    (hNot : ∀ tw : native_Int,
      __eo_typeof t ≠ Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral tw)) :
    __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmv)
        (Term.UOp UserOp.Int) (Term.Numeral 0) (__eo_typeof t) =
      Term.Stuck := by
  by_cases hBv : ∃ n, __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) n
  · rcases hBv with ⟨n, hT⟩
    cases hn : n with
    | Numeral tw =>
        exact False.elim (hNot tw (by simpa [hn] using hT))
    | _ =>
        rw [hT, hn]
        simp [__eo_typeof_extract, __eo_mk_apply, __eo_requires, __eo_gt,
          __eo_add, __eo_neg, native_ite, native_teq, native_not,
          SmtEval.native_not]
  · cases hT : __eo_typeof t with
    | Apply f n =>
        cases f with
        | UOp op =>
            cases op <;> simp [__eo_typeof_extract, hT] at hBv ⊢
        | _ => simp [__eo_typeof_extract, hT]
    | _ => simp [__eo_typeof_extract, hT]

private theorem typeof_extract_zero_bitvec_inv (wm t : Term) (m : Term)
    (h : __eo_typeof_extract (__eo_typeof wm) wm
        (Term.UOp UserOp.Int) (Term.Numeral 0) (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    ∃ wmv tw,
      wm = Term.Numeral wmv ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral tw) ∧
      native_zlt wmv tw = true ∧
      native_zlt 0 (native_zplus wmv 1) = true ∧
      m = Term.Numeral (native_zplus wmv 1) := by
  by_cases hWmNum : ∃ wmv, wm = Term.Numeral wmv
  · rcases hWmNum with ⟨wmv, hWm⟩
    subst wm
    by_cases hBv : ∃ tw, __eo_typeof t =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral tw)
    · rcases hBv with ⟨tw, hT⟩
      rw [hT] at h
      change __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmv)
          (Term.UOp UserOp.Int) (Term.Numeral 0)
          (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral tw)) =
        Term.Apply (Term.UOp UserOp.BitVec) m at h
      rw [typeof_extract_zero_numeral] at h
      by_cases hHi : native_zlt wmv tw = true
      · by_cases hWidth : native_zlt 0 (native_zplus wmv 1) = true
        · simp [native_ite, hHi, hWidth] at h
          exact ⟨wmv, tw, rfl, hT, hHi, hWidth, h.symm⟩
        · simp [native_ite, hHi, hWidth] at h
      · simp [native_ite, hHi] at h
    · have hStuck :=
        typeof_extract_zero_stuck_of_arg_not_bitvec_numeral wmv t
          (by intro tw hT; exact hBv ⟨tw, hT⟩)
      change __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmv)
          (Term.UOp UserOp.Int) (Term.Numeral 0) (__eo_typeof t) =
        Term.Apply (Term.UOp UserOp.BitVec) m at h
      rw [hStuck] at h
      cases h
  · have hStuck :=
      typeof_extract_zero_stuck_of_high_not_numeral wm t
        (by intro i hi; exact hWmNum ⟨i, hi⟩)
    rw [hStuck] at h
    cases h

private theorem width_nat_to_int_eq
    (n : native_Int) (hNonneg : native_zleq 0 n = true) :
    native_nat_to_int (native_int_to_nat n) = n := by
  have hnNonneg : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using Int.toNat_of_nonneg hnNonneg

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

private theorem typeof_args_of_conclusion_bool (w t wm : Term) :
    __eo_typeof (ufBv2natInt2bvExtractConclusion w t wm) = Term.Bool ->
    ∃ wi wmv tw,
      w = Term.Numeral wi ∧ wm = Term.Numeral wmv ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral tw) ∧
      native_zleq 0 wi = true ∧ native_zleq 0 tw = true ∧
      native_zlt wmv tw = true ∧
      native_zlt 0 (native_zplus wmv 1) = true ∧
      wi = native_zplus wmv 1 := by
  intro hTy
  rw [typeof_ufBv2natInt2bvExtractConclusion_eq] at hTy
  simp only [ufBv2natInt2bvExtractType] at hTy
  let lhsTy := __eo_typeof_int_to_bv (__eo_typeof w) w
      (__eo_typeof__at_bvsize (__eo_typeof t))
  let rhsTy := __eo_typeof_extract (__eo_typeof wm) wm
      (Term.UOp UserOp.Int) (Term.Numeral 0) (__eo_typeof t)
  have hEqTy : rhsTy = lhsTy := typeof_eq_bool_inv lhsTy rhsTy hTy
  have hLhsNonStuck : lhsTy ≠ Term.Stuck := by
    intro hStuck
    have hRhsStuck : rhsTy = Term.Stuck := hEqTy.trans hStuck
    change __eo_typeof_eq lhsTy rhsTy = Term.Bool at hTy
    rw [hStuck, hRhsStuck] at hTy
    simp [__eo_typeof_eq] at hTy
  rcases int_to_bv_type_nonstuck_inv (__eo_typeof w) w
      (__eo_typeof__at_bvsize (__eo_typeof t)) hLhsNonStuck with
    ⟨wi, _hWTy, hW, hBvsizeTy, hWiPos, hLhsEq⟩
  subst w
  rcases bvsize_int_inv (__eo_typeof t) hBvsizeTy with ⟨_mt, _hTBitVec⟩
  have hRhsBitVec :
      rhsTy = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wi) := by
    rw [hEqTy]
    exact hLhsEq
  rcases typeof_extract_zero_bitvec_inv wm t (Term.Numeral wi) hRhsBitVec with
    ⟨wmv, tw, hWm, hTty, hHi, hWidth, hWidthEqTerm⟩
  injection hWidthEqTerm with hWiEq
  subst wm
  have hWiNonneg : native_zleq 0 wi = true := by
    have hlt : (-1 : native_Int) < wi := by
      simpa [native_zlt, SmtEval.native_zlt] using hWiPos
    have hnonneg : (0 : native_Int) <= wi := by
      have hStep : (-1 : native_Int) + 1 <= wi :=
        (Int.add_one_le_iff).2 hlt
      simpa using hStep
    simpa [native_zleq, SmtEval.native_zleq] using hnonneg
  have hTwNonneg : native_zleq 0 tw = true := by
    have hWmWidth : wi = native_zplus wmv 1 := hWiEq
    have hwi0 : (0 : native_Int) <= wi := by
      simpa [native_zleq, SmtEval.native_zleq] using hWiNonneg
    have hwm1 : wmv + 1 = wi := by
      simpa [SmtEval.native_zplus] using hWmWidth.symm
    have hwmLt : wmv < tw := by
      simpa [native_zlt, SmtEval.native_zlt] using hHi
    have hwm1Nonneg : (0 : native_Int) <= wmv + 1 := by
      rw [hwm1]
      exact hwi0
    have hwm1LeTw : wmv + 1 <= tw :=
      (Int.add_one_le_iff).2 hwmLt
    have : (0 : native_Int) <= tw := Int.le_trans hwm1Nonneg hwm1LeTw
    simpa [native_zleq, SmtEval.native_zleq] using this
  exact ⟨wi, wmv, tw, rfl, rfl, hTty, hWiNonneg, hTwNonneg,
    hHi, hWidth, hWiEq⟩

private theorem smt_typeof_rhs_eq
    (wmv wi tw : native_Int) (t : Term)
    (hWiEq : wi = native_zplus wmv 1)
    (hTwNonneg : native_zleq 0 tw = true)
    (hHi : native_zlt wmv tw = true)
    (hWidth : native_zlt 0 (native_zplus wmv 1) = true)
    (hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat tw)) :
    __smtx_typeof
        (__eo_to_smt (extractTerm (Term.Numeral wmv) (Term.Numeral 0) t)) =
      SmtType.BitVec (native_int_to_nat wi) := by
  change __smtx_typeof
      (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral 0) (__eo_to_smt t)) =
    SmtType.BitVec (native_int_to_nat wi)
  rw [typeof_extract_eq, hTSmtTy]
  have hLo : native_zleq 0 (0 : native_Int) = true := by
    simp [native_zleq, SmtEval.native_zleq]
  have hTwFit : native_nat_to_int (native_int_to_nat tw) = tw :=
    width_nat_to_int_eq tw hTwNonneg
  have hHi' : native_zlt wmv (native_nat_to_int (native_int_to_nat tw)) = true := by
    rw [hTwFit]
    exact hHi
  have hWidthPos :
      native_zlt 0 (native_zplus (native_zplus wmv 1) (native_zneg 0)) = true := by
    simpa [native_zplus, native_zneg] using hWidth
  have hWidthNat :
      native_int_to_nat (native_zplus (native_zplus wmv 1) (native_zneg 0)) =
        native_int_to_nat wi := by
    rw [hWiEq]
    simp [native_zplus, native_zneg]
  simp [__smtx_typeof_extract, native_ite, hLo, hHi', hWidthPos, hWidthNat]

private theorem typed_conclusion_impl
    (w t wm : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (ufBv2natInt2bvExtractConclusion w t wm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (ufBv2natInt2bvExtractConclusion w t wm) := by
  intro hTTrans hResultTy
  rcases typeof_args_of_conclusion_bool w t wm hResultTy with
    ⟨wi, wmv, tw, hW, hWm, hTty, hWiNonneg, hTwNonneg, hHi, hWidth, hWiEq⟩
  subst w
  subst wm
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t (Term.Numeral tw)
      hTTrans hTty with
    ⟨tw', hTwEq, _hTwNonneg', hTSmtTy⟩
  injection hTwEq with hTwEqVal
  subst tw'
  have hRhsTy := smt_typeof_rhs_eq wmv wi tw t hWiEq hTwNonneg hHi hWidth hTSmtTy
  -- Rebuild the LHS type using the source width `tw`; the top equation has
  -- already established that the int-to-bv width is `wi`.
  have hLhsTy' :
      __smtx_typeof
          (__eo_to_smt (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))) =
        SmtType.BitVec (native_int_to_nat wi) := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral wi)
          (SmtTerm.ubv_to_int (__eo_to_smt t))) =
      SmtType.BitVec (native_int_to_nat wi)
    rw [smtx_typeof_int_to_bv_term_eq, smtx_typeof_ubv_to_int_term_eq]
    simp [__smtx_typeof_int_to_bv, __smtx_typeof_bv_op_1_ret, native_ite,
      hTSmtTy, hWiNonneg]
  change RuleProofs.eo_has_bool_type
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t)))
      (extractTerm (Term.Numeral wmv) (Term.Numeral 0) t))
  refine RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))
    (extractTerm (Term.Numeral wmv) (Term.Numeral 0) t) ?_ ?_
  · rw [hLhsTy', hRhsTy]
  · rw [hLhsTy']; intro h; cases h

private theorem eval_extract_low_zero_matches_int_to_bv
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (wi wmv tw : native_Int)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hWiNonneg : native_zleq 0 wi = true)
    (hTwNonneg : native_zleq 0 tw = true)
    (hWiEq : wi = native_zplus wmv 1)
    (hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat tw)) :
    __smtx_model_eval M
        (__eo_to_smt (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))) =
      __smtx_model_eval M
        (__eo_to_smt (extractTerm (Term.Numeral wmv) (Term.Numeral 0) t)) := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec (native_int_to_nat tw) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hTTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalT⟩
  rw [width_nat_to_int_eq tw hTwNonneg] at hEvalT
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral wi)
        (SmtTerm.ubv_to_int (__eo_to_smt t))) =
    __smtx_model_eval M
      (SmtTerm.extract (SmtTerm.Numeral wmv) (SmtTerm.Numeral 0) (__eo_to_smt t))
  have hEvalWi :
      __smtx_model_eval M (SmtTerm.Numeral wi) = SmtValue.Numeral wi := by
    rw [__smtx_model_eval.eq_2]
  have hEvalWm :
      __smtx_model_eval M (SmtTerm.Numeral wmv) = SmtValue.Numeral wmv := by
    rw [__smtx_model_eval.eq_2]
  have hEvalZero :
      __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
    rw [__smtx_model_eval.eq_2]
  rw [smtx_eval_int_to_bv_term_eq, smtx_eval_ubv_to_int_term_eq,
    smtx_eval_extract_term_eq, hEvalT, hEvalWi, hEvalWm, hEvalZero]
  simp [__smtx_model_eval_ubv_to_int, __smtx_model_eval_int_to_bv,
    __smtx_model_eval_extract, native_binary_extract, native_int_pow2,
    native_zexp_total, native_div_total, hWiEq, native_zplus, native_zneg]

private theorem facts_conclusion_impl
    (M : SmtModel) (hM : model_wf M) (w t wm : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (ufBv2natInt2bvExtractConclusion w t wm) = Term.Bool ->
    eo_interprets M (ufBv2natInt2bvExtractConclusion w t wm) true := by
  intro hTTrans hResultTy
  rcases typeof_args_of_conclusion_bool w t wm hResultTy with
    ⟨wi, wmv, tw, hW, hWm, hTty, hWiNonneg, hTwNonneg, hHi, hWidth, hWiEq⟩
  subst w
  subst wm
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t (Term.Numeral tw)
      hTTrans hTty with
    ⟨tw', hTwEq, _hTwNonneg', hTSmtTy⟩
  injection hTwEq with hTwEqVal
  subst tw'
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (ufBv2natInt2bvExtractConclusion (Term.Numeral wi) t (Term.Numeral wmv)) :=
    typed_conclusion_impl (Term.Numeral wi) t (Term.Numeral wmv) hTTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
    (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))
    (extractTerm (Term.Numeral wmv) (Term.Numeral 0) t) hProgBool
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt (intToBvTerm (Term.Numeral wi) (ubvToIntTerm t))))
    (__smtx_model_eval M
      (__eo_to_smt (extractTerm (Term.Numeral wmv) (Term.Numeral 0) t)))
  rw [eval_extract_low_zero_matches_int_to_bv M hM t wi wmv tw hTTrans
    hWiNonneg hTwNonneg hWiEq hTSmtTy]
  exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_uf_bv2nat_int2bv_extract_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv_extract args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises ≠ Term.Stuck :=
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
                              have hATransTriple :
                                  RuleProofs.eo_has_smt_translation a1 ∧
                                    RuleProofs.eo_has_smt_translation a2 ∧
                                    RuleProofs.eo_has_smt_translation a3 ∧ True := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                              have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                                hATransTriple.2.1
                              change __eo_typeof
                                  (__eo_prog_uf_bv2nat_int2bv_extract a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2)) =
                                Term.Bool at hResultTy
                              have hProgArg :
                                  __eo_prog_uf_bv2nat_int2bv_extract a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              obtain ⟨hA1NS, hA2NS, hA3NS⟩ :=
                                args_ne_stuck_of_prog_not_stuck a1 a2 a3 P1 P2 hProgArg
                              rcases shape_of_prog_uf_bv2nat_int2bv_extract_not_stuck
                                  a1 a2 a3 P1 P2 hA1NS hA2NS hA3NS hProgArg with
                                ⟨lw2, lt2, lwm2, lw3, hP1, hP2⟩
                              rw [hP1, hP2] at hProgArg hResultTy
                              have hProgEq :
                                  __eo_prog_uf_bv2nat_int2bv_extract a1 a2 a3
                                    (Proof.pf
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.eq)
                                          (Term.Apply
                                            (Term.Apply (Term.UOp UserOp.lt) lw2)
                                            (Term.Apply (Term.UOp UserOp._at_bvsize) lt2)))
                                        (Term.Boolean true)))
                                    (Proof.pf
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.eq) lwm2)
                                        (Term.Apply
                                          (Term.Apply (Term.UOp UserOp.neg) lw3)
                                          (Term.Numeral 1)))) =
                                    __eo_requires
                                      (__eo_and
                                        (__eo_and
                                          (__eo_and (__eo_eq a1 lw2) (__eo_eq a2 lt2))
                                          (__eo_eq a3 lwm2))
                                        (__eo_eq a1 lw3))
                                      (Term.Boolean true)
                                      (ufBv2natInt2bvExtractConclusion a1 a2 a3) :=
                                prog_uf_bv2nat_int2bv_extract_eq a1 a2 a3
                                  lw2 lt2 lwm2 lw3 hA1NS hA2NS hA3NS
                              rw [hProgEq] at hProgArg hResultTy
                              have hAlign :
                                  lw2 = a1 ∧ lt2 = a2 ∧ lwm2 = a3 ∧ lw3 = a1 :=
                                eqs_of_requires4_and_eq_true_not_stuck
                                  a1 lw2 a2 lt2 a3 lwm2 a1 lw3
                                  (ufBv2natInt2bvExtractConclusion a1 a2 a3)
                                  hProgArg
                              obtain ⟨hLw2, hLt2, hLwm2, hLw3⟩ := hAlign
                              subst lw2
                              subst lt2
                              subst lwm2
                              subst lw3
                              rw [requires4_and_eq_self_true_body a1 a2 a3
                                (ufBv2natInt2bvExtractConclusion a1 a2 a3)
                                hA1NS hA2NS hA3NS] at hResultTy
                              have hStepEq :
                                  __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract
                                      (CArgList.cons a1
                                        (CArgList.cons a2
                                          (CArgList.cons a3 CArgList.nil)))
                                      (CIndexList.cons p1
                                        (CIndexList.cons p2 CIndexList.nil)) =
                                    ufBv2natInt2bvExtractConclusion a1 a2 a3 := by
                                change __eo_prog_uf_bv2nat_int2bv_extract a1 a2 a3
                                    (Proof.pf P1) (Proof.pf P2) =
                                  ufBv2natInt2bvExtractConclusion a1 a2 a3
                                rw [hP1, hP2, hProgEq,
                                  requires4_and_eq_self_true_body a1 a2 a3
                                    (ufBv2natInt2bvExtractConclusion a1 a2 a3)
                                    hA1NS hA2NS hA3NS]
                              rw [hStepEq]
                              refine ⟨?_, ?_⟩
                              · intro _hPrem
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
