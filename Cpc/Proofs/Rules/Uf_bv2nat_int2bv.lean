module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

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

private abbrev ufBv2natInt2bvConclusion (w t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (intToBvTerm w (ubvToIntTerm t))) t

private abbrev ufBv2natInt2bvType (w t : Term) : Term :=
  __eo_typeof_eq
    (__eo_typeof_int_to_bv (__eo_typeof w) w
      (__eo_typeof__at_bvsize (__eo_typeof t)))
    (__eo_typeof t)

private theorem typeof_ufBv2natInt2bvConclusion_eq (w t : Term) :
    __eo_typeof (ufBv2natInt2bvConclusion w t) =
      ufBv2natInt2bvType w t := by
  rfl

/-- When both args are non-stuck and the premise has the expected `eq`/`bvsize`
    shape, the program reduces to the requires-guarded conclusion. -/
private theorem prog_uf_bv2nat_int2bv_eq (w1 t1 lt lw : Term)
    (hW : w1 ≠ Term.Stuck) (hT : t1 ≠ Term.Stuck) :
    __eo_prog_uf_bv2nat_int2bv w1 t1
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp._at_bvsize) lt)) lw)) =
      __eo_requires (__eo_and (__eo_eq t1 lt) (__eo_eq w1 lw))
        (Term.Boolean true) (ufBv2natInt2bvConclusion w1 t1) := by
  cases w1 <;> cases t1 <;>
    simp [__eo_prog_uf_bv2nat_int2bv, ufBv2natInt2bvConclusion,
      intToBvTerm, ubvToIntTerm] at hW hT ⊢

/-- A non-stuck program forces both args to be non-stuck. -/
private theorem args_ne_stuck_of_prog_not_stuck
    (w1 t1 p : Term)
    (h : __eo_prog_uf_bv2nat_int2bv w1 t1 (Proof.pf p) ≠ Term.Stuck) :
    w1 ≠ Term.Stuck ∧ t1 ≠ Term.Stuck := by
  constructor
  · intro hW
    subst w1
    simp [__eo_prog_uf_bv2nat_int2bv] at h
  · intro hT
    subst t1
    cases w1 <;> simp [__eo_prog_uf_bv2nat_int2bv] at h

/-- Shape lemma: a non-stuck program forces the premise to be an equality of a
    `bvsize` term and another term. -/
private theorem shape_of_prog_uf_bv2nat_int2bv_not_stuck
    (w1 t1 p : Term)
    (hW : w1 ≠ Term.Stuck) (hT : t1 ≠ Term.Stuck)
    (h : __eo_prog_uf_bv2nat_int2bv w1 t1 (Proof.pf p) ≠ Term.Stuck) :
    ∃ lt lw : Term,
      p =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp._at_bvsize) lt)) lw := by
  unfold __eo_prog_uf_bv2nat_int2bv at h
  split at h
  · exact absurd rfl hW
  · exact absurd rfl hT
  · rename_i lt lw _ _ heq
    injection heq with heq
    exact ⟨lt, lw, heq⟩
  · exact absurd rfl h

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true := hProg'.1
  have hBoth :
      __eo_eq x1 x2 = Term.Boolean true ∧ __eo_eq y1 y2 = Term.Boolean true := by
    have eq_stuck_or_bool :
        ∀ a b : Term, __eo_eq a b = Term.Stuck ∨
          ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
      intro a b
      by_cases ha : a = Term.Stuck
      · subst a
        exact Or.inl (by simp [__eo_eq])
      · by_cases hb : b = Term.Stuck
        · subst b
          exact Or.inl (by simp [__eo_eq])
        · exact Or.inr ⟨native_teq b a, by simp [__eo_eq]⟩
    rcases eq_stuck_or_bool x1 x2 with hX | ⟨b1, hX⟩
    · simp [__eo_and, hX] at hAnd
    rcases eq_stuck_or_bool y1 y2 with hY | ⟨b2, hY⟩
    · simp [__eo_and, hX, hY] at hAnd
    cases b1 <;> cases b2 <;> simp [__eo_and, hX, hY, native_and] at hAnd ⊢
  exact ⟨eq_of_eo_eq_true x1 x2 hBoth.1, eq_of_eo_eq_true y1 y2 hBoth.2⟩

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem requires_and_eq_self_true_body
    (w t body : Term)
    (hWNotStuck : w ≠ Term.Stuck)
    (hTNotStuck : t ≠ Term.Stuck) :
    __eo_requires (__eo_and (__eo_eq t t) (__eo_eq w w))
      (Term.Boolean true) body = body := by
  simp [__eo_requires, __eo_and, eo_eq_self_true_of_ne_stuck w hWNotStuck,
    eo_eq_self_true_of_ne_stuck t hTNotStuck, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and]

/-- `int_to_bv` typing yields `Stuck` whenever its operand type is `Stuck`
    (in particular when `t` is not a bit-vector, so `ubv_to_int` is ill-typed). -/
private theorem typeof_int_to_bv_stuck_of_arg_stuck (A w : Term) :
    __eo_typeof_int_to_bv A w Term.Stuck = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

/-- `int_to_bv` typing yields `Stuck` whenever the width type is not `Int`. -/
private theorem typeof_int_to_bv_stuck_of_width_ty_ne_int (A w B : Term)
    (hA : A ≠ Term.UOp UserOp.Int) :
    __eo_typeof_int_to_bv A w B = Term.Stuck := by
  unfold __eo_typeof_int_to_bv
  split <;> simp_all

/-- Inversion: if `int_to_bv` (with an `Int` operand type) yields a `BitVec`
    type, then the width type is `Int`, the width is a nonnegative numeral and
    the resulting width term matches. -/
private theorem int_to_bv_type_bitvec_inv (A w m : Term)
    (h : __eo_typeof_int_to_bv A w (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) m) :
    A = Term.UOp UserOp.Int ∧
      ∃ n, w = Term.Numeral n ∧ native_zlt (-1 : native_Int) n = true ∧
        m = Term.Numeral n := by
  -- If the width type `A` is not `UOp Int`, the result is `Stuck`.
  by_cases hA : A = Term.UOp UserOp.Int
  · subst A
    refine ⟨rfl, ?_⟩
    -- Now `int_to_bv (UOp Int) w (UOp Int)`; the width `w` must be a numeral.
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

/-- `bvsize`/`ubv_to_int` typing yields `Stuck` unless the operand type is a
    bit-vector. -/
private theorem bvsize_stuck_of_not_bitvec (T : Term) :
    (∀ m, T ≠ Term.Apply (Term.UOp UserOp.BitVec) m) ->
    __eo_typeof__at_bvsize T = Term.Stuck := by
  intro hNotBv
  cases T with
  | Apply f m =>
      cases f with
      | UOp op =>
          cases op <;> first | rfl | (exact absurd rfl (hNotBv m))
      | _ => rfl
  | _ => rfl

/-- Inversion for `__eo_typeof_eq`: a `Bool` result forces both operand types to
    be equal (and non-stuck). -/
private theorem typeof_eq_bool_inv (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    B = A := by
  -- `typeof_eq A B = requires (eq A B) true Bool`; a `Bool` result is non-stuck.
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
      have hEqTrue : __eo_eq A B = Term.Boolean true := hReq'.1
      exact eq_of_eo_eq_true A B hEqTrue

/-- From the result type being `Bool`, the width is a nonnegative numeral and
    `t`'s type is exactly `BitVec` of that same numeral. -/
private theorem typeof_args_of_conclusion_bool (w t : Term) :
    __eo_typeof (ufBv2natInt2bvConclusion w t) = Term.Bool ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
  intro hTy
  rw [typeof_ufBv2natInt2bvConclusion_eq] at hTy
  simp only [ufBv2natInt2bvType] at hTy
  -- The two operand types of the top `eq` agree.
  have hEqTy :
      __eo_typeof t =
        __eo_typeof_int_to_bv (__eo_typeof w) w
          (__eo_typeof__at_bvsize (__eo_typeof t)) :=
    typeof_eq_bool_inv _ _ hTy
  -- The LHS type is a `BitVec`, so `typeof t` is a `BitVec` and the inversion
  -- of `int_to_bv` applies.
  by_cases hBv : ∃ m, __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) m
  · rcases hBv with ⟨m, hTTy⟩
    have hBvsizeInt : __eo_typeof__at_bvsize (__eo_typeof t) = Term.UOp UserOp.Int := by
      rw [hTTy]; rfl
    rw [hBvsizeInt] at hEqTy
    rw [hTTy] at hEqTy
    rcases int_to_bv_type_bitvec_inv (__eo_typeof w) w m hEqTy.symm with
      ⟨_hWTyInt, n, hwn, hPos, hmn⟩
    subst w
    subst m
    refine ⟨n, rfl, ?_, hTTy⟩
    have hLt' : (-1 : native_Int) < n := by
      simpa [native_zlt, SmtEval.native_zlt] using hPos
    have hNonneg : (0 : native_Int) <= n := by
      have hStep : (-1 : native_Int) + 1 <= n := (Int.add_one_le_iff).2 hLt'
      simpa using hStep
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  · -- typeof t is not a bit-vector; bvsize is Stuck, so the LHS type is Stuck.
    exfalso
    have hBvStuck : __eo_typeof__at_bvsize (__eo_typeof t) = Term.Stuck :=
      bvsize_stuck_of_not_bitvec (__eo_typeof t)
        (by intro m hm; exact hBv ⟨m, hm⟩)
    rw [hBvStuck, typeof_int_to_bv_stuck_of_arg_stuck] at hTy
    simp [__eo_typeof_eq] at hTy

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

/-- SMT typing of the left side `int_to_bv w (ubv_to_int t)` matches the BitVec
    type of `t`. -/
private theorem smt_typeof_lhs_eq
    (n : native_Int) (t : Term) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof
        (__eo_to_smt (intToBvTerm (Term.Numeral n) (ubvToIntTerm t))) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro hNonneg hTSmtTy
  change __smtx_typeof
      (SmtTerm.int_to_bv (SmtTerm.Numeral n)
        (SmtTerm.ubv_to_int (__eo_to_smt t))) =
    SmtType.BitVec (native_int_to_nat n)
  rw [smtx_typeof_int_to_bv_term_eq, smtx_typeof_ubv_to_int_term_eq]
  simp [__smtx_typeof_int_to_bv, __smtx_typeof_bv_op_1_ret, native_ite,
    hTSmtTy, hNonneg]

/-- The two sides of the conclusion evaluate to the same value: the round-trip
    `int_to_bv w (ubv_to_int t)` collapses to `t` by bitvector canonicity. -/
private theorem eval_lhs_matches_t
    (M : SmtModel) (hM : model_wf M) (n : native_Int) (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_model_eval M
        (__eo_to_smt (intToBvTerm (Term.Numeral n) (ubvToIntTerm t))) =
      __smtx_model_eval M (__eo_to_smt t) := by
  intro hTTrans hNonneg hTSmtTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec (native_int_to_nat n) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hTTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalT⟩
  rw [width_nat_to_int_eq n hNonneg] at hEvalT
  -- canonicity: payload = mod payload 2^n
  have hCanon :
      native_zeq payload (native_mod_total payload (native_int_pow2 n)) = true :=
    bitvec_payload_canonical (u := native_int_to_nat n)
      (by rw [hEvalT] at hEvalTy; exact hEvalTy)
  have hMod : native_mod_total payload (native_int_pow2 n) = payload := by
    have hEq : payload = native_mod_total payload (native_int_pow2 n) := by
      simpa [SmtEval.native_zeq] using hCanon
    exact hEq.symm
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral n)
        (SmtTerm.ubv_to_int (__eo_to_smt t))) =
    __smtx_model_eval M (__eo_to_smt t)
  rw [smtx_eval_int_to_bv_term_eq, smtx_eval_ubv_to_int_term_eq, hEvalT]
  have hEvalN :
      __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
    rw [__smtx_model_eval.eq_2]
  rw [hEvalN]
  simp [__smtx_model_eval_ubv_to_int, __smtx_model_eval_int_to_bv, hMod]

private theorem typed_conclusion_impl
    (w t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (ufBv2natInt2bvConclusion w t) = Term.Bool ->
    RuleProofs.eo_has_bool_type (ufBv2natInt2bvConclusion w t) := by
  intro hTTrans hResultTy
  rcases typeof_args_of_conclusion_bool w t hResultTy with ⟨n, hW, hNonneg, hTType⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t (Term.Numeral n) hTTrans hTType with
    ⟨n', hNeq, _hNonneg', hTSmtTy⟩
  injection hNeq with hnn
  subst hnn
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (intToBvTerm (Term.Numeral n) (ubvToIntTerm t))) =
        SmtType.BitVec (native_int_to_nat n) :=
    smt_typeof_lhs_eq n t hNonneg hTSmtTy
  refine RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (intToBvTerm (Term.Numeral n) (ubvToIntTerm t)) t
    (by rw [hLhsTy, hTSmtTy]) ?_
  rw [hLhsTy]
  intro hC
  cases hC

private theorem facts_conclusion_impl
    (M : SmtModel) (hM : model_wf M) (w t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (ufBv2natInt2bvConclusion w t) = Term.Bool ->
    eo_interprets M (ufBv2natInt2bvConclusion w t) true := by
  intro hTTrans hResultTy
  rcases typeof_args_of_conclusion_bool w t hResultTy with ⟨n, hW, hNonneg, hTType⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width t (Term.Numeral n) hTTrans hTType with
    ⟨n', hNeq, _hNonneg', hTSmtTy⟩
  injection hNeq with hnn
  subst hnn
  have hProgBool :
      RuleProofs.eo_has_bool_type (ufBv2natInt2bvConclusion (Term.Numeral n) t) :=
    typed_conclusion_impl (Term.Numeral n) t hTTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
    (intToBvTerm (Term.Numeral n) (ubvToIntTerm t)) t hProgBool
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt (intToBvTerm (Term.Numeral n) (ubvToIntTerm t))))
    (__smtx_model_eval M (__eo_to_smt t))
  rw [eval_lhs_matches_t M hM n t hTTrans hNonneg hTSmtTy]
  exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_uf_bv2nat_int2bv_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv args premises ≠ Term.Stuck :=
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
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n1 premises =>
                  cases premises with
                  | nil =>
                      let P1 := __eo_state_proven_nth s n1
                      have hATransPair :
                          RuleProofs.eo_has_smt_translation a1 ∧
                            RuleProofs.eo_has_smt_translation a2 ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                        hATransPair.2.1
                      change __eo_typeof
                          (__eo_prog_uf_bv2nat_int2bv a1 a2 (Proof.pf P1)) =
                        Term.Bool at hResultTy
                      have hProgArg :
                          __eo_prog_uf_bv2nat_int2bv a1 a2 (Proof.pf P1) ≠ Term.Stuck :=
                        term_ne_stuck_of_typeof_bool hResultTy
                      obtain ⟨hA1NS, hA2NS⟩ :=
                        args_ne_stuck_of_prog_not_stuck a1 a2 P1 hProgArg
                      rcases shape_of_prog_uf_bv2nat_int2bv_not_stuck a1 a2 P1
                        hA1NS hA2NS hProgArg with ⟨lt, lw, hP1⟩
                      rw [hP1] at hProgArg hResultTy
                      -- Reduce the program to its requires-guarded form.
                      have hProgEq :
                          __eo_prog_uf_bv2nat_int2bv a1 a2
                            (Proof.pf
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp.eq)
                                  (Term.Apply (Term.UOp UserOp._at_bvsize) lt)) lw)) =
                            __eo_requires (__eo_and (__eo_eq a2 lt) (__eo_eq a1 lw))
                              (Term.Boolean true) (ufBv2natInt2bvConclusion a1 a2) :=
                        prog_uf_bv2nat_int2bv_eq a1 a2 lt lw hA1NS hA2NS
                      rw [hProgEq] at hProgArg hResultTy
                      have hAlign : lt = a2 ∧ lw = a1 :=
                        eqs_of_requires_and_eq_true_not_stuck a2 a1 lt lw
                          (ufBv2natInt2bvConclusion a1 a2) hProgArg
                      obtain ⟨hLt, hLw⟩ := hAlign
                      subst lt
                      subst lw
                      rw [requires_and_eq_self_true_body a1 a2
                        (ufBv2natInt2bvConclusion a1 a2) hA1NS hA2NS]
                        at hResultTy
                      -- The cmd-step term reduces to the bare conclusion.
                      have hStepEq :
                          __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv
                              (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                              (CIndexList.cons n1 CIndexList.nil) =
                            ufBv2natInt2bvConclusion a1 a2 := by
                        change __eo_prog_uf_bv2nat_int2bv a1 a2 (Proof.pf P1) =
                          ufBv2natInt2bvConclusion a1 a2
                        rw [hP1, hProgEq,
                          requires_and_eq_self_true_body a1 a2
                            (ufBv2natInt2bvConclusion a1 a2) hA1NS hA2NS]
                      rw [hStepEq]
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        exact facts_conclusion_impl M hM a1 a2 hA2Trans hResultTy
                      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed_conclusion_impl a1 a2 hA2Trans hResultTy)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
