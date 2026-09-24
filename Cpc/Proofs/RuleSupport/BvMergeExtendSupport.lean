module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport

public section

/-! Support for the `bv_merge_sign_extend_1` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvMergeSignExtend1Lhs (x i j : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.sign_extend i)
    (Term.Apply (Term.UOp1 UserOp1.sign_extend j) x)

def bvMergeSignExtend1Rhs (x k : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.sign_extend k) x

def bvMergeSignExtend1Term (x i j k : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvMergeSignExtend1Lhs x i j)) (bvMergeSignExtend1Rhs x k)

def bvMergeSignExtend1Prem (i j k : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) k)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) i)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) j) (Term.Numeral 0)))

private theorem eo_typeof_sign_extend_arg_bitvec_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_zero_extend A idx C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_zero_extend at h
  split at h <;> simp at h ⊢

private theorem sign_extend_amount_context
    (x k widthTerm : Term) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) widthTerm ->
    __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) ≠
      Term.Stuck ->
    ∃ a : native_Int,
      k = Term.Numeral a ∧ native_zleq 0 a = true := by
  intro hXTy hSignNe
  change __eo_typeof_zero_extend (__eo_typeof k) k (__eo_typeof x) ≠
      Term.Stuck at hSignNe
  rw [hXTy] at hSignNe
  have hParts :
      __eo_typeof k = Term.UOp UserOp.Int ∧
      __eo_requires (__eo_gt k (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec)
            (__eo_add widthTerm k)) ≠ Term.Stuck := by
    unfold __eo_typeof_zero_extend at hSignNe
    split at hSignNe <;> simp_all
  have hGuard :
      __eo_gt k (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hParts.2
  rcases sign_numeral_nonneg_of_gt_neg_one k hGuard with ⟨a, hK, ha0⟩
  exact ⟨a, hK, ha0⟩

private theorem sign_extend_full_context
    (x k : Term) (w : native_Int) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) ≠
      Term.Stuck ->
    ∃ a : native_Int,
      k = Term.Numeral a ∧ native_zleq 0 a = true ∧
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus w a)) := by
  intro hXTy hSignNe
  rcases sign_extend_amount_context x k (Term.Numeral w) hXTy hSignNe with
    ⟨a, hK, ha0⟩
  subst k
  have ha : (0 : Int) ≤ a := by
    simpa [SmtEval.native_zleq] using ha0
  have hLt : native_zlt (-1 : native_Int) a = true := by
    have : (-1 : Int) < a := by omega
    simpa [SmtEval.native_zlt] using this
  refine ⟨a, rfl, ha0, ?_⟩
  change __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral a)
      (__eo_typeof x) = _
  rw [hXTy]
  simp [__eo_typeof_zero_extend, __eo_requires, __eo_gt, __eo_add,
    __eo_mk_apply,
    hLt, native_ite, native_teq, native_not]

private theorem bv_merge_sign_extend_1_context
    (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvMergeSignExtend1Term x i j k) = Term.Bool ->
    ∃ w iv jv kv : native_Int,
      i = Term.Numeral iv ∧ j = Term.Numeral jv ∧
      k = Term.Numeral kv ∧
      native_zleq 0 w = true ∧ native_zleq 0 iv = true ∧
      native_zleq 0 jv = true ∧ native_zleq 0 kv = true ∧
      native_zplus (native_zplus w jv) iv = native_zplus w kv ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvMergeSignExtend1Lhs x i j))
      (__eo_typeof (bvMergeSignExtend1Rhs x k)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hRhsCore :
      __eo_typeof_zero_extend (__eo_typeof k) k (__eo_typeof x) ≠
        Term.Stuck := by
    exact hRhsNe
  rcases eo_typeof_sign_extend_arg_bitvec_of_ne_stuck hRhsCore with
    ⟨widthTerm, hXTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x widthTerm
      hXTrans hXTy with ⟨w, hWidth, hw0, hXSmtTy⟩
  subst widthTerm
  rcases sign_extend_full_context x k w hXTy hRhsNe with
    ⟨kv, hK, hkv0, hRhsTy⟩
  have hLhsCore :
      __eo_typeof_zero_extend (__eo_typeof i) i
          (__eo_typeof
            (Term.Apply (Term.UOp1 UserOp1.sign_extend j) x)) ≠
        Term.Stuck := by
    exact hLhsNe
  rcases eo_typeof_sign_extend_arg_bitvec_of_ne_stuck hLhsCore with
    ⟨innerWidth, hInnerTyRaw⟩
  have hInnerNe :
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend j) x) ≠
        Term.Stuck := by
    rw [hInnerTyRaw]
    intro h
    cases h
  rcases sign_extend_full_context x j w hXTy hInnerNe with
    ⟨jv, hJ, hjv0, hInnerTy⟩
  have hwj0 : native_zleq 0 (native_zplus w jv) = true := by
    have hw : (0 : Int) ≤ w := by
      simpa [SmtEval.native_zleq] using hw0
    have hj : (0 : Int) ≤ jv := by
      simpa [SmtEval.native_zleq] using hjv0
    have hsimpa :=
      Int.add_nonneg hw hj
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  rcases sign_extend_full_context
      (Term.Apply (Term.UOp1 UserOp1.sign_extend j) x) i
      (native_zplus w jv) hInnerTy hLhsNe with
    ⟨iv, hI, hiv0, hLhsTy⟩
  have hTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hWidths :
      native_zplus (native_zplus w jv) iv = native_zplus w kv := by
    change __eo_typeof
        (Term.Apply (Term.UOp1 UserOp1.sign_extend i)
          (Term.Apply (Term.UOp1 UserOp1.sign_extend j) x)) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) at hTypes
    rw [hLhsTy, hRhsTy] at hTypes
    injection hTypes with _ hNumerals
    injection hNumerals
  exact ⟨w, iv, jv, kv, hI, hJ, hK, hw0, hiv0, hjv0, hkv0,
    hWidths, hXSmtTy⟩

private theorem typed_bv_merge_sign_extend_1_term
    (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvMergeSignExtend1Term x i j k) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvMergeSignExtend1Term x i j k) := by
  intro hXTrans hResultTy
  rcases bv_merge_sign_extend_1_context x i j k hXTrans hResultTy with
    ⟨w, iv, jv, kv, rfl, rfl, rfl, hw0, hiv0, hjv0, hkv0,
      hWidths, hXSmtTy⟩
  have hInnerWidth0 :
      native_zleq 0 (native_zplus jv w) = true := by
    have hw : (0 : Int) ≤ w := by
      simpa [SmtEval.native_zleq] using hw0
    have hj : (0 : Int) ≤ jv := by
      simpa [SmtEval.native_zleq] using hjv0
    have hsimpa :=
      Int.add_nonneg hj hw
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.UOp1 UserOp1.sign_extend (Term.Numeral jv)) x)) =
        SmtType.BitVec (native_int_to_nat (native_zplus jv w)) :=
    smt_typeof_sign_extend_of_context x w jv hXSmtTy hw0 hjv0
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMergeSignExtend1Lhs x (Term.Numeral iv)
              (Term.Numeral jv))) =
        SmtType.BitVec
          (native_int_to_nat
            (native_zplus iv (native_zplus jv w))) := by
    unfold bvMergeSignExtend1Lhs
    exact smt_typeof_sign_extend_of_context
      (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral jv)) x)
      (native_zplus jv w) iv hInnerTy hInnerWidth0 hiv0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt (bvMergeSignExtend1Rhs x (Term.Numeral kv))) =
        SmtType.BitVec (native_int_to_nat (native_zplus kv w)) := by
    unfold bvMergeSignExtend1Rhs
    exact smt_typeof_sign_extend_of_context x w kv hXSmtTy hw0 hkv0
  have hWidthInt :
      native_zplus iv (native_zplus jv w) = native_zplus kv w := by
    simp only [SmtEval.native_zplus] at hWidths ⊢
    calc
      iv + (jv + w) = (w + jv) + iv := by ac_rfl
      _ = w + kv := hWidths
      _ = kv + w := Int.add_comm w kv
  have hWidthNat :
      native_int_to_nat (native_zplus iv (native_zplus jv w)) =
        native_int_to_nat (native_zplus kv w) :=
    congrArg native_int_to_nat hWidthInt
  unfold bvMergeSignExtend1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLhsTy, hRhsTy, hWidthNat])
    (by rw [hLhsTy]; intro h; cases h)

private theorem smtx_eval_plus_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus x y) =
      __smtx_model_eval_plus
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

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

private theorem bv_merge_sign_extend_1_index_eq_of_premise
    (M : SmtModel) (iv jv kv : native_Int) :
    eo_interprets M
        (bvMergeSignExtend1Prem (Term.Numeral iv)
          (Term.Numeral jv) (Term.Numeral kv)) true ->
    kv = native_zplus iv jv := by
  intro hPrem
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvMergeSignExtend1Prem (Term.Numeral iv)
              (Term.Numeral jv) (Term.Numeral kv))) =
        SmtValue.Boolean (native_zeq kv (native_zplus iv jv)) := by
    unfold bvMergeSignExtend1Prem
    change __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.Numeral kv)
          (SmtTerm.plus (SmtTerm.Numeral iv)
            (SmtTerm.plus (SmtTerm.Numeral jv) (SmtTerm.Numeral 0)))) = _
    rw [smtx_eval_eq_term_eq, smtx_eval_plus_term_eq,
      smtx_eval_plus_term_eq]
    simp [__smtx_model_eval, __smtx_model_eval_plus,
      __smtx_model_eval_eq, native_veq, SmtEval.native_zplus,
      SmtEval.native_zeq]
    rfl
  have hEq := bool_of_true_eval hPrem hEval
  simpa [SmtEval.native_zeq] using hEq

private theorem bitvec_sign_extend_compose
    (x : BitVec W) (I J : Nat) :
    (x.signExtend (J + W)).signExtend (I + J + W) =
      x.signExtend (I + J + W) := by
  apply BitVec.eq_of_toInt_eq
  calc
    ((x.signExtend (J + W)).signExtend (I + J + W)).toInt =
        (x.signExtend (J + W)).toInt :=
      BitVec.toInt_signExtend_of_le (by omega)
    _ = x.toInt := BitVec.toInt_signExtend_of_le (by omega)
    _ = (x.signExtend (I + J + W)).toInt :=
      (BitVec.toInt_signExtend_of_le (by omega)).symm

private theorem sign_extend_compose_value
    (W I J : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_model_eval_sign_extend (SmtValue.Numeral (I : Int))
        (__smtx_model_eval_sign_extend (SmtValue.Numeral (J : Int))
          (SmtValue.Binary (W : Int) p)) =
      __smtx_model_eval_sign_extend (SmtValue.Numeral ((I + J : Nat) : Int))
        (SmtValue.Binary (W : Int) p) := by
  let x := BitVec.ofInt W p
  let sx := x.signExtend (J + W)
  have hsx0 : (0 : Int) ≤ (sx.toNat : Int) := Int.natCast_nonneg _
  have hsx1 : (sx.toNat : Int) < (2 : Int) ^ (J + W) := by
    exact_mod_cast sx.isLt
  rw [sign_extend_val_bitvec W J p hp0 hp1]
  rw [sign_extend_val_bitvec (J + W) I (sx.toNat : Int) hsx0 hsx1]
  rw [sign_extend_val_bitvec W (I + J) p hp0 hp1]
  have hSxOf : BitVec.ofInt (J + W) (sx.toNat : Int) = sx :=
    bitvec_ofInt_natCast_toNat sx
  rw [hSxOf]
  have hAssoc : I + (J + W) = I + J + W := (Nat.add_assoc I J W).symm
  rw [hAssoc]
  exact congrArg
    (fun z => SmtValue.Binary ((I + J + W : Nat) : Int) (z.toNat : Int))
    (bitvec_sign_extend_compose x I J)

private theorem eval_bv_merge_sign_extend_1
    (M : SmtModel) (hM : model_wf M) (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    eo_interprets M (bvMergeSignExtend1Prem i j k) true ->
    __eo_typeof (bvMergeSignExtend1Term x i j k) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt (bvMergeSignExtend1Lhs x i j)) =
      __smtx_model_eval M (__eo_to_smt (bvMergeSignExtend1Rhs x k)) := by
  intro hXTrans hPrem hResultTy
  rcases bv_merge_sign_extend_1_context x i j k hXTrans hResultTy with
    ⟨w, iv, jv, kv, rfl, rfl, rfl, hw0, hiv0, hjv0, _hkv0,
      _hWidths, hXSmtTy⟩
  have hIndex := bv_merge_sign_extend_1_index_eq_of_premise M iv jv kv hPrem
  let W := native_int_to_nat w
  let I := native_int_to_nat iv
  let J := native_int_to_nat jv
  have hWRound : (W : Int) = w := by
    simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hIRound : (I : Int) = iv := by
    simpa [I, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip iv hiv0
  have hJRound : (J : Int) = jv := by
    simpa [J, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip jv hjv0
  have hKRound : ((I + J : Nat) : Int) = kv := by
    calc
      ((I + J : Nat) : Int) = (I : Int) + (J : Int) := by norm_cast
      _ = iv + jv := by rw [hIRound, hJRound]
      _ = kv := by
        rw [hIndex]
        rfl
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with ⟨p, hXEval, hCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary (W : Int) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval
  have hWidth0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int]
      using hRange.2
  unfold bvMergeSignExtend1Lhs bvMergeSignExtend1Rhs
  rw [eval_sign_extend_term, eval_sign_extend_term, eval_sign_extend_term,
    hXEval']
  simpa [hIRound, hJRound, hKRound] using
    sign_extend_compose_value W I J p hp0 hp1

private theorem facts_bv_merge_sign_extend_1_term
    (M : SmtModel) (hM : model_wf M) (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    eo_interprets M (bvMergeSignExtend1Prem i j k) true ->
    __eo_typeof (bvMergeSignExtend1Term x i j k) = Term.Bool ->
    eo_interprets M (bvMergeSignExtend1Term x i j k) true := by
  intro hXTrans hPrem hResultTy
  have hBool := typed_bv_merge_sign_extend_1_term x i j k
    hXTrans hResultTy
  unfold bvMergeSignExtend1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvMergeSignExtend1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (bvMergeSignExtend1Lhs x i j)))
      (__smtx_model_eval M (__eo_to_smt (bvMergeSignExtend1Rhs x k)))
    rw [eval_bv_merge_sign_extend_1 M hM x i j k hXTrans hPrem hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvMergeSignExtend1Program (x i j k : Term) : Term :=
  __eo_prog_bv_merge_sign_extend_1 x i j k
    (Proof.pf (bvMergeSignExtend1Prem i j k))

theorem bv_merge_sign_extend_1_program_eq_term_of_ne_stuck
    (x i j k : Term) :
    x ≠ Term.Stuck -> i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    k ≠ Term.Stuck ->
    bvMergeSignExtend1Program x i j k =
      bvMergeSignExtend1Term x i j k := by
  intro hXNe hINe hJNe hKNe
  unfold bvMergeSignExtend1Program bvMergeSignExtend1Prem
  rw [__eo_prog_bv_merge_sign_extend_1.eq_5
    x i j k k i j hXNe hINe hJNe hKNe]
  simp [bvMergeSignExtend1Term, bvMergeSignExtend1Lhs,
    bvMergeSignExtend1Rhs, __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, SmtEval.native_and, hINe, hJNe, hKNe]

theorem bv_merge_sign_extend_1_shape_of_ne_stuck
    (x i j k P : Term) :
    __eo_prog_bv_merge_sign_extend_1 x i j k (Proof.pf P) ≠
      Term.Stuck ->
    x ≠ Term.Stuck ∧ i ≠ Term.Stuck ∧ j ≠ Term.Stuck ∧
      k ≠ Term.Stuck ∧
      ∃ pk pi pj, P = bvMergeSignExtend1Prem pi pj pk := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg
      (__eo_prog_bv_merge_sign_extend_1.eq_1 i j k (Proof.pf P))
  have hINe : i ≠ Term.Stuck := by
    intro hI
    subst i
    exact hProg
      (__eo_prog_bv_merge_sign_extend_1.eq_2 x j k (Proof.pf P) hXNe)
  have hJNe : j ≠ Term.Stuck := by
    intro hJ
    subst j
    exact hProg
      (__eo_prog_bv_merge_sign_extend_1.eq_3 x i k (Proof.pf P)
        hXNe hINe)
  have hKNe : k ≠ Term.Stuck := by
    intro hK
    subst k
    exact hProg
      (__eo_prog_bv_merge_sign_extend_1.eq_4 x i j (Proof.pf P)
        hXNe hINe hJNe)
  refine ⟨hXNe, hINe, hJNe, hKNe, ?_⟩
  by_cases hShape :
      ∃ pk pi pj, P = bvMergeSignExtend1Prem pi pj pk
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_merge_sign_extend_1.eq_6 x i j k (Proof.pf P)
        hXNe hINe hJNe hKNe (by
          intro pk pi pj hP
          cases hP
          exact hShape ⟨pk, pi, pj, rfl⟩)))

private theorem eo_and_eq_true_args (a b : Term) :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not, native_and, SmtEval.native_and]
      at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [hW] at h

theorem bv_merge_sign_extend_1_guard_eqs
    (x i j k pk pi pj body : Term) :
    __eo_requires
        (__eo_and (__eo_and (__eo_eq k pk) (__eo_eq i pi))
          (__eo_eq j pj))
        (Term.Boolean true) body ≠ Term.Stuck ->
    pk = k ∧ pi = i ∧ pj = j := by
  intro hReq
  have hGuard :
      __eo_and (__eo_and (__eo_eq k pk) (__eo_eq i pi))
          (__eo_eq j pj) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReq
  rcases eo_and_eq_true_args _ _ hGuard with ⟨hInner, hJ⟩
  rcases eo_and_eq_true_args _ _ hInner with ⟨hK, hI⟩
  exact ⟨support_eq_of_eo_eq_true k pk hK,
    support_eq_of_eo_eq_true i pi hI,
    support_eq_of_eo_eq_true j pj hJ⟩

theorem typed_bv_merge_sign_extend_1_program (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation k ->
    __eo_typeof (bvMergeSignExtend1Program x i j k) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvMergeSignExtend1Program x i j k) := by
  intro hXTrans hITrans hJTrans hKTrans hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hINe := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJNe := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hKNe := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  have hEq := bv_merge_sign_extend_1_program_eq_term_of_ne_stuck
    x i j k hXNe hINe hJNe hKNe
  have hTermTy : __eo_typeof (bvMergeSignExtend1Term x i j k) =
      Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_merge_sign_extend_1_term x i j k hXTrans hTermTy

theorem facts_bv_merge_sign_extend_1_program
    (M : SmtModel) (hM : model_wf M) (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation k ->
    eo_interprets M (bvMergeSignExtend1Prem i j k) true ->
    __eo_typeof (bvMergeSignExtend1Program x i j k) = Term.Bool ->
    eo_interprets M (bvMergeSignExtend1Program x i j k) true := by
  intro hXTrans hITrans hJTrans hKTrans hPrem hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hINe := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJNe := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hKNe := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  have hEq := bv_merge_sign_extend_1_program_eq_term_of_ne_stuck
    x i j k hXNe hINe hJNe hKNe
  have hTermTy : __eo_typeof (bvMergeSignExtend1Term x i j k) =
      Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_merge_sign_extend_1_term M hM x i j k
    hXTrans hPrem hTermTy

/-! The companion merge through a positive zero extension. -/

def bvMergeSignExtend2Lhs (x i j : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.sign_extend i)
    (Term.Apply (Term.UOp1 UserOp1.zero_extend j) x)

def bvMergeSignExtend2Rhs (x k : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.zero_extend k) x

def bvMergeSignExtend2Term (x i j k : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvMergeSignExtend2Lhs x i j)) (bvMergeSignExtend2Rhs x k)

def bvMergeSignExtend2PremPos (j : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) j) (Term.Numeral 0)))
    (Term.Boolean true)

def bvMergeSignExtend2PremSum (i j k : Term) : Term :=
  bvMergeSignExtend1Prem i j k

private theorem zero_extend_amount_context
    (x k widthTerm : Term) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) widthTerm ->
    __eo_typeof (Term.Apply (Term.UOp1 UserOp1.zero_extend k) x) ≠
      Term.Stuck ->
    ∃ a : native_Int,
      k = Term.Numeral a ∧ native_zleq 0 a = true := by
  intro hXTy hExtendNe
  change __eo_typeof_zero_extend (__eo_typeof k) k (__eo_typeof x) ≠
      Term.Stuck at hExtendNe
  rw [hXTy] at hExtendNe
  have hParts :
      __eo_typeof k = Term.UOp UserOp.Int ∧
      __eo_requires (__eo_gt k (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec)
            (__eo_add widthTerm k)) ≠ Term.Stuck := by
    unfold __eo_typeof_zero_extend at hExtendNe
    split at hExtendNe <;> simp_all
  have hGuard :
      __eo_gt k (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hParts.2
  rcases sign_numeral_nonneg_of_gt_neg_one k hGuard with ⟨a, hK, ha0⟩
  exact ⟨a, hK, ha0⟩

private theorem zero_extend_full_context
    (x k : Term) (w : native_Int) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    __eo_typeof (Term.Apply (Term.UOp1 UserOp1.zero_extend k) x) ≠
      Term.Stuck ->
    ∃ a : native_Int,
      k = Term.Numeral a ∧ native_zleq 0 a = true ∧
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.zero_extend k) x) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus w a)) := by
  intro hXTy hExtendNe
  rcases zero_extend_amount_context x k (Term.Numeral w) hXTy hExtendNe with
    ⟨a, hK, ha0⟩
  subst k
  have hLt : native_zlt (-1 : native_Int) a = true := by
    have ha : (0 : Int) ≤ a := by
      simpa [SmtEval.native_zleq] using ha0
    have : (-1 : Int) < a := by omega
    simpa [SmtEval.native_zlt] using this
  refine ⟨a, rfl, ha0, ?_⟩
  change __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral a)
      (__eo_typeof x) = _
  rw [hXTy]
  simp [__eo_typeof_zero_extend, __eo_requires, __eo_gt, __eo_add,
    __eo_mk_apply, hLt, native_ite, native_teq, native_not]

private theorem bv_merge_sign_extend_2_context
    (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvMergeSignExtend2Term x i j k) = Term.Bool ->
    ∃ w iv jv kv : native_Int,
      i = Term.Numeral iv ∧ j = Term.Numeral jv ∧
      k = Term.Numeral kv ∧
      native_zleq 0 w = true ∧ native_zleq 0 iv = true ∧
      native_zleq 0 jv = true ∧ native_zleq 0 kv = true ∧
      native_zplus (native_zplus w jv) iv = native_zplus w kv ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvMergeSignExtend2Lhs x i j))
      (__eo_typeof (bvMergeSignExtend2Rhs x k)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hRhsCore :
      __eo_typeof_zero_extend (__eo_typeof k) k (__eo_typeof x) ≠
        Term.Stuck := by
    exact hRhsNe
  rcases eo_typeof_sign_extend_arg_bitvec_of_ne_stuck hRhsCore with
    ⟨widthTerm, hXTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x widthTerm
      hXTrans hXTy with ⟨w, hWidth, hw0, hXSmtTy⟩
  subst widthTerm
  rcases zero_extend_full_context x k w hXTy hRhsNe with
    ⟨kv, hK, hkv0, hRhsTy⟩
  have hLhsCore :
      __eo_typeof_zero_extend (__eo_typeof i) i
          (__eo_typeof
            (Term.Apply (Term.UOp1 UserOp1.zero_extend j) x)) ≠
        Term.Stuck := by
    exact hLhsNe
  rcases eo_typeof_sign_extend_arg_bitvec_of_ne_stuck hLhsCore with
    ⟨innerWidth, hInnerTyRaw⟩
  have hInnerNe :
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.zero_extend j) x) ≠
        Term.Stuck := by
    rw [hInnerTyRaw]
    intro h
    cases h
  rcases zero_extend_full_context x j w hXTy hInnerNe with
    ⟨jv, hJ, hjv0, hInnerTy⟩
  rcases sign_extend_full_context
      (Term.Apply (Term.UOp1 UserOp1.zero_extend j) x) i
      (native_zplus w jv) hInnerTy hLhsNe with
    ⟨iv, hI, hiv0, hLhsTy⟩
  have hTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hWidths :
      native_zplus (native_zplus w jv) iv = native_zplus w kv := by
    change __eo_typeof
        (Term.Apply (Term.UOp1 UserOp1.sign_extend i)
          (Term.Apply (Term.UOp1 UserOp1.zero_extend j) x)) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.zero_extend k) x) at hTypes
    rw [hLhsTy, hRhsTy] at hTypes
    injection hTypes with _ hNumerals
    injection hNumerals
  exact ⟨w, iv, jv, kv, hI, hJ, hK, hw0, hiv0, hjv0, hkv0,
    hWidths, hXSmtTy⟩

private theorem smt_typeof_zero_extend_of_context
    (x : Term) (w a : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ->
    native_zleq 0 w = true ->
    native_zleq 0 a = true ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral a)) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus a w)) := by
  intro hXTy hw0 ha0
  have hRound := native_int_to_nat_roundtrip w hw0
  change __smtx_typeof
      (SmtTerm.zero_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [typeof_zero_extend_eq, hXTy]
  simp [__smtx_typeof_zero_extend, native_ite, ha0, hRound]

private theorem typed_bv_merge_sign_extend_2_term
    (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvMergeSignExtend2Term x i j k) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvMergeSignExtend2Term x i j k) := by
  intro hXTrans hResultTy
  rcases bv_merge_sign_extend_2_context x i j k hXTrans hResultTy with
    ⟨w, iv, jv, kv, rfl, rfl, rfl, hw0, hiv0, hjv0, hkv0,
      hWidths, hXSmtTy⟩
  have hInnerWidth0 :
      native_zleq 0 (native_zplus jv w) = true := by
    have hw : (0 : Int) ≤ w := by
      simpa [SmtEval.native_zleq] using hw0
    have hj : (0 : Int) ≤ jv := by
      simpa [SmtEval.native_zleq] using hjv0
    have hsimpa :=
      Int.add_nonneg hj hw
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.UOp1 UserOp1.zero_extend (Term.Numeral jv)) x)) =
        SmtType.BitVec (native_int_to_nat (native_zplus jv w)) :=
    smt_typeof_zero_extend_of_context x w jv hXSmtTy hw0 hjv0
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMergeSignExtend2Lhs x (Term.Numeral iv)
              (Term.Numeral jv))) =
        SmtType.BitVec
          (native_int_to_nat
            (native_zplus iv (native_zplus jv w))) := by
    unfold bvMergeSignExtend2Lhs
    exact smt_typeof_sign_extend_of_context
      (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral jv)) x)
      (native_zplus jv w) iv hInnerTy hInnerWidth0 hiv0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt (bvMergeSignExtend2Rhs x (Term.Numeral kv))) =
        SmtType.BitVec (native_int_to_nat (native_zplus kv w)) := by
    unfold bvMergeSignExtend2Rhs
    exact smt_typeof_zero_extend_of_context x w kv hXSmtTy hw0 hkv0
  have hWidthInt :
      native_zplus iv (native_zplus jv w) = native_zplus kv w := by
    simp only [SmtEval.native_zplus] at hWidths ⊢
    calc
      iv + (jv + w) = (w + jv) + iv := by ac_rfl
      _ = w + kv := hWidths
      _ = kv + w := Int.add_comm w kv
  have hWidthNat :
      native_int_to_nat (native_zplus iv (native_zplus jv w)) =
        native_int_to_nat (native_zplus kv w) :=
    congrArg native_int_to_nat hWidthInt
  unfold bvMergeSignExtend2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLhsTy, hRhsTy, hWidthNat])
    (by rw [hLhsTy]; intro h; cases h)

private theorem smtx_eval_gt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt x y) =
      __smtx_model_eval_gt
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem bv_merge_sign_extend_2_pos_of_premise
    (M : SmtModel) (jv : native_Int) :
    eo_interprets M
        (bvMergeSignExtend2PremPos (Term.Numeral jv)) true ->
    native_zlt 0 jv = true := by
  intro hPrem
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvMergeSignExtend2PremPos (Term.Numeral jv))) =
        SmtValue.Boolean (native_zlt 0 jv) := by
    unfold bvMergeSignExtend2PremPos
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.gt (SmtTerm.Numeral jv) (SmtTerm.Numeral 0))
          (SmtTerm.Boolean true)) = _
    rw [smtx_eval_eq_term_eq, smtx_eval_gt_term_eq]
    simp [__smtx_model_eval, __smtx_model_eval_gt,
      __smtx_model_eval_lt, __smtx_model_eval_eq, native_veq,
      SmtEval.native_zlt]
  exact bool_of_true_eval hPrem hEval

private theorem eval_zero_extend_term
    (M : SmtModel) (x : Term) (a : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral a)) x)) =
      __smtx_model_eval_zero_extend (SmtValue.Numeral a)
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M
      (SmtTerm.zero_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  simp [__smtx_model_eval]

private theorem sign_extend_zero_extend_value
    (W I J : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hJPos : 0 < J) :
    __smtx_model_eval_sign_extend (SmtValue.Numeral (I : Int))
        (__smtx_model_eval_zero_extend (SmtValue.Numeral (J : Int))
          (SmtValue.Binary (W : Int) p)) =
      __smtx_model_eval_zero_extend
        (SmtValue.Numeral ((I + J : Nat) : Int))
        (SmtValue.Binary (W : Int) p) := by
  have hJW : (J : Int) + (W : Int) = ((J + W : Nat) : Int) := by
    norm_cast
  have hTotal : ((I + J : Nat) : Int) + (W : Int) =
      ((I + J + W : Nat) : Int) := by
    norm_cast
  simp only [__smtx_model_eval_zero_extend, SmtEval.native_zplus]
  rw [hJW, hTotal]
  have hPowJW : (2 : Int) ^ W ≤ (2 : Int) ^ (J + W) := by
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : W ≤ J + W))
  have hpJW : p < (2 : Int) ^ (J + W) :=
    Int.lt_of_lt_of_le hp1 hPowJW
  rw [sign_extend_val_bitvec (J + W) I p hp0 hpJW]
  let inner := BitVec.ofInt (J + W) p
  let total := I + J + W
  have hHalfExp : W ≤ J + W - 1 := by omega
  have hHalfPow : (2 : Int) ^ W ≤ (2 : Int) ^ (J + W - 1) := by
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 0 < 2) hHalfExp)
  have hpHalf : p < (2 : Int) ^ (J + W - 1) :=
    Int.lt_of_lt_of_le hp1 hHalfPow
  have hInnerToInt : inner.toInt = p := by
    apply BitVec.toInt_ofInt_eq_self (by omega)
    · have hPow0 : (0 : Int) ≤ (2 : Int) ^ (J + W - 1) :=
        Int.le_of_lt (Int.pow_pos (by decide))
      omega
    · exact hpHalf
  have hTotalExp : W ≤ total - 1 := by
    simp [total]
    omega
  have hTotalHalfPow : (2 : Int) ^ W ≤ (2 : Int) ^ (total - 1) := by
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 0 < 2) hTotalExp)
  have hpTotalHalf : p < (2 : Int) ^ (total - 1) :=
    Int.lt_of_lt_of_le hp1 hTotalHalfPow
  have hDirectToInt : (BitVec.ofInt total p).toInt = p := by
    apply BitVec.toInt_ofInt_eq_self (by simp [total]; omega)
    · have hPow0 : (0 : Int) ≤ (2 : Int) ^ (total - 1) :=
        Int.le_of_lt (Int.pow_pos (by decide))
      omega
    · exact hpTotalHalf
  have hSignEq : inner.signExtend total = BitVec.ofInt total p := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by simp [inner, total]),
      hInnerToInt, hDirectToInt]
  have hPowTotal : (2 : Int) ^ W ≤ (2 : Int) ^ total := by
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by simp [total]))
  have hpTotal : p < (2 : Int) ^ total :=
    Int.lt_of_lt_of_le hp1 hPowTotal
  have hDirectNat : (BitVec.ofInt total p).toNat = p.toNat :=
    ofInt_toNat_canonical total p hp0 hpTotal
  have hpCast : (p.toNat : Int) = p := Int.toNat_of_nonneg hp0
  have hAssoc : I + (J + W) = total := by
    simp [total, Nat.add_assoc]
  rw [hAssoc]
  change SmtValue.Binary (total : Int)
      ((inner.signExtend total).toNat : Int) =
    SmtValue.Binary (total : Int) p
  rw [hSignEq, hDirectNat, hpCast]

private theorem eval_bv_merge_sign_extend_2
    (M : SmtModel) (hM : model_wf M) (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    eo_interprets M (bvMergeSignExtend2PremPos j) true ->
    eo_interprets M (bvMergeSignExtend2PremSum i j k) true ->
    __eo_typeof (bvMergeSignExtend2Term x i j k) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt (bvMergeSignExtend2Lhs x i j)) =
      __smtx_model_eval M (__eo_to_smt (bvMergeSignExtend2Rhs x k)) := by
  intro hXTrans hPremPos hPremSum hResultTy
  rcases bv_merge_sign_extend_2_context x i j k hXTrans hResultTy with
    ⟨w, iv, jv, kv, rfl, rfl, rfl, hw0, hiv0, hjv0, _hkv0,
      _hWidths, hXSmtTy⟩
  have hIndex : kv = native_zplus iv jv :=
    bv_merge_sign_extend_1_index_eq_of_premise M iv jv kv
      (by simpa [bvMergeSignExtend2PremSum] using hPremSum)
  have hjPos := bv_merge_sign_extend_2_pos_of_premise M jv hPremPos
  let W := native_int_to_nat w
  let I := native_int_to_nat iv
  let J := native_int_to_nat jv
  have hWRound : (W : Int) = w := by
    simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hIRound : (I : Int) = iv := by
    simpa [I, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip iv hiv0
  have hJRound : (J : Int) = jv := by
    simpa [J, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip jv hjv0
  have hJPos : 0 < J := by
    have : (0 : Int) < jv := by
      simpa [SmtEval.native_zlt] using hjPos
    exact_mod_cast (show (0 : Int) < (J : Int) by simpa [hJRound] using this)
  have hKRound : ((I + J : Nat) : Int) = kv := by
    calc
      ((I + J : Nat) : Int) = (I : Int) + (J : Int) := by norm_cast
      _ = iv + jv := by rw [hIRound, hJRound]
      _ = kv := by
        simpa [SmtEval.native_zplus] using hIndex.symm
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with ⟨p, hXEval, hCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary (W : Int) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval
  have hWidth0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int]
      using hRange.2
  unfold bvMergeSignExtend2Lhs bvMergeSignExtend2Rhs
  rw [eval_sign_extend_term, eval_zero_extend_term, eval_zero_extend_term,
    hXEval']
  simpa [hIRound, hJRound, hKRound] using
    sign_extend_zero_extend_value W I J p hp0 hp1 hJPos

private theorem facts_bv_merge_sign_extend_2_term
    (M : SmtModel) (hM : model_wf M) (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    eo_interprets M (bvMergeSignExtend2PremPos j) true ->
    eo_interprets M (bvMergeSignExtend2PremSum i j k) true ->
    __eo_typeof (bvMergeSignExtend2Term x i j k) = Term.Bool ->
    eo_interprets M (bvMergeSignExtend2Term x i j k) true := by
  intro hXTrans hPremPos hPremSum hResultTy
  have hBool := typed_bv_merge_sign_extend_2_term x i j k
    hXTrans hResultTy
  unfold bvMergeSignExtend2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvMergeSignExtend2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (bvMergeSignExtend2Lhs x i j)))
      (__smtx_model_eval M (__eo_to_smt (bvMergeSignExtend2Rhs x k)))
    rw [eval_bv_merge_sign_extend_2 M hM x i j k hXTrans
      hPremPos hPremSum hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvMergeSignExtend2Program (x i j k : Term) : Term :=
  __eo_prog_bv_merge_sign_extend_2 x i j k
    (Proof.pf (bvMergeSignExtend2PremPos j))
    (Proof.pf (bvMergeSignExtend2PremSum i j k))

theorem bv_merge_sign_extend_2_program_eq_term_of_ne_stuck
    (x i j k : Term) :
    x ≠ Term.Stuck -> i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    k ≠ Term.Stuck ->
    bvMergeSignExtend2Program x i j k =
      bvMergeSignExtend2Term x i j k := by
  intro hXNe hINe hJNe hKNe
  unfold bvMergeSignExtend2Program bvMergeSignExtend2PremPos
    bvMergeSignExtend2PremSum bvMergeSignExtend1Prem
  rw [__eo_prog_bv_merge_sign_extend_2.eq_5
    x i j k j k i j hXNe hINe hJNe hKNe]
  simp [bvMergeSignExtend2Term, bvMergeSignExtend2Lhs,
    bvMergeSignExtend2Rhs, __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, SmtEval.native_and, hINe, hJNe, hKNe]

theorem bv_merge_sign_extend_2_shape_of_ne_stuck
    (x i j k P1 P2 : Term) :
    __eo_prog_bv_merge_sign_extend_2 x i j k
        (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ i ≠ Term.Stuck ∧ j ≠ Term.Stuck ∧
      k ≠ Term.Stuck ∧
      ∃ pjPos pk pi pjSum,
        P1 = bvMergeSignExtend2PremPos pjPos ∧
        P2 = bvMergeSignExtend2PremSum pi pjSum pk := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg
      (__eo_prog_bv_merge_sign_extend_2.eq_1 i j k
        (Proof.pf P1) (Proof.pf P2))
  have hINe : i ≠ Term.Stuck := by
    intro hI
    subst i
    exact hProg
      (__eo_prog_bv_merge_sign_extend_2.eq_2 x j k
        (Proof.pf P1) (Proof.pf P2) hXNe)
  have hJNe : j ≠ Term.Stuck := by
    intro hJ
    subst j
    exact hProg
      (__eo_prog_bv_merge_sign_extend_2.eq_3 x i k
        (Proof.pf P1) (Proof.pf P2) hXNe hINe)
  have hKNe : k ≠ Term.Stuck := by
    intro hK
    subst k
    exact hProg
      (__eo_prog_bv_merge_sign_extend_2.eq_4 x i j
        (Proof.pf P1) (Proof.pf P2) hXNe hINe hJNe)
  refine ⟨hXNe, hINe, hJNe, hKNe, ?_⟩
  by_cases hShape :
      ∃ pjPos pk pi pjSum,
        P1 = bvMergeSignExtend2PremPos pjPos ∧
        P2 = bvMergeSignExtend2PremSum pi pjSum pk
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_merge_sign_extend_2.eq_6 x i j k
        (Proof.pf P1) (Proof.pf P2) hXNe hINe hJNe hKNe (by
          intro pjPos pk pi pjSum hP1 hP2
          cases hP1
          cases hP2
          exact hShape ⟨pjPos, pk, pi, pjSum, rfl, rfl⟩)))

theorem bv_merge_sign_extend_2_guard_eqs
    (x i j k pjPos pk pi pjSum body : Term) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq j pjPos) (__eo_eq k pk))
            (__eo_eq i pi))
          (__eo_eq j pjSum))
        (Term.Boolean true) body ≠ Term.Stuck ->
    pjPos = j ∧ pk = k ∧ pi = i ∧ pjSum = j := by
  intro hReq
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and (__eo_eq j pjPos) (__eo_eq k pk))
            (__eo_eq i pi))
          (__eo_eq j pjSum) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReq
  rcases eo_and_eq_true_args _ _ hGuard with ⟨hFirst3, hJSum⟩
  rcases eo_and_eq_true_args _ _ hFirst3 with ⟨hFirst2, hI⟩
  rcases eo_and_eq_true_args _ _ hFirst2 with ⟨hJPos, hK⟩
  exact ⟨support_eq_of_eo_eq_true j pjPos hJPos,
    support_eq_of_eo_eq_true k pk hK,
    support_eq_of_eo_eq_true i pi hI,
    support_eq_of_eo_eq_true j pjSum hJSum⟩

theorem typed_bv_merge_sign_extend_2_program (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation k ->
    __eo_typeof (bvMergeSignExtend2Program x i j k) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvMergeSignExtend2Program x i j k) := by
  intro hXTrans hITrans hJTrans hKTrans hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hINe := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJNe := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hKNe := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  have hEq := bv_merge_sign_extend_2_program_eq_term_of_ne_stuck
    x i j k hXNe hINe hJNe hKNe
  have hTermTy : __eo_typeof (bvMergeSignExtend2Term x i j k) =
      Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_merge_sign_extend_2_term x i j k hXTrans hTermTy

theorem facts_bv_merge_sign_extend_2_program
    (M : SmtModel) (hM : model_wf M) (x i j k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation k ->
    eo_interprets M (bvMergeSignExtend2PremPos j) true ->
    eo_interprets M (bvMergeSignExtend2PremSum i j k) true ->
    __eo_typeof (bvMergeSignExtend2Program x i j k) = Term.Bool ->
    eo_interprets M (bvMergeSignExtend2Program x i j k) true := by
  intro hXTrans hITrans hJTrans hKTrans hPremPos hPremSum hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hINe := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJNe := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hKNe := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  have hEq := bv_merge_sign_extend_2_program_eq_term_of_ne_stuck
    x i j k hXNe hINe hJNe hKNe
  have hTermTy : __eo_typeof (bvMergeSignExtend2Term x i j k) =
      Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_merge_sign_extend_2_term M hM x i j k
    hXTrans hPremPos hPremSum hTermTy
