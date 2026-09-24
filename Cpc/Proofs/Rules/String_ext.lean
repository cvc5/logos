module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-! ### Core math: two equal-length unequal lists differ at an in-bounds index. -/

private theorem list_diff_at_index :
    ∀ (xs ys : List SmtValue), xs.length = ys.length → xs ≠ ys →
      ∃ i : Nat, i < xs.length ∧ (xs.drop i).take 1 ≠ (ys.drop i).take 1
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hne => by
      by_cases hxy : x = y
      · subst hxy
        have htl : xs ≠ ys := fun h => hne (by rw [h])
        have hlen' : xs.length = ys.length := by simpa using hlen
        obtain ⟨i, hi, hdiff⟩ := list_diff_at_index xs ys hlen' htl
        refine ⟨i + 1, ?_, ?_⟩
        · simpa using Nat.succ_lt_succ hi
        · simpa using hdiff
      · refine ⟨0, by simp, ?_⟩
        simp only [List.drop_zero, List.take_succ_cons, List.take_zero]
        intro h
        exact hxy (by simpa using h)

/-- For an in-bounds (Nat) index, `native_seq_extract` returns the length-1 slice there. -/
private theorem native_seq_extract_one_nat (xs : List SmtValue) (j : Nat)
    (hj : j < xs.length) :
    native_seq_extract xs (Int.ofNat j) 1 = (xs.drop j).take 1 := by
  have e1 : decide ((Int.ofNat j : native_Int) < 0) = false :=
    decide_eq_false (show ¬ ((j : Int) < 0) by omega)
  have e2 : decide ((1 : native_Int) ≤ 0) = false := by decide
  have e3 : decide ((Int.ofNat j : native_Int) ≥ Int.ofNat xs.length) = false :=
    decide_eq_false (show ¬ ((j : Int) ≥ (xs.length : Int)) by omega)
  have h1 : (1 : Int) ≤ (xs.length : Int) - (j : Int) := by omega
  have hmin : min (1 : native_Int) (Int.ofNat xs.length - Int.ofNat j) = 1 :=
    Int.min_eq_left h1
  have htn : (Int.ofNat j : native_Int).toNat = j := rfl
  have htake : (min (1 : native_Int) (Int.ofNat xs.length - Int.ofNat j)).toNat = 1 := by
    rw [hmin]; exact Int.toNat_one
  simp only [native_seq_extract]
  rw [e1, e2, e3, htake, htn]
  simp

private theorem cmd_step_string_ext_one_eq
    (s : CState) (n : CIndex) :
    __eo_cmd_step_proven s CRule.string_ext CArgList.nil (CIndexList.cons n CIndexList.nil) =
      __eo_prog_string_ext (Proof.pf (__eo_state_proven_nth s n)) := by
  rfl

/-- From the deq_diff being Int-typed, extract equal Seq element types. -/
private theorem string_ext_deq_diff_int_imp_seq
    (a b : Term)
    (h : __eo_typeof__at_strings_deq_diff (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int) :
    ∃ A : Term, __eo_typeof a = Term.Apply (Term.UOp UserOp.Seq) A ∧
      __eo_typeof b = Term.Apply (Term.UOp UserOp.Seq) A := by
  cases hTA : __eo_typeof a with
  | Apply fA TA =>
    cases fA with
    | UOp opA =>
      cases opA with
      | Seq =>
        cases hTB : __eo_typeof b with
        | Apply fB TB =>
          cases fB with
          | UOp opB =>
            cases opB with
            | Seq =>
              rw [hTA, hTB] at h
              simp only [__eo_typeof__at_strings_deq_diff] at h
              have hEq : __eo_requires (__eo_eq TA TB) (Term.Boolean true)
                  (Term.UOp UserOp.Int) ≠ Term.Stuck := by
                rw [h]; simp
              have hBA : TB = TA :=
                RuleProofs.eq_of_requires_eq_true_not_stuck TA TB
                  (Term.UOp UserOp.Int) hEq
              subst TB
              exact ⟨TA, rfl, rfl⟩
            | _ => rw [hTA, hTB] at h; simp [__eo_typeof__at_strings_deq_diff] at h
          | _ => rw [hTA, hTB] at h; simp [__eo_typeof__at_strings_deq_diff] at h
        | _ => rw [hTA, hTB] at h; simp [__eo_typeof__at_strings_deq_diff] at h
      | _ => rw [hTA] at h; simp [__eo_typeof__at_strings_deq_diff] at h
    | _ => rw [hTA] at h; simp [__eo_typeof__at_strings_deq_diff] at h
  | _ => rw [hTA] at h; simp [__eo_typeof__at_strings_deq_diff] at h

private theorem eo_mk_apply_eq (x y : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_mk_apply x y = Term.Apply x y := by
  cases x <;> cases y <;> simp_all [__eo_mk_apply]

private theorem eo_to_smt_stuck_none : __eo_to_smt Term.Stuck = SmtTerm.None := rfl

private theorem ne_stuck_of_smt_typeof_seq (t : Term) (As : SmtType)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Seq As) : t ≠ Term.Stuck := by
  intro hs
  rw [hs, eo_to_smt_stuck_none, TranslationProofs.smtx_typeof_none] at h
  cases h

/-- `__str_mk_ext_deq` is non-stuck only when its 4th arg is a `Seq` type. -/
private theorem str_mk_ext_deq_ne_stuck_imp_seq
    (a b k T : Term)
    (h : __str_mk_ext_deq a b k T ≠ Term.Stuck) :
    ∃ A : Term, T = Term.Apply (Term.UOp UserOp.Seq) A := by
  by_cases ha : a = Term.Stuck
  · subst a; simp [__str_mk_ext_deq] at h
  by_cases hb : b = Term.Stuck
  · subst b; simp [__str_mk_ext_deq] at h
  by_cases hkS : k = Term.Stuck
  · subst k; simp [__str_mk_ext_deq] at h
  cases hT : T with
  | Apply fT TT =>
    cases fT with
    | UOp opT =>
      cases opT with
      | Seq => exact ⟨TT, rfl⟩
      | _ => simp [__str_mk_ext_deq, hT] at h
    | _ => simp [__str_mk_ext_deq, hT] at h
  | _ => simp [__str_mk_ext_deq, hT] at h

/-- The deq subterm of the `string_ext` conclusion. -/
private def stringExtDeq (a b A : Term) : Term :=
  __str_mk_ext_deq a b
    (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
    (Term.Apply (Term.UOp UserOp.Seq) A)

/-- The first disjunct of the `string_ext` conclusion. -/
private def stringExtD1 (a b : Term) : Term :=
  Term.Apply Term.not
    (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.UOp UserOp.str_len) a))
      (Term.Apply (Term.UOp UserOp.str_len) b))

/-- The bounds conjunct of the `string_ext` conclusion. -/
private def stringExtBounds (a b : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq) (Term.Numeral 0))
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.lt)
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
          (Term.Apply (Term.UOp UserOp.str_len) a)))
      (Term.Boolean true))

/-- Explicit (mk_apply-resolved) form of the `string_ext` conclusion. -/
private theorem prog_string_ext_explicit
    (a b A : Term)
    (hATy : __eo_typeof a = Term.Apply (Term.UOp UserOp.Seq) A)
    (hDeqNeStuck : stringExtDeq a b A ≠ Term.Stuck) :
    __eo_prog_string_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b))) =
      Term.Apply (Term.Apply (Term.UOp UserOp.or) (stringExtD1 a b))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.or)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) (stringExtDeq a b A))
              (stringExtBounds a b)))
          (Term.Boolean false)) := by
  have hDeq' : __str_mk_ext_deq a b
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
      (Term.Apply (Term.UOp UserOp.Seq) A) ≠ Term.Stuck := hDeqNeStuck
  simp only [__eo_prog_string_ext, stringExtD1, stringExtBounds, stringExtDeq]
  rw [hATy]
  rw [eo_mk_apply_eq (Term.UOp UserOp.and) _ (by simp) hDeq']
  rw [eo_mk_apply_eq (Term.Apply (Term.UOp UserOp.and)
      (__str_mk_ext_deq a b
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
        (Term.Apply (Term.UOp UserOp.Seq) A))) _ (by simp) (by simp)]
  rw [eo_mk_apply_eq (Term.UOp UserOp.or) _ (by simp) (by simp)]
  rw [eo_mk_apply_eq _ (Term.Boolean false) (by simp) (by simp)]
  rw [eo_mk_apply_eq ((Term.UOp UserOp.or).Apply
      ((Term.UOp UserOp.not).Apply
        (((Term.UOp UserOp.eq).Apply ((Term.UOp UserOp.str_len).Apply a)).Apply
          ((Term.UOp UserOp.str_len).Apply b)))) _ (by simp) (by simp)]

/-- From the result being Bool, extract equal Seq element types for `a` and `b`. -/
private theorem string_ext_result_imp_seq_types
    (a b : Term)
    (hResultTy :
      __eo_typeof
          (__eo_prog_string_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    ∃ A : Term, __eo_typeof a = Term.Apply (Term.UOp UserOp.Seq) A ∧
      __eo_typeof b = Term.Apply (Term.UOp UserOp.Seq) A := by
  -- the conclusion is not Stuck, so the deq subterm is not Stuck
  have hConclNeStuck := term_ne_stuck_of_typeof_bool hResultTy
  -- the deq subterm
  have hDeqNeStuck0 :
      __str_mk_ext_deq a b
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
        (__eo_typeof a) ≠ Term.Stuck := by
    intro hDeq
    apply hConclNeStuck
    simp only [__eo_prog_string_ext]
    rw [hDeq]
    simp [__eo_mk_apply]
  rcases str_mk_ext_deq_ne_stuck_imp_seq a b
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)
      (__eo_typeof a) hDeqNeStuck0 with ⟨A, hA⟩
  refine ⟨A, hA, ?_⟩
  have hDeqNeStuck : stringExtDeq a b A ≠ Term.Stuck := by
    rw [stringExtDeq, ← hA]; exact hDeqNeStuck0
  -- explicit form of the conclusion
  rw [prog_string_ext_explicit a b A hA hDeqNeStuck] at hResultTy
  -- reduce the typeof to its component form.
  change
    __eo_typeof_or
        (__eo_typeof_not
          (__eo_typeof_eq (__eo_typeof_str_len (__eo_typeof a))
            (__eo_typeof_str_len (__eo_typeof b))))
        (__eo_typeof_or
          (__eo_typeof_or (__eo_typeof (stringExtDeq a b A))
            (__eo_typeof_or
              (__eo_typeof_lt (Term.UOp UserOp.Int)
                (__eo_typeof__at_strings_deq_diff (__eo_typeof a) (__eo_typeof b)))
              (__eo_typeof_or
                (__eo_typeof_lt
                  (__eo_typeof__at_strings_deq_diff (__eo_typeof a) (__eo_typeof b))
                  (__eo_typeof_str_len (__eo_typeof a)))
                Term.Bool)))
          Term.Bool) =
      Term.Bool at hResultTy
  -- The `leq 0 k` component forces the deq_diff index to be Int.
  have hkInt : __eo_typeof__at_strings_deq_diff (__eo_typeof a) (__eo_typeof b) =
      Term.UOp UserOp.Int := by
    rw [hA] at hResultTy ⊢
    -- if not Int, the `lt`/`leq` components are Stuck and the `or` is Stuck.
    cases hkc : __eo_typeof__at_strings_deq_diff (Term.Apply (Term.UOp UserOp.Seq) A)
        (__eo_typeof b) with
    | UOp op =>
      cases op with
      | Int => rfl
      | _ =>
        exfalso; rw [hkc] at hResultTy
        simp [__eo_typeof_or, __eo_typeof_or, __eo_typeof_lt, __eo_typeof_str_len,
          __eo_requires, __eo_eq, native_ite, native_teq,
          ] at hResultTy
    | _ =>
      exfalso; rw [hkc] at hResultTy
      simp [__eo_typeof_or, __eo_typeof_or, __eo_typeof_lt, __eo_typeof_str_len,
        __eo_requires, __eo_eq, native_ite, native_teq,
        ] at hResultTy
  rcases string_ext_deq_diff_int_imp_seq a b hkInt with ⟨A', hA'a, hA'b⟩
  rw [hA] at hA'a
  have : A' = A := by
    have := hA'a; simp at this; exact this.symm
  rw [this] at hA'b
  exact hA'b


/-- Bundle of EO/SMT typing facts for a `string_ext` instance. -/
private theorem string_ext_smt_types
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))
    (hResultTy :
      __eo_typeof
          (__eo_prog_string_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    ∃ A : Term,
      let As := __eo_to_smt_type A
      __eo_typeof a = Term.Apply (Term.UOp UserOp.Seq) A ∧
        __eo_typeof b = Term.Apply (Term.UOp UserOp.Seq) A ∧
        __smtx_typeof (__eo_to_smt a) = SmtType.Seq As ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Seq As ∧
        As ≠ SmtType.None ∧
        RuleProofs.eo_has_smt_translation a ∧
        RuleProofs.eo_has_smt_translation b := by
  rcases string_ext_result_imp_seq_types a b hResultTy with ⟨A, hATy, hBTy⟩
  have hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq a) b) :=
    RuleProofs.eo_has_bool_type_not_arg _ hPremBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
    ⟨hSame, hANonNone⟩
  have hATrans : RuleProofs.eo_has_smt_translation a := hANonNone
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    rw [RuleProofs.eo_has_smt_translation]; rw [← hSame]; exact hANonNone
  have hSmtARaw :
      __smtx_typeof (__eo_to_smt a) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) A) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      a _ (__eo_to_smt a) rfl hATrans hATy
  have hSeqNonNone :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) A) ≠ SmtType.None := by
    rw [← hSmtARaw]; exact hATrans
  have hSeqTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) A) =
        SmtType.Seq (__eo_to_smt_type A) := by
    rw [TranslationProofs.eo_to_smt_type_seq] at hSeqNonNone ⊢
    generalize hAt : __eo_to_smt_type A = As at hSeqNonNone ⊢
    cases As <;> simp_all [__smtx_typeof_guard, native_ite, native_Teq]
  have hANonNone' : __eo_to_smt_type A ≠ SmtType.None := by
    intro hN
    rw [TranslationProofs.eo_to_smt_type_seq, hN] at hSeqNonNone
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hSeqNonNone
  have hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A) :=
    hSmtARaw.trans hSeqTy
  have hSmtB : __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type A) := by
    rw [← hSame]; exact hSmtA
  exact ⟨A, hATy, hBTy, hSmtA, hSmtB, hANonNone', hATrans, hBTrans⟩

/-- The SMT translation of the deq-diff index. -/
private theorem eo_to_smt_deq_diff_eq (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b) =
      SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

/-- The deq-diff index translates to an `Int`-typed SMT term. -/
private theorem deq_diff_smt_typeof_int
    (a b : Term) (A : Term)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A))
    (hSmtB : __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type A)) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
      SmtType.Int := by
  rw [eo_to_smt_deq_diff_eq, typeof_seq_diff_eq, hSmtA, hSmtB]
  simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]

/-- The SMT typeof of `str_len a` is `Int` when `a` is a sequence. -/
private theorem str_len_smt_typeof_int
    (a A : Term)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) a)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.str_len (__eo_to_smt a)) = SmtType.Int
  rw [typeof_str_len_eq, hSmtA]
  simp [__smtx_typeof_seq_op_1_ret]

/-- A `leq`/`lt` between two `Int`-typed terms is Boolean-typed. -/
private theorem eo_has_bool_type_leq_of_int_args
    (x y : Term)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) := by
  rw [RuleProofs.eo_has_bool_type]
  change __smtx_typeof (SmtTerm.leq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
  rw [typeof_leq_eq, hX, hY]
  simp [__smtx_typeof_arith_overload_op_2_ret]

private theorem eo_has_bool_type_lt_of_int_args
    (x y : Term)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) := by
  rw [RuleProofs.eo_has_bool_type]
  change __smtx_typeof (SmtTerm.lt (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
  rw [typeof_lt_eq, hX, hY]
  simp [__smtx_typeof_arith_overload_op_2_ret]

/-- `Numeral n` has SMT type `Int`. -/
private theorem numeral_smt_typeof_int (n : native_Int) :
    __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int
  rw [__smtx_typeof.eq_2]

/-- SMT typeof of `str_substr a k 1` is `Seq As` when `a : Seq As`. -/
private theorem str_substr_smt_typeof
    (a k : Term) (As : SmtType)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq As)
    (hSmtK : __smtx_typeof (__eo_to_smt k) = SmtType.Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) a) k)
            (Term.Numeral 1))) = SmtType.Seq As := by
  change __smtx_typeof (SmtTerm.str_substr (__eo_to_smt a) (__eo_to_smt k)
    (SmtTerm.Numeral 1)) = SmtType.Seq As
  rw [typeof_str_substr_eq, hSmtA, hSmtK]
  simp [__smtx_typeof_str_substr, __smtx_typeof]

/-- `Seq As` typeable means `As` is well-formed. -/
private theorem wf_elem_of_seq_typeof
    (a : Term) (As : SmtType)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq As) :
    __smtx_type_wf As = true := by
  have hNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type; rw [hSmtA]; simp
  have hWf : __smtx_type_wf (SmtType.Seq As) = true :=
    Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt a) hNN hSmtA
  have hParts : native_inhabited_type As = true ∧
      __smtx_type_wf_rec As = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      SmtEval.native_and] using hWf
  cases As <;>
    simp_all [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      SmtEval.native_and, native_inhabited_type]

/-- SMT typeof of `seq_nth a k` is `As` when `a : Seq As`. -/
private theorem seq_nth_smt_typeof
    (a k : Term) (As : SmtType)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq As)
    (hSmtK : __smtx_typeof (__eo_to_smt k) = SmtType.Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) a) k)) = As := by
  change __smtx_typeof (SmtTerm.seq_nth (__eo_to_smt a) (__eo_to_smt k)) = As
  rw [typeof_seq_nth_eq, hSmtA, hSmtK]
  simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf,
    wf_elem_of_seq_typeof a As hSmtA, native_ite]

/-- Reduce the deq subterm to its substr/seq_nth normal form. -/
private theorem stringExtDeq_eq (a b A : Term)
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    stringExtDeq a b A =
      if A = Term.UOp UserOp.Char then
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) a)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
              (Term.Numeral 1)))
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) b)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
              (Term.Numeral 1))))
      else
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) a)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) b)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))) := by
  unfold stringExtDeq __str_mk_ext_deq
  cases a with
  | Stuck => exact absurd rfl ha
  | _ =>
    cases b with
    | Stuck => exact absurd rfl hb
    | _ =>
      cases A with
      | UOp op =>
        cases op with
        | Char => simp
        | _ => simp [Term.UOp.injEq]
      | _ => simp
      all_goals simp

/-- The deq conjunct is Boolean-typed. -/
private theorem stringExtDeq_bool
    (a b A : Term)
    (hSmtA : __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type A))
    (hSmtB : __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type A))
    (hAsNonNone : __eo_to_smt_type A ≠ SmtType.None)
    (hKInt :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
        SmtType.Int) :
    RuleProofs.eo_has_bool_type (stringExtDeq a b A) := by
  have ha : a ≠ Term.Stuck := ne_stuck_of_smt_typeof_seq a _ hSmtA
  have hb : b ≠ Term.Stuck := ne_stuck_of_smt_typeof_seq b _ hSmtB
  rw [stringExtDeq_eq a b A ha hb]
  by_cases hChar : A = Term.UOp UserOp.Char
  · subst hChar
    simp only
    apply RuleProofs.eo_has_bool_type_not_of_bool_arg
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [str_substr_smt_typeof a _ _ hSmtA hKInt,
        str_substr_smt_typeof b _ _ hSmtB hKInt]
    · rw [str_substr_smt_typeof a _ _ hSmtA hKInt]; simp
  · rw [if_neg hChar]
    apply RuleProofs.eo_has_bool_type_not_of_bool_arg
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [seq_nth_smt_typeof a _ _ hSmtA hKInt, seq_nth_smt_typeof b _ _ hSmtB hKInt]
    · rw [seq_nth_smt_typeof a _ _ hSmtA hKInt]; exact hAsNonNone

private theorem typed___eo_prog_string_ext_impl
    (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))
    (hResultTy :
      __eo_typeof
          (__eo_prog_string_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_string_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) := by
  rcases string_ext_smt_types a b hPremBool hResultTy with
    ⟨A, hATy, hBTy, hSmtA, hSmtB, hAsNonNone, hATrans, hBTrans⟩
  -- common facts
  have hLenA : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) a)) =
      SmtType.Int := str_len_smt_typeof_int a A hSmtA
  have hLenB : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) b)) =
      SmtType.Int := str_len_smt_typeof_int b A hSmtB
  have hKInt :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
        SmtType.Int := deq_diff_smt_typeof_int a b A hSmtA hSmtB
  -- deq term is non-stuck
  have hDeqBool : RuleProofs.eo_has_bool_type (stringExtDeq a b A) :=
    stringExtDeq_bool a b A hSmtA hSmtB hAsNonNone hKInt
  have hDeqNeStuck : stringExtDeq a b A ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation _
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _ hDeqBool)
  -- rewrite the conclusion to explicit form
  rw [prog_string_ext_explicit a b A hATy hDeqNeStuck]
  -- bool types of the pieces
  have hD1Bool : RuleProofs.eo_has_bool_type (stringExtD1 a b) := by
    apply RuleProofs.eo_has_bool_type_not_of_bool_arg
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLenA, hLenB]
    · rw [hLenA]; simp
  have hLeqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) (Term.Numeral 0))
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) :=
    eo_has_bool_type_leq_of_int_args _ _ (numeral_smt_typeof_int 0) hKInt
  have hLtBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.lt)
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
          (Term.Apply (Term.UOp UserOp.str_len) a)) :=
    eo_has_bool_type_lt_of_int_args _ _ hKInt hLenA
  have hBoundsBool : RuleProofs.eo_has_bool_type (stringExtBounds a b) := by
    unfold stringExtBounds
    apply RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLeqBool
    apply RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLtBool
    exact RuleProofs.eo_has_bool_type_true
  -- assemble
  apply RuleProofs.eo_has_bool_type_or_of_bool_args _ _ hD1Bool
  apply RuleProofs.eo_has_bool_type_or_of_bool_args
  · exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hDeqBool hBoundsBool
  · exact RuleProofs.eo_has_bool_type_false

/-! ### Value-level semantics of `seq_diff` (the deq-diff index).

`@strings_deq_diff a b` translates (Spec.lean) to `SmtTerm.seq_diff (smt a) (smt b)`,
whose evaluation `native_eval_seq_diff` selects, via `Classical.choose`, some index
at which the two evaluated sequence VALUES disagree (counting a missing element past the
end of the shorter sequence as a disagreement), or `-1` when they are equal.  No model
push / fresh variable is involved, so the rule's soundness needs no premise-closedness
hypothesis.  The lemmas below characterise that index. -/

/-- `native_not (native_veq a b) = true` iff the two values differ. -/
private theorem native_not_veq_true_iff (a b : SmtValue) :
    SmtEval.native_not (native_veq a b) = true ↔ a ≠ b := by
  simp [SmtEval.native_not, native_veq, decide_eq_false_iff_not]

/-- Two equal-length unequal lists differ in their `getD` at some index. -/
private theorem getD_diff_of_ne (d : SmtValue) :
    ∀ xs ys : List SmtValue, xs.length = ys.length → xs ≠ ys →
      ∃ i, xs.getD i d ≠ ys.getD i d
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hne => by
      by_cases hxy : x = y
      · subst hxy
        have htl : xs ≠ ys := fun h => hne (by rw [h])
        obtain ⟨i, hi⟩ := getD_diff_of_ne d xs ys (by simpa using hlen) htl
        exact ⟨i + 1, by simpa using hi⟩
      · exact ⟨0, by simpa using hxy⟩

/-- `getD` past the end of a list is the default. -/
private theorem getD_ge (d : SmtValue) (l : List SmtValue) (i : Nat)
    (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- For an in-bounds index, the length-1 slice is the singleton of that element. -/
private theorem take1_drop_eq (d : SmtValue) (l : List SmtValue) (j : Nat)
    (h : j < l.length) : (l.drop j).take 1 = [l.getD j d] := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons, List.take_zero,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/- Generic characterisation of the `seq_diff` choice, abstracting the (inaccessible,
macro-generated) recursive indexing function as `g`.  Given a differing `getD` index, the
result is `Numeral (Int.ofNat j)` for some index `j` at which the two sequences differ. -/
open Classical in
private theorem dite_seqdiff_spec (g : SmtSeq → Nat → SmtValue)
    (s1 s2 : SmtSeq)
    (hg : ∀ s i, g s i = (native_unpack_seq s).getD i SmtValue.NotValue)
    (hex : ∃ i, (native_unpack_seq s1).getD i SmtValue.NotValue
        ≠ (native_unpack_seq s2).getD i SmtValue.NotValue) :
    ∃ j : Nat,
      (if h : ∃ i, SmtEval.native_not (native_veq (g s1 i) (g s2 i)) = true
         then SmtValue.Numeral (Int.ofNat (Classical.choose h))
         else SmtValue.Numeral (-1))
        = SmtValue.Numeral (Int.ofNat j)
      ∧ (native_unpack_seq s1).getD j SmtValue.NotValue
          ≠ (native_unpack_seq s2).getD j SmtValue.NotValue := by
  have hex' : ∃ i, SmtEval.native_not (native_veq (g s1 i) (g s2 i)) = true := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by rw [native_not_veq_true_iff, hg, hg]; exact hi⟩
  rw [dif_pos hex']
  refine ⟨Classical.choose hex', rfl, ?_⟩
  have hspec := Classical.choose_spec hex'
  rw [native_not_veq_true_iff, hg, hg] at hspec
  exact hspec

/-- Evaluating `seq_diff` on two differing sequence values yields a `Numeral` index at
which the underlying lists differ.  The inaccessible recursive indexer is captured by
unification and shown equal to list `getD` by induction in place. -/
private theorem seq_diff_pick (s1 s2 : SmtSeq)
    (hex : ∃ i, (native_unpack_seq s1).getD i SmtValue.NotValue
        ≠ (native_unpack_seq s2).getD i SmtValue.NotValue) :
    ∃ j : Nat,
      __smtx_model_eval_seq_diff (SmtValue.Seq s1) (SmtValue.Seq s2)
        = SmtValue.Numeral (Int.ofNat j)
      ∧ (native_unpack_seq s1).getD j SmtValue.NotValue
          ≠ (native_unpack_seq s2).getD j SmtValue.NotValue := by
  simp only [__smtx_model_eval_seq_diff]
  refine dite_seqdiff_spec _ s1 s2 ?_ hex
  intro s i
  induction i generalizing s with
  | zero => cases s <;> rfl
  | succ n ih => cases s with
    | empty T => rfl
    | cons v vs => exact ih vs

/-- `seq.nth` on a value reduces to list `getD` at the (nonneg) index. -/
private theorem ssm_seq_nth_ofNat (d : SmtValue) :
    ∀ (s : SmtSeq) (j : Nat),
      __smtx_seq_value_nth s (Int.ofNat j) d = (native_unpack_seq s).getD j d
  | SmtSeq.empty T, j => by simp [__smtx_seq_value_nth, native_unpack_seq]
  | SmtSeq.cons v vs, 0 => by simp [__smtx_seq_value_nth, native_unpack_seq]
  | SmtSeq.cons v vs, (j + 1) => by
      have hidx : native_zplus (Int.ofNat (j + 1)) (native_zneg 1) = Int.ofNat j := by
        show Int.ofNat j + 1 + (-1) = Int.ofNat j
        omega
      have ih := ssm_seq_nth_ofNat d vs j
      simp only [__smtx_seq_value_nth, hidx, ih, native_unpack_seq, List.getD_cons_succ]

/-- In bounds, `getD` does not depend on the default. -/
private theorem getD_lt_eq (d d' : SmtValue) (l : List SmtValue) (j : Nat)
    (h : j < l.length) : l.getD j d = l.getD j d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h, Option.getD_some, Option.getD_some]

/-! ### Eval-layer rewrites for SMT operators not covered by `RuleSupport.Support`.

`__smtx_model_eval` does not reduce definitionally (it is a huge `noncomputable` match),
so we peel one constructor at a time with these stable equation lemmas, mirroring the
public `smtx_eval_*_term_eq` lemmas. -/
private theorem eval_leq_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only
private theorem eval_lt_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.lt x y) =
      __smtx_model_eval_lt (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only
private theorem eval_str_substr_eq (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only
private theorem eval_seq_nth_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_nth x y) =
      __smtx_seq_nth M (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only
private theorem eval_seq_diff_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_diff x y) =
      __smtx_model_eval_seq_diff (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only
private theorem eval_numeral_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-! ### Translation (`__eo_to_smt`) normal forms for the conclusion's atoms (all `rfl`). -/
private theorem tr_D1 (a b : Term) :
    __eo_to_smt (stringExtD1 a b) =
      SmtTerm.not (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt a))
        (SmtTerm.str_len (__eo_to_smt b))) := rfl
private theorem tr_deq_char (a b : Term) :
    __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) a)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
              (Term.Numeral 1)))
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) b)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
              (Term.Numeral 1)))) =
      SmtTerm.not (SmtTerm.eq
        (SmtTerm.str_substr (__eo_to_smt a)
          (SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b)) (SmtTerm.Numeral 1))
        (SmtTerm.str_substr (__eo_to_smt b)
          (SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b)) (SmtTerm.Numeral 1))) := rfl
private theorem tr_deq_nth (a b : Term) :
    __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) a)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) b)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)))) =
      SmtTerm.not (SmtTerm.eq
        (SmtTerm.seq_nth (__eo_to_smt a)
          (SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b)))
        (SmtTerm.seq_nth (__eo_to_smt b)
          (SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b)))) := rfl
private theorem tr_leq0k (a b : Term) :
    __eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) (Term.Numeral 0))
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
      SmtTerm.leq (SmtTerm.Numeral 0)
        (SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b)) := rfl
private theorem tr_ltklen (a b : Term) :
    __eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.lt)
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b))
          (Term.Apply (Term.UOp UserOp.str_len) a)) =
      SmtTerm.lt (SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b))
        (SmtTerm.str_len (__eo_to_smt a)) := rfl

/-! ### Disequality of element values (for the general `seq.nth` deq branch).

`__smtx_model_eval_eq` uses regex extensional equality on `RegLan` pairs, so it only
agrees with structural `native_veq` when the operands are not both `RegLan`.  Sequence
elements have the sequence's element type `As`, and `Seq RegLan` is not well-formed, so
`As ≠ RegLan` and the elements are never `RegLan` values. -/
private theorem eval_neq (v1 v2 : SmtValue)
    (hReg : ¬ ∃ r1 r2, v1 = SmtValue.RegLan r1 ∧ v2 = SmtValue.RegLan r2)
    (h : v1 ≠ v2) :
    __smtx_model_eval_not (__smtx_model_eval_eq v1 v2) = SmtValue.Boolean true := by
  have heq : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean (native_veq v1 v2) := by
    cases v1 <;> cases v2 <;> first | exact absurd ⟨_, _, rfl, rfl⟩ hReg | rfl
  rw [heq]
  simp [__smtx_model_eval_not, native_veq, SmtEval.native_not, h]

private theorem list_typed_getD (T : SmtType) :
    ∀ (xs : List SmtValue) (j : Nat), list_typed T xs → j < xs.length →
      __smtx_typeof_value (xs.getD j SmtValue.NotValue) = T
  | v :: vs, 0, h, _ => h.1
  | v :: vs, j + 1, h, hlt => by
      simp only [List.getD_cons_succ]
      exact list_typed_getD T vs j h.2 (by simpa using hlt)
  | [], j, _, hlt => by simp at hlt

private theorem getD_ne_reglan (xs : List SmtValue) (As : SmtType)
    (hAs : As ≠ SmtType.RegLan) (hxs : list_typed As xs) (j : Nat) (r : SmtRegLan) :
    xs.getD j SmtValue.NotValue ≠ SmtValue.RegLan r := by
  intro h
  by_cases hj : j < xs.length
  · have hty := list_typed_getD As xs j hxs hj
    rw [h] at hty
    exact hAs hty.symm
  · rw [getD_ge SmtValue.NotValue xs j (Nat.le_of_not_lt hj)] at h
    exact SmtValue.noConfusion h

private theorem facts___eo_prog_string_ext_impl
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))
    (hResultTy :
      __eo_typeof
          (__eo_prog_string_ext
            (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) =
        Term.Bool)
    (hPremTrue :
      eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)) true) :
    eo_interprets M
      (__eo_prog_string_ext
        (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b)))) true := by
  rcases string_ext_smt_types a b hPremBool hResultTy with
    ⟨A, hATy, hBTy, hSmtA, hSmtB, hAsNonNone, hATrans, hBTrans⟩
  -- canonical evaluations of `a` and `b`
  have hAvalTy : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
      SmtType.Seq (__eo_to_smt_type A) :=
    smt_model_eval_preserves_type M hM (__eo_to_smt a) (SmtType.Seq (__eo_to_smt_type A))
      hSmtA (seq_ne_none _) (type_inhabited_seq _)
  have hBvalTy : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) =
      SmtType.Seq (__eo_to_smt_type A) :=
    smt_model_eval_preserves_type M hM (__eo_to_smt b) (SmtType.Seq (__eo_to_smt_type A))
      hSmtB (seq_ne_none _) (type_inhabited_seq _)
  rcases seq_value_canonical hAvalTy with ⟨s1, hAEval⟩
  rcases seq_value_canonical hBvalTy with ⟨s2, hBEval⟩
  have hs1ty : __smtx_typeof_seq_value s1 = SmtType.Seq (__eo_to_smt_type A) := by
    simpa [hAEval, __smtx_typeof_value] using hAvalTy
  have hs2ty : __smtx_typeof_seq_value s2 = SmtType.Seq (__eo_to_smt_type A) := by
    simpa [hBEval, __smtx_typeof_value] using hBvalTy
  have hElem1 : __smtx_elem_typeof_seq_value s1 = __eo_to_smt_type A :=
    elem_typeof_seq_value_of_typeof_seq_value hs1ty
  have hElem2 : __smtx_elem_typeof_seq_value s2 = __eo_to_smt_type A :=
    elem_typeof_seq_value_of_typeof_seq_value hs2ty
  have hxs1 : list_typed (__eo_to_smt_type A) (native_unpack_seq s1) :=
    typed_unpack_seq_of_typeof_seq_value hs1ty
  have hxs2 : list_typed (__eo_to_smt_type A) (native_unpack_seq s2) :=
    typed_unpack_seq_of_typeof_seq_value hs2ty
  -- the element type is not `RegLan` (since `Seq RegLan` is not well-formed)
  have hAsNe : __eo_to_smt_type A ≠ SmtType.RegLan := by
    have hNN : term_has_non_none_type (__eo_to_smt a) := by
      unfold term_has_non_none_type; rw [hSmtA]; simp
    have hSeqWf : __smtx_type_wf (SmtType.Seq (__eo_to_smt_type A)) = true :=
      Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt a) hNN hSmtA
    intro hR; rw [hR] at hSeqWf; exact absurd hSeqWf (by native_decide)
  -- typing facts of the conclusion's components (mirroring the typing lemma)
  have hKInt :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) a) b)) =
        SmtType.Int := deq_diff_smt_typeof_int a b A hSmtA hSmtB
  have hDeqBool : RuleProofs.eo_has_bool_type (stringExtDeq a b A) :=
    stringExtDeq_bool a b A hSmtA hSmtB hAsNonNone hKInt
  have hDeqNeStuck : stringExtDeq a b A ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation _
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _ hDeqBool)
  have hLenA : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) a)) =
      SmtType.Int := str_len_smt_typeof_int a A hSmtA
  have hD1Bool : RuleProofs.eo_has_bool_type (stringExtD1 a b) := by
    apply RuleProofs.eo_has_bool_type_not_of_bool_arg
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLenA, str_len_smt_typeof_int b A hSmtB]
    · rw [hLenA]; simp
  have hBoundsBool : RuleProofs.eo_has_bool_type (stringExtBounds a b) := by
    unfold stringExtBounds
    apply RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      (eo_has_bool_type_leq_of_int_args _ _ (numeral_smt_typeof_int 0) hKInt)
    apply RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      (eo_has_bool_type_lt_of_int_args _ _ hKInt hLenA)
    exact RuleProofs.eo_has_bool_type_true
  have hRHSBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.or)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) (stringExtDeq a b A))
              (stringExtBounds a b)))
          (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args _ _
      (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hDeqBool hBoundsBool)
      RuleProofs.eo_has_bool_type_false
  -- the premise `(not (= a b))` forces the two sequence values to differ
  have hABne : SmtValue.Seq s1 ≠ SmtValue.Seq s2 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremTrue
    cases hPremTrue with
    | intro_true _ hEval =>
        rw [show __eo_to_smt (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b))
              = SmtTerm.not (SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b)) from rfl,
            smtx_eval_not_term_eq, smtx_eval_eq_term_eq, hAEval, hBEval] at hEval
        intro hEq
        rw [hEq] at hEval
        simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq,
          SmtEval.native_not] at hEval
  -- rewrite the conclusion to its explicit disjunction form
  rw [prog_string_ext_explicit a b A hATy hDeqNeStuck]
  by_cases hLen : (native_unpack_seq s1).length = (native_unpack_seq s2).length
  · -- equal lengths: establish the second disjunct
    have hxsne : native_unpack_seq s1 ≠ native_unpack_seq s2 := by
      intro hEq
      apply hABne
      rw [← native_pack_unpack_seq s1, ← native_pack_unpack_seq s2, hElem1, hElem2, hEq]
    obtain ⟨i0, hi0⟩ := getD_diff_of_ne SmtValue.NotValue _ _ hLen hxsne
    obtain ⟨j, hKval0, hjDiff⟩ := seq_diff_pick s1 s2 ⟨i0, hi0⟩
    have hjLt : j < (native_unpack_seq s1).length := by
      rcases Nat.lt_or_ge j (native_unpack_seq s1).length with h | h
      · exact h
      · exact absurd
          (by rw [getD_ge SmtValue.NotValue _ _ h, getD_ge SmtValue.NotValue _ _ (hLen ▸ h)])
          hjDiff
    have hjLt2 : j < (native_unpack_seq s2).length := hLen ▸ hjLt
    -- evaluation of the deq-diff index `seq_diff a b`
    have hSeqDiffEval :
        __smtx_model_eval M (SmtTerm.seq_diff (__eo_to_smt a) (__eo_to_smt b))
          = SmtValue.Numeral (Int.ofNat j) := by
      rw [eval_seq_diff_eq, hAEval, hBEval, hKval0]
    apply RuleProofs.eo_interprets_or_right_intro M hM _ _ hD1Bool
    apply RuleProofs.eo_interprets_or_left_intro M hM _ _ _
      RuleProofs.eo_has_bool_type_false
    apply RuleProofs.eo_interprets_and_intro
    · -- the deq conjunct: the elements at index `j` differ
      apply RuleProofs.eo_interprets_of_bool_eval M _ true hDeqBool
      rw [stringExtDeq_eq a b A
        (ne_stuck_of_smt_typeof_seq a _ hSmtA) (ne_stuck_of_smt_typeof_seq b _ hSmtB)]
      by_cases hChar : A = Term.UOp UserOp.Char
      · rw [if_pos hChar, tr_deq_char, smtx_eval_not_term_eq, smtx_eval_eq_term_eq,
          eval_str_substr_eq, eval_str_substr_eq, hAEval, hBEval, hSeqDiffEval]
        simp only [eval_numeral_eq, __smtx_model_eval_str_substr, hElem1, hElem2,
          native_seq_extract_one_nat _ _ hjLt, native_seq_extract_one_nat _ _ hjLt2,
          take1_drop_eq SmtValue.NotValue _ _ hjLt,
          take1_drop_eq SmtValue.NotValue _ _ hjLt2,
          __smtx_model_eval_eq, __smtx_model_eval_not]
        rw [SmtValue.Boolean.injEq, native_not_veq_true_iff]
        intro h
        rw [SmtValue.Seq.injEq] at h
        exact hjDiff (by simpa using native_pack_seq_inj _ h)
      · rw [if_neg hChar, tr_deq_nth, smtx_eval_not_term_eq, smtx_eval_eq_term_eq,
          eval_seq_nth_eq, eval_seq_nth_eq, hAEval, hBEval, hSeqDiffEval]
        have hnth1 : __smtx_seq_nth M (SmtValue.Seq s1) (SmtValue.Numeral (Int.ofNat j))
            = (native_unpack_seq s1).getD j SmtValue.NotValue := by
          simp only [__smtx_seq_nth, ssm_seq_nth_ofNat]
          exact getD_lt_eq _ _ _ _ hjLt
        have hnth2 : __smtx_seq_nth M (SmtValue.Seq s2) (SmtValue.Numeral (Int.ofNat j))
            = (native_unpack_seq s2).getD j SmtValue.NotValue := by
          simp only [__smtx_seq_nth, ssm_seq_nth_ofNat]
          exact getD_lt_eq _ _ _ _ hjLt2
        rw [hnth1, hnth2]
        exact eval_neq _ _
          (fun ⟨r1, r2, hr1, _⟩ => getD_ne_reglan _ _ hAsNe hxs1 j r1 hr1) hjDiff
    · -- the bounds conjunct: `0 ≤ j < len a`
      unfold stringExtBounds
      apply RuleProofs.eo_interprets_and_intro
      · apply RuleProofs.eo_interprets_of_bool_eval M _ true
          (eo_has_bool_type_leq_of_int_args _ _ (numeral_smt_typeof_int 0) hKInt)
        rw [tr_leq0k, eval_leq_eq, eval_numeral_eq, hSeqDiffEval]
        have h0 : native_zleq 0 (Int.ofNat j) = true := by
          rw [native_zleq]; exact decide_eq_true_eq.mpr (Int.natCast_nonneg j)
        simp only [__smtx_model_eval_leq, h0]
      · apply RuleProofs.eo_interprets_and_intro
        · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            (eo_has_bool_type_lt_of_int_args _ _ hKInt hLenA)
          rw [tr_ltklen, eval_lt_eq, hSeqDiffEval, smtx_eval_str_len_term_eq, hAEval]
          have hpf : (Int.ofNat j) < native_seq_len (native_unpack_seq s1) := by
            rw [native_seq_len, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]; omega
          have h1 : native_zlt (Int.ofNat j) (native_seq_len (native_unpack_seq s1)) = true := by
            rw [native_zlt]; exact decide_eq_true_eq.mpr hpf
          simp only [__smtx_model_eval_str_len, __smtx_model_eval_lt, h1]
        · exact RuleProofs.eo_interprets_true M
  · -- unequal lengths: establish the first disjunct
    apply RuleProofs.eo_interprets_or_left_intro M hM _ _ _ hRHSBool
    apply RuleProofs.eo_interprets_of_bool_eval M _ true hD1Bool
    rw [tr_D1, smtx_eval_not_term_eq, smtx_eval_eq_term_eq,
      smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq, hAEval, hBEval]
    simp only [__smtx_model_eval_str_len, __smtx_model_eval_eq, __smtx_model_eval_not]
    rw [SmtValue.Boolean.injEq, native_not_veq_true_iff]
    intro h
    apply hLen
    injection h with h'
    have h2 : (↑(native_unpack_seq s1).length : Int) = (↑(native_unpack_seq s2).length : Int) := by
      simpa [native_seq_len] using h'
    exact_mod_cast h2


/-
`string_ext` is sound and fully proven.  The premise is `(not (= a b))` and the
conclusion is

    (or (not (= (str_len a) (str_len b)))
        (or (and (deq-at-k a b) (and (0 <= k) (and (k < str_len a) true))) false))

where `k = @strings_deq_diff a b` translates (Spec.lean) to `seq_diff (smt a) (smt b)`,
whose evaluation directly selects (via `Classical.choose`) some index at which the two
already-evaluated sequence VALUES disagree, or `-1` when equal.  No model push / fresh
variable is involved, so no premise-closedness hypothesis is needed.

Proof (`facts___eo_prog_string_ext_impl`): the premise makes the evaluated values
`a, b` differ.  If their lengths differ, the first disjunct `(not (= (str_len a)
(str_len b)))` holds.  Otherwise the underlying lists differ at some index
(`getD_diff_of_ne`), so `seq_diff` (`seq_diff_pick`) returns an index `j` at which the
elements differ; `j` is in bounds (`getD_ge`), giving the deq conjunct (chars/elements
at `j` differ) and the bounds `0 ≤ j < len a`.
-/
public theorem cmd_step_string_ext_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_ext args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_ext args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_ext args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.string_ext args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n premises =>
          cases premises with
          | nil =>
              have hPremBoolState :
                  RuleProofs.eo_has_bool_type (__eo_state_proven_nth s n) :=
                hPremisesBool (__eo_state_proven_nth s n) (by simp [premiseTermList])
              cases hp : __eo_state_proven_nth s n with
              | Apply f pArg =>
                  cases f with
                  | UOp op =>
                      cases op with
                      | not =>
                          cases pArg with
                          | Apply fEq b =>
                              cases fEq with
                              | Apply gEq a =>
                                  cases gEq with
                                  | UOp opEq =>
                                      by_cases hOpEq : opEq = UserOp.eq
                                      · subst opEq
                                        have hPremBool :
                                            RuleProofs.eo_has_bool_type
                                              (Term.Apply Term.not
                                                (Term.Apply (Term.Apply Term.eq a) b)) := by
                                          simpa [hp] using hPremBoolState
                                        have hResultTyAB :
                                            __eo_typeof
                                                (__eo_prog_string_ext
                                                  (Proof.pf
                                                    (Term.Apply Term.not
                                                      (Term.Apply (Term.Apply Term.eq a) b)))) =
                                              Term.Bool := by
                                          simpa [cmd_step_string_ext_one_eq, hp] using hResultTy
                                        refine ⟨?_, ?_⟩
                                        · intro hPremTrue
                                          have hStatePremTrue :
                                              eo_interprets M (__eo_state_proven_nth s n) true :=
                                            hPremTrue (__eo_state_proven_nth s n)
                                              (by simp [premiseTermList])
                                          have hThisPremTrue :
                                              eo_interprets M
                                                (Term.Apply Term.not
                                                  (Term.Apply (Term.Apply Term.eq a) b)) true :=
                                            by simpa [hp] using hStatePremTrue
                                          simpa [cmd_step_string_ext_one_eq, hp] using
                                            facts___eo_prog_string_ext_impl M hM a b
                                              hPremBool hResultTyAB hThisPremTrue
                                        · simpa [cmd_step_string_ext_one_eq, hp] using
                                            RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                              (typed___eo_prog_string_ext_impl a b
                                                hPremBool hResultTyAB)
                                      · have hBad :
                                            __eo_cmd_step_proven s CRule.string_ext
                                                CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                              Term.Stuck := by
                                          rw [cmd_step_string_ext_one_eq, hp]
                                          simp [__eo_prog_string_ext, hOpEq]
                                        exact False.elim (hProg hBad)
                                  | _ =>
                                      have hBad :
                                          __eo_cmd_step_proven s CRule.string_ext
                                              CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                            Term.Stuck := by
                                        rw [cmd_step_string_ext_one_eq, hp]
                                        simp [__eo_prog_string_ext]
                                      exact False.elim (hProg hBad)
                              | _ =>
                                  have hBad :
                                      __eo_cmd_step_proven s CRule.string_ext
                                          CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                        Term.Stuck := by
                                    rw [cmd_step_string_ext_one_eq, hp]
                                    simp [__eo_prog_string_ext]
                                  exact False.elim (hProg hBad)
                          | _ =>
                              have hBad :
                                  __eo_cmd_step_proven s CRule.string_ext
                                      CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                    Term.Stuck := by
                                rw [cmd_step_string_ext_one_eq, hp]
                                simp [__eo_prog_string_ext]
                              exact False.elim (hProg hBad)
                      | _ =>
                          have hBad :
                              __eo_cmd_step_proven s CRule.string_ext
                                  CArgList.nil (CIndexList.cons n CIndexList.nil) =
                                Term.Stuck := by
                            rw [cmd_step_string_ext_one_eq, hp]
                            simp [__eo_prog_string_ext]
                          exact False.elim (hProg hBad)
                  | _ =>
                      have hBad :
                          __eo_cmd_step_proven s CRule.string_ext
                              CArgList.nil (CIndexList.cons n CIndexList.nil) =
                            Term.Stuck := by
                        rw [cmd_step_string_ext_one_eq, hp]
                        simp [__eo_prog_string_ext]
                      exact False.elim (hProg hBad)
              | _ =>
                  have hBad :
                      __eo_cmd_step_proven s CRule.string_ext
                          CArgList.nil (CIndexList.cons n CIndexList.nil) =
                        Term.Stuck := by
                    rw [cmd_step_string_ext_one_eq, hp]
                    simp [__eo_prog_string_ext]
                  exact False.elim (hProg hBad)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
