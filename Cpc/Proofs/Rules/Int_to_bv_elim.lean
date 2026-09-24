module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def intToBvZeroList : native_Nat -> Term
  | 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int)
  | Nat.succ k =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (intToBvZeroList k)

private abbrev intToBvAbconv (n : Term) (k : native_Nat) : Term :=
  __abconv_int_to_bv_elim n (intToBvZeroList k)
    (Term.Numeral (native_int_pow2 (native_nat_to_int k)))

private abbrev intToBvBit (n : Term) (p half : native_Int) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.ite)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.geq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.mod_total) n)
              (Term.Numeral p)))
          (Term.Numeral half)))
      (Term.Binary 1 1))
    (Term.Binary 1 0)

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

private theorem eo_requires_left_ne_stuck_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro hReq hx
  have hStuck : __eo_requires x y z = Term.Stuck := by
    subst x
    simp [__eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not]
  exact hReq hStuck

private theorem eo_mk_apply_of_ne_stuck
    {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem term_apply_ne_stuck (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

private theorem typedConsZeroHead_ne_stuck :
    Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
      (Term.Numeral 0) ≠ Term.Stuck := by
  intro h
  cases h

private theorem native_int_pow2_nat (k : native_Nat) :
    native_int_pow2 (native_nat_to_int k) = (2 ^ k : Int) := by
  have hnot : ¬ ((k : Int) < 0) :=
    Int.not_lt_of_ge (Int.natCast_nonneg k)
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, hnot]

private theorem native_int_pow2_nat_pos (k : native_Nat) :
    0 < native_int_pow2 (native_nat_to_int k) := by
  rw [native_int_pow2_nat]
  exact_mod_cast (Nat.pow_pos (a := 2) (n := k) (by decide : 0 < 2))

private theorem native_int_pow2_nat_succ (k : native_Nat) :
    native_int_pow2 (native_nat_to_int (k + 1)) =
      2 * native_int_pow2 (native_nat_to_int k) := by
  rw [native_int_pow2_nat, native_int_pow2_nat]
  change ((2 ^ (k + 1) : Nat) : Int) =
    (2 : Int) * ((2 ^ k : Nat) : Int)
  rw [Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
  simp

private theorem native_int_pow2_nat_succ_div_two (k : native_Nat) :
    native_div_total (native_int_pow2 (native_nat_to_int (k + 1))) 2 =
      native_int_pow2 (native_nat_to_int k) := by
  rw [native_int_pow2_nat_succ]
  exact Int.mul_ediv_cancel_left (native_int_pow2 (native_nat_to_int k))
    (by decide : (2 : Int) ≠ 0)

private theorem int_mod_pow2_succ_decomp
    (z : native_Int) (k : native_Nat) :
    native_zplus
        (native_zmult
          (native_ite
            (native_zleq
              (native_int_pow2 (native_nat_to_int k))
              (native_mod_total z
                (native_int_pow2 (native_nat_to_int (k + 1)))))
            1 0)
          (native_int_pow2 (native_nat_to_int k)))
        (native_mod_total z (native_int_pow2 (native_nat_to_int k))) =
      native_mod_total z
        (native_int_pow2 (native_nat_to_int (k + 1))) := by
  let half : Int := native_int_pow2 (native_nat_to_int k)
  have hHalfPos : 0 < half := by
    simpa [half] using native_int_pow2_nat_pos k
  have hFull :
      native_int_pow2 (native_nat_to_int (k + 1)) = 2 * half := by
    simpa [half] using native_int_pow2_nat_succ k
  let r : Int := z % (2 * half)
  have hFullPos : 0 < 2 * half := by omega
  have hr0 : 0 <= r := by
    simpa [r, native_mod_total] using
      Int.emod_nonneg z (Int.ne_of_gt hFullPos)
  have hrlt : r < 2 * half := by
    simpa [r, native_mod_total] using Int.emod_lt_of_pos z hFullPos
  have hzHalf : z % half = r % half := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hSub : z - r = (2 * half) * (z / (2 * half)) := by
      have h := Int.mul_ediv_add_emod z (2 * half)
      change (2 * half) * (z / (2 * half)) + r = z at h
      calc
        z - r = ((2 * half) * (z / (2 * half)) + r) - r := by
          exact (congrArg (fun x => x - r) h).symm
        _ = (2 * half) * (z / (2 * half)) := by simp
    rw [hSub]
    apply Int.emod_eq_zero_of_dvd
    refine ⟨2 * (z / (2 * half)), ?_⟩
    simp [Int.mul_assoc, Int.mul_left_comm]
  rw [hFull]
  change
    native_zplus
        (native_zmult (native_ite (native_zleq half r) 1 0) half)
        (native_mod_total z half) =
      r
  by_cases hle : half <= r
  · have hCond : native_zleq half r = true := by
      simpa [native_zleq] using hle
    have hDiff0 : 0 <= r - half := by omega
    have hDiffLt : r - half < half := by omega
    have hrMod : r % half = r - half := by
      have hrEq : r = half + (r - half) := by omega
      have hrEq' : half + (r - half) = r := hrEq.symm
      calc
        r % half = (half + (r - half)) % half := by
          exact (congrArg (fun x => x % half) hrEq').symm
        _ = (half % half + (r - half) % half) % half := by
          rw [Int.add_emod]
        _ = (r - half) % half := by simp [Int.emod_self]
        _ = r - half := Int.emod_eq_of_lt hDiff0 hDiffLt
    have hzMod : native_mod_total z half = r - half := by
      simpa [native_mod_total] using hzHalf.trans hrMod
    rw [hCond]
    calc
      native_zplus (native_zmult (native_ite true 1 0) half)
          (native_mod_total z half) =
        half + (r - half) := by
          simp [native_ite, native_zplus, native_zmult, hzMod]
      _ = r := by omega
  · have hCond : native_zleq half r = false := by
      simp [native_zleq, hle]
    have hlt : r < half := by omega
    have hrMod : r % half = r := Int.emod_eq_of_lt hr0 hlt
    rw [hCond]
    simp [native_ite, native_zplus, native_zmult, native_mod_total,
      hzHalf, hrMod]

private theorem intToBvBit_ne_stuck
    (n : Term) (p half : native_Int)
    (hn : n ≠ Term.Stuck) :
    intToBvBit n p half ≠ Term.Stuck := by
  intro h
  cases h

private theorem intToBvBit_mk_eq
    (n : Term) (p half : native_Int) :
    __eo_mk_apply
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.ite)
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.geq)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.mod_total) n)
                  (Term.Numeral p)))
              (Term.Numeral half)))
          (Term.Binary 1 1))
        (Term.Binary 1 0) =
      intToBvBit n p half := by
  rw [eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
    (by intro h; cases h)]
  rw [eo_mk_apply_of_ne_stuck (by intro h; cases h)
    (term_apply_ne_stuck _ _)]
  rw [eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
    (by intro h; cases h)]
  rw [eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
    (by intro h; cases h)]

private theorem intToBvZeroList_zero_eq :
    intToBvZeroList 0 =
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int) := by
  rfl

private theorem intToBvZeroList_ne_stuck :
    ∀ k : native_Nat, intToBvZeroList k ≠ Term.Stuck := by
  intro k
  induction k with
  | zero =>
      rw [intToBvZeroList_zero_eq]
      intro h
      cases h
  | succ k ih =>
      intro h
      cases h

private theorem intToBvZeroList_succ_eq (k : native_Nat) :
    intToBvZeroList (k + 1) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (intToBvZeroList k) := by
  rfl

private theorem intToBvZeroList_repeat_rec_eq :
    ∀ k : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) k =
        intToBvZeroList k := by
  intro k
  induction k with
  | zero =>
      change
        __eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_typeof (Term.Numeral 0)) =
          intToBvZeroList 0
      rw [intToBvZeroList_zero_eq]
      rw [show __eo_typeof (Term.Numeral 0) = Term.UOp UserOp.Int by rfl]
      rfl
  | succ k ih =>
      change
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0))
            (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) k) =
          intToBvZeroList (k + 1)
      rw [ih]
      rw [eo_mk_apply_of_ne_stuck typedConsZeroHead_ne_stuck
        (intToBvZeroList_ne_stuck k)]
      rfl

private theorem intToBvAbconv_zero_eq (n : Term) (hn : n ≠ Term.Stuck) :
    intToBvAbconv n 0 = Term.Binary 0 0 := by
  cases n <;> simp [intToBvAbconv, intToBvZeroList_zero_eq,
    __abconv_int_to_bv_elim] at hn ⊢

private theorem intToBvAbconv_ne_stuck
    (n : Term) (hn : n ≠ Term.Stuck) :
    ∀ k : native_Nat, intToBvAbconv n k ≠ Term.Stuck := by
  intro k
  induction k with
  | zero =>
      rw [intToBvAbconv_zero_eq n hn]
      intro h
      cases h
  | succ k ih =>
      have hBit :
          intToBvBit n
              (native_int_pow2 (native_nat_to_int (k + 1)))
              (native_int_pow2 (native_nat_to_int k)) ≠ Term.Stuck :=
        intToBvBit_ne_stuck n _ _ hn
      simp [intToBvAbconv, intToBvZeroList_succ_eq,
        __abconv_int_to_bv_elim, __eo_zdiv,
        native_int_pow2_nat_succ_div_two, native_ite, native_zeq]
      rw [intToBvBit_mk_eq]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hBit]
      rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) ih]
      intro h
      cases h

private theorem intToBvAbconv_succ_eq
    (n : Term) (hn : n ≠ Term.Stuck) (k : native_Nat) :
    intToBvAbconv n (k + 1) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.concat)
          (intToBvBit n
            (native_int_pow2 (native_nat_to_int (k + 1)))
            (native_int_pow2 (native_nat_to_int k))))
        (intToBvAbconv n k) := by
  have hTail := intToBvAbconv_ne_stuck n hn k
  have hBit :
      intToBvBit n
          (native_int_pow2 (native_nat_to_int (k + 1)))
          (native_int_pow2 (native_nat_to_int k)) ≠ Term.Stuck :=
    intToBvBit_ne_stuck n _ _ hn
  simp [intToBvAbconv, intToBvZeroList_succ_eq,
    __abconv_int_to_bv_elim, __eo_zdiv,
    native_int_pow2_nat_succ_div_two, native_ite, native_zeq]
  rw [intToBvBit_mk_eq]
  rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hBit]
  rw [eo_mk_apply_of_ne_stuck (by intro h; cases h) hTail]

private theorem intToBvBit_eval
    (M : SmtModel) (n : Term) (z p half : native_Int)
    (hnEval : __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral z) :
    __smtx_model_eval M
        (__eo_to_smt (intToBvBit n p half)) =
      SmtValue.Binary 1
        (native_ite (native_zleq half (native_mod_total z p)) 1 0) := by
  rw [show
    __eo_to_smt (intToBvBit n p half) =
      SmtTerm.ite
        (SmtTerm.geq
          (SmtTerm.mod_total (__eo_to_smt n) (SmtTerm.Numeral p))
          (SmtTerm.Numeral half))
        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0) by rfl]
  rw [smtx_eval_ite_term_eq, __smtx_model_eval.eq_20,
    __smtx_model_eval.eq_32, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_2, __smtx_model_eval.eq_5,
    __smtx_model_eval.eq_5]
  rw [hnEval]
  cases hCond : native_zleq half (native_mod_total z p) <;>
    simp [__smtx_model_eval_mod_total, __smtx_model_eval_geq,
      __smtx_model_eval_leq, __smtx_model_eval_ite, native_ite, hCond]

private theorem intToBvAbconv_eval
    (M : SmtModel) (n : Term) (z : native_Int)
    (hn : n ≠ Term.Stuck)
    (hnEval : __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral z) :
    ∀ k : native_Nat,
      __smtx_model_eval M (__eo_to_smt (intToBvAbconv n k)) =
        SmtValue.Binary (native_nat_to_int k)
          (native_mod_total z (native_int_pow2 (native_nat_to_int k))) := by
  intro k
  induction k with
  | zero =>
      rw [intToBvAbconv_zero_eq n hn]
      rw [show __eo_to_smt (Term.Binary 0 0) = SmtTerm.Binary 0 0 by rfl,
        __smtx_model_eval.eq_5]
      simp [native_nat_to_int, native_int_pow2, native_zexp_total,
        native_mod_total]
  | succ k ih =>
      rw [intToBvAbconv_succ_eq n hn k]
      rw [show
        __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.concat)
              (intToBvBit n
                (native_int_pow2 (native_nat_to_int (k + 1)))
                (native_int_pow2 (native_nat_to_int k))))
            (intToBvAbconv n k)) =
          SmtTerm.concat
            (__eo_to_smt
              (intToBvBit n
                (native_int_pow2 (native_nat_to_int (k + 1)))
                (native_int_pow2 (native_nat_to_int k))))
            (__eo_to_smt (intToBvAbconv n k)) by rfl]
      rw [__smtx_model_eval.eq_36]
      rw [intToBvBit_eval M n z
        (native_int_pow2 (native_nat_to_int (k + 1)))
        (native_int_pow2 (native_nat_to_int k)) hnEval, ih]
      simp [__smtx_model_eval_concat, native_binary_concat]
      have hWidth :
          native_zplus 1 (native_nat_to_int k) =
            native_nat_to_int (k + 1) := by
        simp [native_zplus, native_nat_to_int, Int.add_comm]
      rw [hWidth]
      have hPayload := int_mod_pow2_succ_decomp z k
      rw [hPayload]
      simp [native_mod_total]

private theorem intToBvAbconv_is_concat_list
    (n : Term) (hn : n ≠ Term.Stuck) :
    ∀ k : native_Nat,
      __eo_is_list (Term.UOp UserOp.concat) (intToBvAbconv n k) =
        Term.Boolean true := by
  intro k
  induction k with
  | zero =>
      rw [intToBvAbconv_zero_eq n hn]
      simp [__eo_is_list, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, __eo_is_ok, native_ite, native_teq, native_not,
        SmtEval.native_not]
  | succ k ih =>
      rw [intToBvAbconv_succ_eq n hn k]
      simp [__eo_is_list, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.concat)
              (intToBvAbconv n k)) =
          Term.Boolean true
      have hTailNe := intToBvAbconv_ne_stuck n hn k
      have hIhEq :
          __eo_is_list (Term.UOp UserOp.concat) (intToBvAbconv n k) =
            __eo_is_ok
              (__eo_get_nil_rec (Term.UOp UserOp.concat)
                (intToBvAbconv n k)) := by
        cases hTail : intToBvAbconv n k
        case Stuck =>
          exact False.elim (hTailNe hTail)
        all_goals simp [__eo_is_list]
      rw [hIhEq] at ih
      exact ih

private theorem intToBvAbconv_succ_is_not_concat_nil
    (n : Term) (hn : n ≠ Term.Stuck) (k : native_Nat) :
    __eo_is_list_nil (Term.UOp UserOp.concat)
        (intToBvAbconv n (k + 1)) =
      Term.Boolean false := by
  rw [intToBvAbconv_succ_eq n hn k]
  simp [__eo_is_list_nil]

private theorem intToBvExpanded_eval
    (M : SmtModel) (n : Term) (z : native_Int)
    (hn : n ≠ Term.Stuck)
    (hnEval : __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral z) :
    ∀ k : native_Nat,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.concat)
              (intToBvAbconv n k))) =
        SmtValue.Binary (native_nat_to_int k)
          (native_mod_total z (native_int_pow2 (native_nat_to_int k))) := by
  intro k
  cases k with
  | zero =>
      rw [intToBvAbconv_zero_eq n hn]
      simp [__eo_list_singleton_elim, __eo_list_singleton_elim_2,
        __eo_is_list, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, __eo_is_ok, native_ite, native_teq, native_not,
        SmtEval.native_not,
        native_nat_to_int, native_int_pow2, native_zexp_total,
        native_mod_total]
      rw [show __eo_to_smt (Term.Binary 0 0) = SmtTerm.Binary 0 0 by rfl,
        __smtx_model_eval.eq_5]
  | succ k =>
      cases k with
      | zero =>
          rw [intToBvAbconv_succ_eq n hn 0]
          have hList :
              __eo_is_list (Term.UOp UserOp.concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (intToBvBit n
                      (native_int_pow2 (native_nat_to_int 1))
                      (native_int_pow2 (native_nat_to_int 0))))
                  (intToBvAbconv n 0)) =
                Term.Boolean true := by
            simpa [intToBvAbconv_succ_eq n hn 0] using
              intToBvAbconv_is_concat_list n hn 1
          have hTailNil :
              __eo_is_list_nil (Term.UOp UserOp.concat)
                  (intToBvAbconv n 0) =
                Term.Boolean true := by
            rw [intToBvAbconv_zero_eq n hn]
            simp [__eo_is_list_nil]
          -- `intToBvBit` is an `abbrev`, so v4.33's `simp` unfolds it in the
          -- goal; normalise the eval lemma the same way before rewriting.
          have hBit := intToBvBit_eval M n z
            (native_int_pow2 (native_nat_to_int 1))
            (native_int_pow2 (native_nat_to_int 0)) hnEval
          simp [__eo_list_singleton_elim, hList, __eo_requires,
            __eo_list_singleton_elim_2, hTailNil, __eo_ite, native_ite,
            native_teq, native_not, SmtEval.native_not] at hBit ⊢
          rw [hBit]
          have hPayload := int_mod_pow2_succ_decomp z 0
          simp [native_nat_to_int, native_int_pow2, native_zexp_total,
            native_mod_total, native_zplus, native_zmult] at hPayload ⊢
          exact hPayload
      | succ k =>
          rw [intToBvAbconv_succ_eq n hn (k + 1)]
          have hList :
              __eo_is_list (Term.UOp UserOp.concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (intToBvBit n
                      (native_int_pow2
                        (native_nat_to_int (k + 1 + 1)))
                      (native_int_pow2 (native_nat_to_int (k + 1)))))
                  (intToBvAbconv n (k + 1))) =
                Term.Boolean true := by
            simpa [intToBvAbconv_succ_eq n hn (k + 1)] using
              intToBvAbconv_is_concat_list n hn (k + 1 + 1)
          have hTailNotNil :
              __eo_is_list_nil (Term.UOp UserOp.concat)
                  (intToBvAbconv n (k + 1)) =
                Term.Boolean false :=
            intToBvAbconv_succ_is_not_concat_nil n hn k
          -- v4.33 `simp` unfolds the `intToBvBit` abbrev and distributes
          -- `__eo_to_smt` over the concat, so normalise the eval lemma the same
          -- way and drop the (now redundant) explicit translation rewrite.
          have hBit := intToBvBit_eval M n z
            (native_int_pow2 (native_nat_to_int (k + 1 + 1)))
            (native_int_pow2 (native_nat_to_int (k + 1))) hnEval
          simp [__eo_list_singleton_elim, hList, __eo_requires,
            __eo_list_singleton_elim_2, hTailNotNil, __eo_ite, native_ite,
            native_teq, native_not, SmtEval.native_not] at hBit ⊢
          rw [__smtx_model_eval.eq_36]
          rw [hBit, intToBvAbconv_eval M n z hn hnEval (k + 1)]
          simp [__smtx_model_eval_concat, native_binary_concat]
          have hWidth :
              native_zplus 1 (native_nat_to_int (k + 1)) =
                native_nat_to_int (k + 1 + 1) := by
            simp [native_zplus, native_nat_to_int, Int.add_comm]
          rw [hWidth]
          have hPayload := int_mod_pow2_succ_decomp z (k + 1)
          simp only [native_ite] at hPayload
          -- v4.33 `simp` splits the `SmtValue.Binary` equation into a
          -- conjunction; the width component is now closed by `rfl`.
          refine ⟨rfl, ?_⟩
          rw [hPayload]
          simp [native_mod_total]

private theorem intToBvElim_shape_of_ne_stuck (A : Term) :
    __eo_prog_int_to_bv_elim A ≠ Term.Stuck ->
    ∃ w n b,
      A =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n)) b := by
  intro h
  by_cases hShape :
      ∃ w n b,
        A =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n)) b
  · exact hShape
  · have hStuck : __eo_prog_int_to_bv_elim A = Term.Stuck := by
      rw [__eo_prog_int_to_bv_elim.eq_2]
      intro w n b hEq
      exact hShape ⟨w, n, b, hEq⟩
    exact False.elim (h hStuck)

private theorem intToBvExpanded_eval_rel
    (M : SmtModel) (hM : model_wf M)
    (w n : Term) (i : native_Int)
    (hw : __eo_to_smt w = SmtTerm.Numeral i)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hi0 : native_zleq 0 i = true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat)
            (__abconv_int_to_bv_elim n
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0) w)
              (__eo_ite (__eo_is_z w)
                (__eo_ite (__eo_is_neg w) (Term.Numeral 0)
                  (__eo_pow (Term.Numeral 2) w))
                (Term.Apply (Term.UOp UserOp.int_pow2) w))))))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n))) := by
  have hwTerm : w = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral w i hw
  subst w
  have hiNonneg : 0 <= i := by
    simpa [native_zleq] using hi0
  have hiNotNeg : native_zlt i 0 = false := by
    simp [native_zlt]
    omega
  have hNatToInt : native_nat_to_int (native_int_to_nat i) = i := by
    simpa [native_nat_to_int, native_int_to_nat] using
      (Int.toNat_of_nonneg hiNonneg)
  have hnNN : term_has_non_none_type (__eo_to_smt n) := by
    unfold term_has_non_none_type
    rw [hnTy]
    intro h
    cases h
  have hnEvalTy := type_preservation M hM (__eo_to_smt n) hnNN
  rw [hnTy] at hnEvalTy
  rcases int_value_canonical hnEvalTy with ⟨z, hnEval⟩
  have hnNe : n ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation n (by
      unfold RuleProofs.eo_has_smt_translation
      rw [hnTy]
      intro h
      cases h)
  have hExpandedEval :
      __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat)
            (__abconv_int_to_bv_elim n
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0) (Term.Numeral i))
              (__eo_ite (__eo_is_z (Term.Numeral i))
                (__eo_ite (__eo_is_neg (Term.Numeral i)) (Term.Numeral 0)
                  (__eo_pow (Term.Numeral 2) (Term.Numeral i)))
                (Term.Apply (Term.UOp UserOp.int_pow2) (Term.Numeral i)))))) =
        SmtValue.Binary i (native_mod_total z (native_int_pow2 i)) := by
    have hRepeat :
        __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) (Term.Numeral i) =
          intToBvZeroList (native_int_to_nat i) := by
      simp [__eo_list_repeat, native_ite, hiNotNeg,
        intToBvZeroList_repeat_rec_eq]
    have hPow :
        __eo_ite (__eo_is_z (Term.Numeral i))
            (__eo_ite (__eo_is_neg (Term.Numeral i)) (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2) (Term.Numeral i)))
            (Term.Apply (Term.UOp UserOp.int_pow2) (Term.Numeral i)) =
          Term.Numeral (native_int_pow2 i) := by
      simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
        __eo_ite, native_ite, native_teq, native_and, native_not,
        SmtEval.native_not, hiNotNeg, native_int_pow2]
    rw [hRepeat, hPow]
    have hPowWidth :
        native_int_pow2 (native_nat_to_int (native_int_to_nat i)) =
          native_int_pow2 i := by
      rw [hNatToInt]
    rw [← hPowWidth]
    simpa [intToBvAbconv, hNatToInt] using
      intToBvExpanded_eval M n z hnNe hnEval (native_int_to_nat i)
  have hIntToBvEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) n)) =
        SmtValue.Binary i (native_mod_total z (native_int_pow2 i)) := by
    rw [show
      __eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral i)) n) =
        SmtTerm.int_to_bv (SmtTerm.Numeral i) (__eo_to_smt n) by rfl]
    rw [smtx_eval_int_to_bv_term_eq, __smtx_model_eval.eq_2]
    rw [hnEval]
    rfl
  rw [hExpandedEval, hIntToBvEval]
  exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_int_to_bv_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.int_to_bv_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.int_to_bv_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.int_to_bv_elim args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.int_to_bv_elim args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons A2 argsRest =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons n rest =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                  cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_int_to_bv_elim A)
              change __eo_typeof (__eo_prog_int_to_bv_elim A) = Term.Bool
                at hResultTy
              have hProgNe' : __eo_prog_int_to_bv_elim A ≠ Term.Stuck := by
                exact hProgNe
              rcases intToBvElim_shape_of_ne_stuck A hProgNe' with
                ⟨w, n, rhs, hShape⟩
              subst A
              let intToBv := Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n
              let expanded :=
                __eo_list_singleton_elim (Term.UOp UserOp.concat)
                  (__abconv_int_to_bv_elim n
                    (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.Numeral 0) w)
                    (__eo_ite (__eo_is_z w)
                      (__eo_ite (__eo_is_neg w) (Term.Numeral 0)
                        (__eo_pow (Term.Numeral 2) w))
                      (Term.Apply (Term.UOp UserOp.int_pow2) w)))
              let orig :=
                Term.Apply (Term.Apply (Term.UOp UserOp.eq) intToBv) rhs
              have hReqNe :
                  __eo_requires expanded rhs orig ≠ Term.Stuck := by
                simpa [__eo_prog_int_to_bv_elim, intToBv, expanded, orig]
                  using hProgNe'
              have hExpandedEq : expanded = rhs :=
                eo_requires_arg_eq_of_ne_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                eo_requires_left_ne_stuck_of_ne_stuck hReqNe
              have hRhsNe : rhs ≠ Term.Stuck := by
                rw [← hExpandedEq]
                exact hExpandedNe
              have hProgEq :
                  __eo_prog_int_to_bv_elim
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.eq) intToBv) rhs) =
                    orig := by
                rw [__eo_prog_int_to_bv_elim.eq_1]
                change __eo_requires expanded rhs orig = orig
                simp [__eo_requires, hExpandedEq, hRhsNe, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hOrigTy : __eo_typeof orig = Term.Bool := by
                simpa [hProgEq, orig, intToBv] using hResultTy
              have hOrigBool : RuleProofs.eo_has_bool_type orig :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  orig hATrans hOrigTy
              rcases
                  RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    intToBv rhs hOrigBool with
                ⟨_hSameTy, hIntToBvNN⟩
              have hIntToBvTermNN :
                  term_has_non_none_type
                    (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n)) := by
                unfold term_has_non_none_type
                exact hIntToBvNN
              rcases int_to_bv_args_of_non_none hIntToBvTermNN with
                ⟨i, hw, hnTy, hi0⟩
              have hRelExpanded :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt expanded))
                    (__smtx_model_eval M (__eo_to_smt intToBv)) := by
                simpa [expanded, intToBv] using
                  intToBvExpanded_eval_rel M hM w n i hw hnTy hi0
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt intToBv))
                    (__smtx_model_eval M (__eo_to_smt rhs)) := by
                rw [← hExpandedEq]
                exact RuleProofs.smt_value_rel_symm _ _ hRelExpanded
              have hFact :
                  eo_interprets M (__eo_prog_int_to_bv_elim orig) true := by
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel
                  M intToBv rhs hOrigBool hRel
              exact
                { facts_of_true := by
                    intro _premisesTrue
                    simpa [orig] using hFact
                  has_smt_translation := by
                    rw [hProgEq]
                    exact
                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                        orig hOrigBool }
