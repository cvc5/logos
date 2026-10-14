module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Init.Data.Repr
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.Core
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.Core

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.term_apply_ne_stuck (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

theorem EvaluateProofInternal.bv_list_repeat_rec_binary_ne_stuck
    (w n : native_Int) :
    ∀ k : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n) k ≠
        Term.Stuck := by
  intro k
  induction k with
  | zero =>
      change Term.Binary 0 0 ≠ Term.Stuck
      intro h
      cases h
  | succ k ih =>
      change
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) ≠
          Term.Stuck
      rw [EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
        (EvaluateProofInternal.term_apply_ne_stuck _ _) ih]
      exact EvaluateProofInternal.term_apply_ne_stuck _ _

theorem EvaluateProofInternal.bv_list_repeat_rec_binary_succ_eq
    (w n : native_Int) (k : native_Nat) :
    __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
        (Nat.succ k) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k) := by
  change
    __eo_mk_apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k)
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (EvaluateProofInternal.term_apply_ne_stuck _ _)
    (EvaluateProofInternal.bv_list_repeat_rec_binary_ne_stuck w n k)

theorem EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary
    (w n : native_Int)
    (hWNonneg : native_zleq 0 w = true) :
    ∀ k : native_Nat,
      ∃ m : native_Int,
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) =
          Term.Binary (native_zmult (native_nat_to_int k) w) m ∧
        __smtx_repeat_rec k (SmtValue.Binary w n) =
          SmtValue.Binary (native_zmult (native_nat_to_int k) w) m ∧
        native_zeq m
          (native_mod_total m
            (native_int_pow2
              (native_zmult (native_nat_to_int k) w))) =
          true
  | Nat.zero => by
      refine ⟨0, ?_, ?_, ?_⟩
      · change Term.Binary 0 0 =
          Term.Binary (native_zmult (native_nat_to_int 0) w) 0
        simp [SmtEval.native_zmult, Smtm.native_nat_to_int]
      · simp [__smtx_repeat_rec, SmtEval.native_zmult,
          Smtm.native_nat_to_int]
      · simp [SmtEval.native_zeq, SmtEval.native_mod_total,
          SmtEval.native_zmult, Smtm.native_nat_to_int]
  | Nat.succ k => by
      rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary w n hWNonneg k with
        ⟨m, hTerm, hEval, _hCanon⟩
      let recW := native_zmult (native_nat_to_int k) w
      let newW := native_zmult (native_nat_to_int (Nat.succ k)) w
      let newM :=
        native_mod_total (native_binary_concat w n recW m)
          (native_int_pow2 newW)
      have hWidthEq :
          native_zplus w recW = newW := by
        have hWidthEqInt : w + ↑k * w = (↑k + 1) * w := by
          calc
            w + ↑k * w = 1 * w + ↑k * w := by simp
            _ = (1 + ↑k) * w := by rw [Int.add_mul]
            _ = (↑k + 1) * w := by simp [Int.add_comm]
        simpa [recW, newW, SmtEval.native_zplus, SmtEval.native_zmult,
          Smtm.native_nat_to_int] using hWidthEqInt
      have hWidthNonneg :
          native_zleq 0 (native_zplus w recW) = true := by
        have hw : 0 <= w := by
          simpa [SmtEval.native_zleq] using hWNonneg
        have hk : 0 <= native_nat_to_int k := by
          simp [Smtm.native_nat_to_int]
        have hRecW : 0 <= recW := by
          simpa [recW, SmtEval.native_zmult] using Int.mul_nonneg hk hw
        have hAdd : 0 <= w + recW := Int.add_nonneg hw hRecW
        have hsimpa := hAdd
        try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
        exact decide_eq_true hsimpa
      refine ⟨newM, ?_, ?_, ?_⟩
      · rw [EvaluateProofInternal.bv_list_repeat_rec_binary_succ_eq]
        change
          __eo_concat (Term.Binary w n)
              (__bv_eval_concat
                (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                  (Term.Binary w n) k)) =
            Term.Binary newW newM
        rw [hTerm]
        change
          __eo_mk_binary (native_zplus w recW)
              (native_binary_concat w n recW m) =
            Term.Binary newW newM
        have hMk :
            __eo_mk_binary (native_zplus w recW)
                (native_binary_concat w n recW m) =
              Term.Binary (native_zplus w recW)
                (native_mod_total (native_binary_concat w n recW m)
                  (native_int_pow2 (native_zplus w recW))) := by
          simp [__eo_mk_binary, hWidthNonneg, native_ite]
        rw [hMk]
        exact congrArg
          (fun z =>
            Term.Binary z
              (native_mod_total (native_binary_concat w n recW m)
                (native_int_pow2 z)))
          hWidthEq
      · rw [__smtx_repeat_rec, hEval, __smtx_model_eval_concat]
        exact congrArg
          (fun z =>
            SmtValue.Binary z
              (native_mod_total (native_binary_concat w n recW m)
                (native_int_pow2 z)))
          hWidthEq
      · exact native_mod_total_canonical newW
          (native_binary_concat w n recW m)

theorem EvaluateProofInternal.bv_eval_concat_list_repeat_binary_eval
    (M : SmtModel) (i w n : native_Int)
    (hi0 : native_zleq 0 i = true)
    (hWNonneg : native_zleq 0 w = true) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_eval_concat
            (__eo_list_repeat (Term.UOp UserOp.concat)
              (Term.Binary w n) (Term.Numeral i)))) =
      __smtx_repeat_rec (native_int_to_nat i)
        (SmtValue.Binary w n) := by
  have hiNonneg : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hiNotNeg : native_zlt i 0 = false := by
    simp [SmtEval.native_zlt]
    omega
  have hList :
      __eo_list_repeat (Term.UOp UserOp.concat) (Term.Binary w n)
          (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          (native_int_to_nat i) := by
    simp [__eo_list_repeat, native_ite, hiNotNeg]
  rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary w n hWNonneg
      (native_int_to_nat i) with
    ⟨m, hTerm, hEval, _hCanon⟩
  rw [hList, hTerm, hEval]
  change
    __smtx_model_eval M
        (SmtTerm.Binary
          (native_zmult (native_nat_to_int (native_int_to_nat i)) w) m) =
      SmtValue.Binary
        (native_zmult (native_nat_to_int (native_int_to_nat i)) w) m
  rw [__smtx_model_eval.eq_5]

theorem EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary_stuck_of_neg
    (w n : native_Int)
    (hWNeg : native_zleq 0 w = false) :
    ∀ k : native_Nat,
      k ≠ 0 ->
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) =
          Term.Stuck := by
  intro k hk
  induction k with
  | zero =>
      exact False.elim (hk rfl)
  | succ k ih =>
      rw [EvaluateProofInternal.bv_list_repeat_rec_binary_succ_eq]
      change
        __eo_concat (Term.Binary w n)
          (__bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k)) =
          Term.Stuck
      cases k with
      | zero =>
          change __eo_concat (Term.Binary w n) (Term.Binary 0 0) =
            Term.Stuck
          change
            __eo_mk_binary (native_zplus w 0)
                (native_binary_concat w n 0 0) =
              Term.Stuck
          have hWidth :
              native_zleq 0 (native_zplus w 0) = false := by
            simpa [SmtEval.native_zleq, SmtEval.native_zplus]
              using hWNeg
          simp [__eo_mk_binary, hWidth, native_ite]
      | succ k' =>
          have hTail :
              __bv_eval_concat
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Binary w n) (Nat.succ k')) =
                Term.Stuck := by
            exact ih (by intro h; cases h)
          rw [hTail]
          rfl

theorem EvaluateProofInternal.bv_eval_concat_list_repeat_rec_not_binary_stuck
    (x : Term)
    (hNotBinary : ¬ ∃ w : native_Int, ∃ n : native_Int,
      x = Term.Binary w n) :
    ∀ k : native_Nat,
      k ≠ 0 ->
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat) x k) =
          Term.Stuck := by
  intro k hk
  induction k with
  | zero =>
      exact False.elim (hk rfl)
  | succ k ih =>
      cases x with
      | Stuck =>
          rfl
      | String s =>
          cases k with
          | zero =>
              change
                __bv_eval_concat
                    (__eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.concat) (Term.String s))
                      (Term.Binary 0 0)) =
                  Term.Stuck
              rw [EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
                (EvaluateProofInternal.term_apply_ne_stuck _ _)
                (by intro h; cases h)]
              rfl
          | succ k' =>
              change
                __bv_eval_concat
                    (__eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.concat) (Term.String s))
                      (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                        (Term.String s) (Nat.succ k'))) =
                  Term.Stuck
              by_cases hTailStuck :
                  __eo_list_repeat_rec (Term.UOp UserOp.concat)
                      (Term.String s) (Nat.succ k') =
                    Term.Stuck
              · rw [hTailStuck]
                rfl
              · rw [EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
                  (EvaluateProofInternal.term_apply_ne_stuck _ _) hTailStuck]
                change
                  __eo_concat (Term.String s)
                    (__bv_eval_concat
                      (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                        (Term.String s) (Nat.succ k'))) =
                    Term.Stuck
                have hTailEval :
                    __bv_eval_concat
                        (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                          (Term.String s) (Nat.succ k')) =
                      Term.Stuck :=
                  ih (by intro h; cases h)
                rw [hTailEval]
                rfl
      | Binary w n =>
          exfalso
          exact hNotBinary ⟨w, n, rfl⟩
      | __eo_List =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | __eo_List_nil =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List_nil)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List_nil k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List_nil k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Bool =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.Bool)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.Bool k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.Bool k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Boolean b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Boolean b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Boolean b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Boolean b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Numeral n =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Numeral n))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Numeral n) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Numeral n) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Rational q =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Rational q))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Rational q) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Rational q) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | «Type» =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.Type)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.Type k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.Type k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DatatypeTypeRef s =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DatatypeTypeRef s))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DatatypeTypeRef s) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DatatypeTypeRef s) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp op =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UOp op))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp op) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp op) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp1 op a =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UOp1 op a))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp1 op a) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp1 op a) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp2 op a b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.UOp2 op a b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp2 op a b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp2 op a b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp3 op a b c =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.UOp3 op a b c))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp3 op a b c) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp3 op a b c) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Apply f a =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Apply f a))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Apply f a) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Apply f a) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Var s T =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Var s T))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Var s T) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Var s T) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtcAppType a b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtcAppType a b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtcAppType a b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtcAppType a b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtCons s d i =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtCons s d i))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtCons s d i) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtCons s d i) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UConst i T =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UConst i T))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UConst i T) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UConst i T) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | FunType =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.FunType)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.FunType k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.FunType k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | __eo_List_cons =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List_cons)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List_cons k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List_cons k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DatatypeType s d =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DatatypeType s d))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DatatypeType s d) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DatatypeType s d) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtSel s d i j =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtSel s d i j))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtSel s d i j) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtSel s d i j) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | USort i =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.USort i))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.USort i) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.USort i) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      all_goals
        change
          __bv_eval_concat
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.concat) _)
                (__eo_list_repeat_rec (Term.UOp UserOp.concat) _ k)) =
            Term.Stuck
        cases hTail :
            __eo_list_repeat_rec (Term.UOp UserOp.concat) _ k <;>
          simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]

theorem EvaluateProofInternal.eo_repeat_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int)
    (hi1 : native_zleq 1 i = true) :
    __eo_typeof
        (__bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int, ∃ m : native_Int,
      x = Term.Binary wx nx ∧
        native_zleq 0 wx = true ∧
        w = native_zmult i wx ∧
        __bv_eval_concat
            (__eo_list_repeat (Term.UOp UserOp.concat) x
              (Term.Numeral i)) =
          Term.Binary (native_zmult i wx) m ∧
        native_zeq m
          (native_mod_total m
            (native_int_pow2 (native_zmult i wx))) =
          true := by
  intro h
  have hi : (1 : Int) <= i := by
    simpa [native_zleq, SmtEval.native_zleq] using hi1
  have hi0Int : (0 : Int) <= i := by
    omega
  have hi0 : native_zleq 0 i = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hi0Int
  have hiPos : (0 : Int) < i := by
    omega
  have hiNotNeg : native_zlt i 0 = false := by
    simp [native_zlt, SmtEval.native_zlt]
    omega
  have hIntNat :
      native_nat_to_int (native_int_to_nat i) = i := by
    simpa [native_nat_to_int, native_int_to_nat,
      Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hi0Int]
  have hNatNeZero : native_int_to_nat i ≠ 0 := by
    intro hZero
    have hIeq0 : i = 0 := by
      calc
        i = native_nat_to_int (native_int_to_nat i) := hIntNat.symm
        _ = native_nat_to_int 0 := by rw [hZero]
        _ = 0 := by simp [native_nat_to_int, Smtm.native_nat_to_int]
    have hBad : (0 : Int) < 0 := by
      simpa [hIeq0] using hiPos
    exact (by decide : ¬ (0 : Int) < 0) hBad
  have hList (hxNe : x ≠ Term.Stuck) :
      __eo_list_repeat (Term.UOp UserOp.concat) x (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat) x
          (native_int_to_nat i) := by
    cases x <;> simp [__eo_list_repeat, native_ite, hiNotNeg] at hxNe ⊢
  by_cases hBinary :
      ∃ wx : native_Int, ∃ nx : native_Int, x = Term.Binary wx nx
  · rcases hBinary with ⟨wx, nx, rfl⟩
    cases hWxNonneg : native_zleq 0 wx
    · have hStuck :=
        EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary_stuck_of_neg wx nx
          hWxNonneg (native_int_to_nat i) hNatNeZero
      rw [hList (by intro h; cases h), hStuck] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary wx nx hWxNonneg
          (native_int_to_nat i) with
        ⟨m, hTerm, _hEval, hCanon⟩
      have hWidth : w = native_zmult i wx := by
        rw [hList (by intro h; cases h), hTerm] at h
        change
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral
                (native_zmult
                  (native_nat_to_int (native_int_to_nat i)) wx)) =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
        simp [hIntNat]
      have hRepeatTerm :
          __bv_eval_concat
              (__eo_list_repeat (Term.UOp UserOp.concat)
                (Term.Binary wx nx) (Term.Numeral i)) =
            Term.Binary (native_zmult i wx) m := by
        rw [hList (by intro h; cases h)]
        simpa [hIntNat] using hTerm
      have hCanon' :
          native_zeq m
            (native_mod_total m
              (native_int_pow2 (native_zmult i wx))) =
            true := by
        simpa [hIntNat] using hCanon
      exact ⟨wx, nx, m, rfl, hWxNonneg, hWidth, hRepeatTerm, hCanon'⟩
  · by_cases hxStuck : x = Term.Stuck
    · subst x
      simp [__eo_list_repeat, __bv_eval_concat] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · have hStuck :=
        EvaluateProofInternal.bv_eval_concat_list_repeat_rec_not_binary_stuck x hBinary
          (native_int_to_nat i) hNatNeZero
      rw [hList hxStuck, hStuck] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h

