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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecRepeat
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecRepeat
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.IteOperands
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.IteOperands

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.eo_and_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_and x y ≠ Term.Stuck) :
    __eo_typeof (__eo_and x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_and] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_or_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_or x y ≠ Term.Stuck) :
    __eo_typeof (__eo_or x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_or] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_xor_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_xor x y ≠ Term.Stuck) :
    __eo_typeof (__eo_xor x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_xor] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_add_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_add x y ≠ Term.Stuck) :
    __eo_typeof (__eo_add x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_add] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_mul_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_mul x y ≠ Term.Stuck) :
    __eo_typeof (__eo_mul x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_mul] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_neg_typeof_bitvec_of_arg_bitvec
    (x : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_neg x) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> simp [__eo_neg] at hX hNe ⊢
  case Binary wx nx =>
    cases hX
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_zdiv_typeof_bitvec_of_args_bitvec_and_ne_stuck
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_zdiv x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zdiv x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_zdiv] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    cases hZero : native_zeq 0 ny <;>
      simp [__eo_requires, __eo_eq, hZero, native_ite, native_teq,
        native_not] at hNe ⊢
    all_goals
      rfl
  all_goals
    first
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_zmod_typeof_bitvec_of_args_bitvec_and_ne_stuck
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_zmod x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zmod x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_zmod] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    cases hZero : native_zeq 0 ny <;>
      simp [__eo_requires, __eo_eq, hZero, native_ite, native_teq,
        native_not] at hNe ⊢
    all_goals
      rfl
  all_goals
    first
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_concat_typeof_bitvec_of_args_bitvec_and_ne_stuck
    (x y : Term) (wx wy : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy))
    (hNe : __eo_concat x y ≠ Term.Stuck) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zplus wx wy)) := by
  cases x <;> cases y <;> simp [__eo_concat] at hX hY hNe ⊢
  case Binary.Binary vx nx vy ny =>
    cases hX
    cases hY
    cases hWidth : native_zleq 0 (native_zplus wx wy) <;>
      simp [__eo_mk_binary, hWidth, native_ite] at hNe ⊢
    all_goals
      first
      | rfl
      | contradiction
  all_goals
    first
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck
    (x y : Term)
    (hNe : __eo_eq x y ≠ Term.Stuck) :
    __eo_typeof (__eo_eq x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_eq] at hNe ⊢

theorem EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck
    (x y : Term)
    (hNe : __eo_gt x y ≠ Term.Stuck) :
    __eo_typeof (__eo_gt x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_gt] at hNe ⊢
  case Binary.Binary wx nx wy ny =>
    by_cases hWidth : wx = wy
    · subst wy
      simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    · simp [__eo_requires, native_ite, native_teq, native_not, hWidth]
        at hNe

theorem EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
    (w : native_Int) (n : Term)
    (hNe : __eo_to_bin (Term.Numeral w) n ≠ Term.Stuck) :
    __eo_typeof (__eo_to_bin (Term.Numeral w) n) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases n <;> simp [__eo_to_bin] at hNe ⊢
  case Numeral n =>
    cases hBound : native_zleq w 4294967296 <;>
      cases hWidth : native_zleq 0 w <;>
      simp [__eo_mk_binary, hBound, hWidth, native_ite] at hNe ⊢
    all_goals
      first
      | rfl
      | contradiction
  case Binary wn n =>
    cases hBound : native_zleq w 4294967296 <;>
      cases hWidth : native_zleq 0 w <;>
      simp [__eo_mk_binary, hBound, hWidth, native_ite] at hNe ⊢
    all_goals
      first
      | rfl
      | contradiction

theorem EvaluateProofInternal.eo_ite_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
    (c n m : Term) (w : native_Int)
    (hNe :
      __eo_ite c (__eo_to_bin (Term.Numeral w) n)
          (__eo_to_bin (Term.Numeral w) m) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite c (__eo_to_bin (Term.Numeral w) n)
          (__eo_to_bin (Term.Numeral w) m)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      c (__eo_to_bin (Term.Numeral w) n)
      (__eo_to_bin (Term.Numeral w) m) hNe with
    ⟨b, hCond, hSel⟩
  cases b
  · rw [hCond]
    have hsimpa :=
      EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck w m hSel
    try simp [__eo_ite] at hsimpa ⊢
    exact hsimpa
  · rw [hCond]
    have hsimpa :=
      EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck w n hSel
    try simp [__eo_ite] at hsimpa ⊢
    exact hsimpa

theorem EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
    (x y : Term) (w : native_Nat)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w) :
    __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool := by
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    simp
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hYTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hYMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hYTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hXTy)
  have hYEoBv :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hYMatch.symm.trans hYTy)
  rw [hXEoBv, hYEoBv]
  simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not]

theorem EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
    (x : Term) (w : native_Nat)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  exact TranslationProofs.eo_to_smt_type_eq_bitvec
    (hXMatch.symm.trans hXTy)

theorem EvaluateProofInternal.eo_typeof_bvand_bitvec_of_smt_bitvec_args
    (x y : Term) (w : native_Nat)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w) :
    __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  have hXEoBv := EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec x w hXTy
  have hYEoBv := EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec y w hYTy
  rw [hXEoBv, hYEoBv]
  simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not]

theorem EvaluateProofInternal.eo_repeat_typeof_bitvec_of_arg_bitvec_and_ne_stuck
    (x : Term) (i w : native_Int)
    (hi1 : native_zleq 1 i = true)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe :
      __bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i)) ≠ Term.Stuck) :
    __eo_typeof
        (__bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zmult i w)) := by
  have hi : (1 : Int) <= i := by
    simpa [native_zleq, SmtEval.native_zleq] using hi1
  have hi0Int : (0 : Int) <= i := by
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
    have hBad : (1 : Int) <= 0 := by
      simpa [hIeq0] using hi
    exact (by decide : ¬ (1 : Int) <= 0) hBad
  by_cases hBinary :
      ∃ wx : native_Int, ∃ nx : native_Int, x = Term.Binary wx nx
  · rcases hBinary with ⟨wx, nx, rfl⟩
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at hX
    cases hX
    have hList :
        __eo_list_repeat (Term.UOp UserOp.concat)
            (Term.Binary w nx) (Term.Numeral i) =
          __eo_list_repeat_rec (Term.UOp UserOp.concat)
            (Term.Binary w nx) (native_int_to_nat i) := by
      simp [__eo_list_repeat, native_ite, hiNotNeg]
    cases hWxNonneg : native_zleq 0 w
    · have hStuck :=
        EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary_stuck_of_neg
          w nx hWxNonneg (native_int_to_nat i) hNatNeZero
      exact False.elim (hNe (by rw [hList, hStuck]))
    · rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary
        w nx hWxNonneg (native_int_to_nat i) with
        ⟨m, hTerm, _hEval, _hCanon⟩
      rw [hList, hTerm]
      change
        __eo_typeof
            (Term.Binary
              (native_zmult (native_nat_to_int (native_int_to_nat i)) w)
              m) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_zmult i w))
      simp [hIntNat]
      rfl
  · have hList (hxNe : x ≠ Term.Stuck) :
        __eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i) =
          __eo_list_repeat_rec (Term.UOp UserOp.concat) x
            (native_int_to_nat i) := by
      cases x <;> simp [__eo_list_repeat, native_ite, hiNotNeg]
        at hxNe ⊢
    by_cases hxStuck : x = Term.Stuck
    · subst x
      simp [__eo_list_repeat, __bv_eval_concat] at hNe
    · have hStuck :=
        EvaluateProofInternal.bv_eval_concat_list_repeat_rec_not_binary_stuck x hBinary
          (native_int_to_nat i) hNatNeZero
      exact False.elim (hNe (by rw [hList hxStuck, hStuck]))

theorem EvaluateProofInternal.eo_extract_typeof_bitvec_of_arg_bitvec_and_ne_stuck
    (x : Term) (i j w : native_Int)
    (hj0 : native_zleq 0 j = true)
    (hWidth : native_zlt 0
      (native_zplus (native_zplus i 1) (native_zneg j)) = true)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe :
      __eo_extract x (Term.Numeral j) (Term.Numeral i) ≠
        Term.Stuck) :
    __eo_typeof (__eo_extract x (Term.Numeral j) (Term.Numeral i)) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral
          (native_zplus (native_zplus i (native_zneg j)) 1)) := by
  cases x <;> simp [__eo_extract] at hX hNe ⊢
  case Binary wx nx =>
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at hX
    cases hX
    have hjNonneg : 0 <= j := by
      simpa [native_zleq, SmtEval.native_zleq] using hj0
    have hjNotNeg : native_zlt j 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using
        Int.not_lt_of_ge hjNonneg
    have hWidthAssoc :
        native_zplus (native_zplus i 1) (native_zneg j) =
          native_zplus (native_zplus i (native_zneg j)) 1 := by
      simp [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    have hWidthPosNative :
        native_zlt 0
            (native_zplus (native_zplus i (native_zneg j)) 1) =
          true := by
      simpa [hWidthAssoc] using hWidth
    have hWidthNonnegNative :
        native_zleq 0
            (native_zplus (native_zplus i (native_zneg j)) 1) =
          true := by
      have hPos :
          (0 : native_Int) <
            native_zplus (native_zplus i (native_zneg j)) 1 := by
        simpa [native_zlt, SmtEval.native_zlt] using hWidthPosNative
      simpa [native_zleq, SmtEval.native_zleq] using Int.le_of_lt hPos
    cases hDeltaNeg :
        native_zlt (native_zplus i (native_zneg j)) 0
    · have hDeltaNotLt : ¬ i + -j < 0 := by
        have hsimpa := hDeltaNeg
        try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
        exact Int.not_lt.mp (of_decide_eq_false hsimpa)
      have hDeltaNonneg : 0 <= i + -j :=
        Int.le_of_not_gt hDeltaNotLt
      have hWidthNonneg :
          native_zleq 0
              (native_zplus (native_zplus i (native_zneg j)) 1) =
            true := by
        have hNonneg : 0 <= i + -j + 1 :=
          Int.add_nonneg hDeltaNonneg (by decide)
        simpa [native_zleq, SmtEval.native_zleq, native_zplus,
          SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
          Int.add_assoc] using hNonneg
      simp [hjNotNeg, hDeltaNeg, native_or, native_ite, __eo_mk_binary,
        hWidthNonneg]
      rfl
    · have hDeltaLt : i + -j < 0 := by
        have hsimpa := hDeltaNeg
        try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
        exact of_decide_eq_true hsimpa
      have hWidthGe : 0 <= i + -j + 1 := by
        simpa [native_zleq, SmtEval.native_zleq, native_zplus,
          SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
          Int.add_assoc] using hWidthNonnegNative
      have hWidthZeroInt : i + -j + 1 = 0 :=
        Int.le_antisymm (Int.add_one_le_iff.mpr hDeltaLt) hWidthGe
      have hWidthZero :
          native_zplus (native_zplus i (native_zneg j)) 1 = 0 := by
        simpa [native_zplus, SmtEval.native_zplus, native_zneg,
          SmtEval.native_zneg, Int.add_assoc] using hWidthZeroInt
      simp [hjNotNeg, hDeltaNeg, native_or, native_ite,
        __eo_lit_type_Binary, __eo_len, __eo_mk_apply, hWidthZero]
      rfl
  all_goals
    first
    | contradiction
    | cases hX

