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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithOperands
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.ArithOperands
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.IteOperands
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.IteOperands
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecTypes
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecTypes

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
    (x y U : Term)
    (hX :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U)
    (hY :
      __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe : __eo_concat x y ≠ Term.Stuck) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  cases x <;> cases y <;> simp [__eo_concat] at hX hY hNe ⊢
  all_goals
    first
    -- `__eo_typeof (Term.String _)` is `Seq Char` for any string, but the
    -- concatenated literal no longer matches `hX`/`hY` syntactically.  This
    -- must come first: `cases hX` succeeds without closing the goal.
    | rfl
    | simpa using hX
    | cases hX
    | cases hY
    | contradiction
  -- `cases hX` substitutes `U` but does not close the goal; once `U` is
  -- concrete the literal's type is `rfl`
  all_goals rfl

theorem EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
    (x i j U : Term)
    (hX :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe : __eo_extract x i j ≠ Term.Stuck) :
    __eo_typeof (__eo_extract x i j) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  cases x <;> cases i <;> cases j <;>
    simp [__eo_extract] at hX hNe ⊢
  all_goals
    first
    | rfl
    | simpa using hX
    | cases hX
    | contradiction
  all_goals rfl

theorem EvaluateProofInternal.eo_not_is_neg_find_typeof_bool_of_ne_stuck
    (x y : Term)
    (hNe : __eo_not (__eo_is_neg (__eo_find x y)) ≠ Term.Stuck) :
    __eo_typeof (__eo_not (__eo_is_neg (__eo_find x y))) =
      Term.Bool := by
  cases x <;> cases y <;>
    simp [__eo_find, __eo_is_neg, __eo_not] at hNe ⊢

theorem EvaluateProofInternal.eo_find_typeof_int_of_ne_stuck
    (x y : Term)
    (hNe : __eo_find x y ≠ Term.Stuck) :
    __eo_typeof (__eo_find x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;>
    simp [__eo_find] at hNe ⊢
  case String.String =>
    rfl

theorem EvaluateProofInternal.eo_seq_type_eq_of_same_smt_elem
    {U V : Term} {T : SmtType}
    (hValid :
      TranslationProofs.eo_type_valid (Term.Apply (Term.UOp UserOp.Seq) U))
    (hU : __eo_to_smt_type U = T)
    (hV : __eo_to_smt_type V = T) :
    Term.Apply (Term.UOp UserOp.Seq) U =
      Term.Apply (Term.UOp UserOp.Seq) V := by
  apply EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hValid
  simp [__eo_to_smt_type, hU, hV]

theorem EvaluateProofInternal.eo_str_replace_body_source_ne_stuck_of_ne_stuck
    (s pat repl : Term)
    (hNe :
      (let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
       __eo_ite (__eo_is_neg idx) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add idx (Term.Numeral (-1 : native_Int))))
            repl)
          (__eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)))) ≠
        Term.Stuck) :
    s ≠ Term.Stuck := by
  let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
  let left :=
    __eo_extract s (Term.Numeral 0)
      (__eo_add idx (Term.Numeral (-1 : native_Int)))
  let inner := __eo_concat left repl
  let right := __eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)
  let body := __eo_ite (__eo_is_neg idx) s (__eo_concat inner right)
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_is_neg idx) s (__eo_concat inner right) hNe with
    ⟨selected, _hCond, hSelectedNe⟩
  cases selected
  · have hTailNe : __eo_concat inner right ≠ Term.Stuck := by
      simpa using hSelectedNe
    have hInnerNe : inner ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftNe : left ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [left, inner] using hInnerNe)
    exact EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [left] using hLeftNe)
  · simpa using hSelectedNe

theorem EvaluateProofInternal.eo_str_replace_body_typeof_seq_of_args_seq_and_ne_stuck
    (s pat repl U : Term)
    (hS : __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) U)
    (hRepl :
      repl ≠ Term.Stuck ->
        __eo_typeof repl = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe :
      (let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
       __eo_ite (__eo_is_neg idx) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add idx (Term.Numeral (-1 : native_Int))))
            repl)
          (__eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)))) ≠
        Term.Stuck) :
    __eo_typeof
      (let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
       __eo_ite (__eo_is_neg idx) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add idx (Term.Numeral (-1 : native_Int))))
            repl)
          (__eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)))) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
  let left :=
    __eo_extract s (Term.Numeral 0)
      (__eo_add idx (Term.Numeral (-1 : native_Int)))
  let inner := __eo_concat left repl
  let right := __eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)
  let body := __eo_ite (__eo_is_neg idx) s (__eo_concat inner right)
  have hSeqNe :
      Term.Apply (Term.UOp UserOp.Seq) U ≠ Term.Stuck := by
    intro h
    cases h
  change __eo_typeof body = Term.Apply (Term.UOp UserOp.Seq) U
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_is_neg idx) s (__eo_concat inner right) hNe with
    ⟨selected, hCond, hSelectedNe⟩
  cases selected
  · dsimp [body]
    rw [hCond]
    change __eo_typeof (__eo_concat inner right) =
      Term.Apply (Term.UOp UserOp.Seq) U
    have hTailNe : __eo_concat inner right ≠ Term.Stuck := by
      simpa using hSelectedNe
    have hInnerNe : inner ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftNe : left ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [left, inner] using hInnerNe)
    have hReplNe : repl ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck (by simpa [left, inner] using hInnerNe)
    have hRightNe : right ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftTy :
        __eo_typeof left = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        s (Term.Numeral 0)
        (__eo_add idx (Term.Numeral (-1 : native_Int))) U hS
        (by simpa [left] using hLeftNe)
    have hInnerTy :
        __eo_typeof inner = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        left repl U hLeftTy (hRepl hReplNe) hInnerNe
    have hRightTy :
        __eo_typeof right = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        s (__eo_add idx (__eo_len pat)) (__eo_len s) U hS
        (by simpa [right] using hRightNe)
    exact
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        inner right U hInnerTy hRightTy hTailNe
  · dsimp [body]
    rw [hCond]
    change __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) U
    exact hS

theorem EvaluateProofInternal.eo_str_indexof_body_typeof_int_of_start_int_and_ne_stuck
    (s pat start runStart : Term)
    (hStart : __eo_typeof start = Term.UOp UserOp.Int)
    (hNe :
      (let lenS := __eo_len s
       let find :=
        __eo_find (__eo_to_str (__eo_extract s start lenS))
          (__eo_to_str pat)
       __eo_ite (__eo_is_neg runStart) (Term.Numeral (-1 : native_Int))
        (__eo_ite (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int))
          (__eo_ite (__eo_is_neg find) find (__eo_add start find)))) ≠
        Term.Stuck) :
    __eo_typeof
      (let lenS := __eo_len s
       let find :=
        __eo_find (__eo_to_str (__eo_extract s start lenS))
          (__eo_to_str pat)
       __eo_ite (__eo_is_neg runStart) (Term.Numeral (-1 : native_Int))
        (__eo_ite (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int))
          (__eo_ite (__eo_is_neg find) find (__eo_add start find)))) =
      Term.UOp UserOp.Int := by
  let lenS := __eo_len s
  let find :=
    __eo_find (__eo_to_str (__eo_extract s start lenS)) (__eo_to_str pat)
  let inner := __eo_ite (__eo_is_neg find) find (__eo_add start find)
  let rest :=
    __eo_ite (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int))
      inner
  let body :=
    __eo_ite (__eo_is_neg runStart) (Term.Numeral (-1 : native_Int))
      rest
  change __eo_typeof body = Term.UOp UserOp.Int
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_is_neg runStart) (Term.Numeral (-1 : native_Int)) rest hNe with
    ⟨topSelected, hTopCond, hTopSelectedNe⟩
  cases topSelected
  · dsimp [body]
    rw [hTopCond]
    change __eo_typeof rest = Term.UOp UserOp.Int
    have hRestNe : rest ≠ Term.Stuck := by
      simpa using hTopSelectedNe
    change
      __eo_ite (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int))
        inner ≠ Term.Stuck at hRestNe
    rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
        (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int)) inner
        hRestNe with
      ⟨gtSelected, hGtCond, hGtSelectedNe⟩
    cases gtSelected
    · dsimp [rest]
      rw [hGtCond]
      change __eo_typeof inner = Term.UOp UserOp.Int
      have hInnerNe : inner ≠ Term.Stuck := by
        simpa using hGtSelectedNe
      change __eo_ite (__eo_is_neg find) find (__eo_add start find) ≠
        Term.Stuck at hInnerNe
      rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
          (__eo_is_neg find) find (__eo_add start find) hInnerNe with
        ⟨findSelected, hFindCond, hFindSelectedNe⟩
      cases findSelected
      · dsimp [inner]
        rw [hFindCond]
        change __eo_typeof (__eo_add start find) = Term.UOp UserOp.Int
        have hAddNe : __eo_add start find ≠ Term.Stuck := by
          simpa using hFindSelectedNe
        have hFindNegNe : __eo_is_neg find ≠ Term.Stuck := by
          rw [hFindCond]
          simp
        have hFindNe : find ≠ Term.Stuck :=
          EvaluateProofInternal.eo_is_neg_arg_ne_stuck hFindNegNe
        have hFindTy : __eo_typeof find = Term.UOp UserOp.Int :=
          EvaluateProofInternal.eo_find_typeof_int_of_ne_stuck
            (__eo_to_str (__eo_extract s start lenS)) (__eo_to_str pat)
            (by simpa [find] using hFindNe)
        exact EvaluateProofInternal.eo_add_typeof_int_of_args_int start find hStart hFindTy hAddNe
      · dsimp [inner]
        rw [hFindCond]
        change __eo_typeof find = Term.UOp UserOp.Int
        have hFindNe : find ≠ Term.Stuck := by
          simpa using hFindSelectedNe
        exact
          EvaluateProofInternal.eo_find_typeof_int_of_ne_stuck
            (__eo_to_str (__eo_extract s start lenS)) (__eo_to_str pat)
            (by simpa [find] using hFindNe)
    · dsimp [rest]
      rw [hGtCond]
      change __eo_typeof (Term.Numeral (-1 : native_Int)) =
        Term.UOp UserOp.Int
      rfl
  · dsimp [body]
    rw [hTopCond]
    change __eo_typeof (Term.Numeral (-1 : native_Int)) =
      Term.UOp UserOp.Int
    rfl

theorem EvaluateProofInternal.eo_str_update_body_source_ne_stuck_of_ne_stuck
    (s n repl : Term)
    (hNe :
      (let lenS := __eo_len s
       __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add n (Term.Numeral (-1 : native_Int))))
            (__eo_extract repl (Term.Numeral 0)
              (__eo_add (__eo_add (__eo_neg n) lenS)
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract s (__eo_add n (__eo_len repl)) lenS))) ≠
        Term.Stuck) :
    s ≠ Term.Stuck := by
  let lenS := __eo_len s
  let left :=
    __eo_extract s (Term.Numeral 0)
      (__eo_add n (Term.Numeral (-1 : native_Int)))
  let middle :=
    __eo_extract repl (Term.Numeral 0)
      (__eo_add (__eo_add (__eo_neg n) lenS)
        (Term.Numeral (-1 : native_Int)))
  let inner := __eo_concat left middle
  let right := __eo_extract s (__eo_add n (__eo_len repl)) lenS
  let body :=
    __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
      (__eo_concat inner right)
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
      (__eo_concat inner right) hNe with
    ⟨selected, _hCond, hSelectedNe⟩
  cases selected
  · have hTailNe : __eo_concat inner right ≠ Term.Stuck := by
      simpa using hSelectedNe
    have hInnerNe : inner ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftNe : left ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [left, inner] using hInnerNe)
    exact EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [left] using hLeftNe)
  · simpa using hSelectedNe

theorem EvaluateProofInternal.eo_str_update_body_typeof_seq_of_args_seq_and_ne_stuck
    (s n repl U : Term)
    (hS : __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) U)
    (hRepl :
      repl ≠ Term.Stuck ->
        __eo_typeof repl = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe :
      (let lenS := __eo_len s
       __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add n (Term.Numeral (-1 : native_Int))))
            (__eo_extract repl (Term.Numeral 0)
              (__eo_add (__eo_add (__eo_neg n) lenS)
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract s (__eo_add n (__eo_len repl)) lenS))) ≠
        Term.Stuck) :
    __eo_typeof
      (let lenS := __eo_len s
       __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add n (Term.Numeral (-1 : native_Int))))
            (__eo_extract repl (Term.Numeral 0)
              (__eo_add (__eo_add (__eo_neg n) lenS)
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract s (__eo_add n (__eo_len repl)) lenS))) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  let lenS := __eo_len s
  let left :=
    __eo_extract s (Term.Numeral 0)
      (__eo_add n (Term.Numeral (-1 : native_Int)))
  let middle :=
    __eo_extract repl (Term.Numeral 0)
      (__eo_add (__eo_add (__eo_neg n) lenS)
        (Term.Numeral (-1 : native_Int)))
  let inner := __eo_concat left middle
  let right := __eo_extract s (__eo_add n (__eo_len repl)) lenS
  let body :=
    __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
      (__eo_concat inner right)
  change __eo_typeof body = Term.Apply (Term.UOp UserOp.Seq) U
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
      (__eo_concat inner right) hNe with
    ⟨selected, hCond, hSelectedNe⟩
  cases selected
  · dsimp [body]
    rw [hCond]
    change __eo_typeof (__eo_concat inner right) =
      Term.Apply (Term.UOp UserOp.Seq) U
    have hTailNe : __eo_concat inner right ≠ Term.Stuck := by
      simpa using hSelectedNe
    have hInnerNe : inner ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftNe : left ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [left, inner] using hInnerNe)
    have hMiddleNe : middle ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck (by simpa [left, inner] using hInnerNe)
    have hReplNe : repl ≠ Term.Stuck :=
      EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [middle] using hMiddleNe)
    have hRightNe : right ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftTy :
        __eo_typeof left = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        s (Term.Numeral 0) (__eo_add n (Term.Numeral (-1 : native_Int)))
        U hS (by simpa [left] using hLeftNe)
    have hMiddleTy :
        __eo_typeof middle = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        repl (Term.Numeral 0)
        (__eo_add (__eo_add (__eo_neg n) lenS)
          (Term.Numeral (-1 : native_Int)))
        U (hRepl hReplNe) (by simpa [middle] using hMiddleNe)
    have hInnerTy :
        __eo_typeof inner = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        left middle U hLeftTy hMiddleTy hInnerNe
    have hRightTy :
        __eo_typeof right = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        s (__eo_add n (__eo_len repl)) lenS U hS
        (by simpa [right] using hRightNe)
    exact
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        inner right U hInnerTy hRightTy hTailNe
  · dsimp [body]
    rw [hCond]
    change __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) U
    exact hS

theorem EvaluateProofInternal.str_leq_eval_rec_typeof_bool_of_ne_stuck :
    ∀ x y : Term,
      __str_leq_eval_rec x y ≠ Term.Stuck ->
        __eo_typeof (__str_leq_eval_rec x y) = Term.Bool
  | Term.Stuck, _, hNe => by
      exact False.elim (hNe rfl)
  | x, Term.Stuck, hNe => by
      cases x <;> simp [__str_leq_eval_rec] at hNe
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2,
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t1) t2,
      hNe => by
      change
        __eo_typeof
            (__eo_ite (__eo_eq s1 t1)
              (__str_leq_eval_rec s2 t2)
              (__eo_gt (__eo_to_z t1) (__eo_to_z s1))) =
          Term.Bool
      rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
          (__eo_eq s1 t1) (__str_leq_eval_rec s2 t2)
          (__eo_gt (__eo_to_z t1) (__eo_to_z s1)) hNe with
        ⟨b, hCond, hSel⟩
      cases b
      · rw [hCond]
        change __eo_gt (__eo_to_z t1) (__eo_to_z s1) ≠ Term.Stuck
          at hSel
        have hsimpa :=
          EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck
            (__eo_to_z t1) (__eo_to_z s1) hSel
        try simp [__eo_ite] at hsimpa ⊢
        exact hsimpa
      · rw [hCond]
        change __str_leq_eval_rec s2 t2 ≠ Term.Stuck at hSel
        have hsimpa :=
          EvaluateProofInternal.str_leq_eval_rec_typeof_bool_of_ne_stuck s2 t2 hSel
        try simp [__eo_ite] at hsimpa ⊢
        exact hsimpa
  | Term.String s, y, hNe => by
      cases s <;> cases y <;>
        simp [__str_leq_eval_rec] at hNe ⊢ <;> rfl
  | x, y, hNe => by
      cases x
      case String s =>
        cases s <;> cases y <;>
          simp [__str_leq_eval_rec] at hNe ⊢ <;> rfl
      case Apply f a =>
        cases y <;> simp [__str_leq_eval_rec] at hNe ⊢ <;> try rfl
        rename_i g b
        cases f <;> cases g <;>
          try (simp [__str_leq_eval_rec] at hNe ⊢ <;> rfl)
        rename_i f1 s1 g1 t1
        cases f1 <;> cases g1 <;>
          try (simp [__str_leq_eval_rec] at hNe ⊢ <;> rfl)
        rename_i op1 op2
        by_cases hOp1 : op1 = UserOp.str_concat
        · subst op1
          by_cases hOp2 : op2 = UserOp.str_concat
          · subst op2
            change
              __eo_typeof
                  (__eo_ite (__eo_eq s1 t1)
                    (__str_leq_eval_rec a b)
                    (__eo_gt (__eo_to_z t1) (__eo_to_z s1))) =
                Term.Bool
            rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
                (__eo_eq s1 t1) (__str_leq_eval_rec a b)
                (__eo_gt (__eo_to_z t1) (__eo_to_z s1)) hNe with
              ⟨b', hCond, hSel⟩
            cases b'
            · rw [hCond]
              change __eo_gt (__eo_to_z t1) (__eo_to_z s1) ≠ Term.Stuck
                at hSel
              have hsimpa :=
                EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck
                  (__eo_to_z t1) (__eo_to_z s1) hSel
              try simp [__eo_ite] at hsimpa ⊢
              exact hsimpa
            · rw [hCond]
              change __str_leq_eval_rec a b ≠ Term.Stuck at hSel
              have hsimpa :=
                EvaluateProofInternal.str_leq_eval_rec_typeof_bool_of_ne_stuck a b hSel
              try simp [__eo_ite] at hsimpa ⊢
              exact hsimpa
          · simp [__str_leq_eval_rec, hOp2] at hNe ⊢ <;> try rfl
        · simp [__str_leq_eval_rec, hOp1] at hNe ⊢ <;> try rfl
      all_goals
        cases y <;> simp [__str_leq_eval_rec] at hNe ⊢ <;> try rfl

theorem EvaluateProofInternal.eo_str_leq_body_typeof_bool_of_seq_char_args_and_ne_stuck
    (x y : Term)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      __eo_ite (__eo_and (__eo_is_str x) (__eo_is_str y))
          (__str_leq_eval_rec (__str_flatten (__str_nary_intro x))
            (__str_flatten (__str_nary_intro y)))
          (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_leq) x)
            y) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_and (__eo_is_str x) (__eo_is_str y))
          (__str_leq_eval_rec (__str_flatten (__str_nary_intro x))
            (__str_flatten (__str_nary_intro y)))
          (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_leq) x)
            y)) = Term.Bool := by
  have hFallback :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y) =
        Term.Bool := by
    change __eo_typeof_str_lt (__eo_typeof x) (__eo_typeof y) = Term.Bool
    rw [hX, hY]
    rfl
  cases x <;> cases y <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_and, __eo_ite,
      __eo_mk_apply, __eo_typeof_str_lt, native_and, native_not,
      native_ite, native_teq] at hX hY hNe hFallback ⊢
  case String.String sx sy =>
    exact EvaluateProofInternal.str_leq_eval_rec_typeof_bool_of_ne_stuck
      (__str_flatten (__str_nary_intro (Term.String sx)))
      (__str_flatten (__str_nary_intro (Term.String sy))) hNe
  all_goals
    first
    | exact hFallback
    | rfl
    | contradiction
    | cases hX
    | cases hY
