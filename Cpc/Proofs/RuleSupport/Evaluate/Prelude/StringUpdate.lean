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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.ValueRel
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.ValueRel
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.SeqOperands
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.SeqOperands
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringIndexof
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringIndexof
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringReplace
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringReplace

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.native_seq_update_string_result
    (s : native_String) (i : native_Int) (repl : native_String) :
    native_String :=
  let len : native_Int := Int.ofNat s.length
  if i < 0 || len <= i then
    s
  else
    let idx := Int.toNat i
    s.take idx ++ repl.take (s.length - idx) ++
      s.drop (idx + repl.length)

theorem EvaluateProofInternal.native_string_valid_seq_update_string_result
    (s repl : native_String) (i : native_Int)
    (hs : native_string_valid s = true)
    (hrepl : native_string_valid repl = true) :
    native_string_valid (EvaluateProofInternal.native_seq_update_string_result s i repl) = true := by
  unfold EvaluateProofInternal.native_seq_update_string_result
  by_cases hGuard :
      (decide (i < 0) || decide (Int.ofNat s.length ≤ i)) = true
  · rw [ite_eq_left hGuard]
    exact hs
  · rw [ite_eq_right hGuard]
    exact native_string_valid_append
      (native_string_valid_append
        (native_string_valid_take (Int.toNat i) hs)
        (native_string_valid_take (s.length - Int.toNat i) hrepl))
      (native_string_valid_drop (Int.toNat i + repl.length) hs)

theorem EvaluateProofInternal.native_seq_update_pack_string
    (s : native_String) (i : native_Int) (repl : native_String) :
    native_pack_seq SmtType.Char
        (native_seq_update
          (native_unpack_seq (native_pack_string s)) i
          (native_unpack_seq (native_pack_string repl))) =
      native_pack_string (EvaluateProofInternal.native_seq_update_string_result s i repl) := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string repl) =
      repl.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  unfold native_seq_update EvaluateProofInternal.native_seq_update_string_result
  simp only [List.length_map]
  by_cases hGuard :
      (decide (i < 0) || decide (Int.ofNat s.length ≤ i)) = true
  · rw [ite_eq_left hGuard, ite_eq_left hGuard]
    simp [native_pack_string]
  · rw [ite_eq_right hGuard, ite_eq_right hGuard]
    simp [native_pack_string, List.map_append]

theorem EvaluateProofInternal.smtx_model_eval_str_update_pack_string
    (s repl : native_String) (i : native_Int) :
    __smtx_model_eval_str_update
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Numeral i)
        (SmtValue.Seq (native_pack_string repl)) =
      SmtValue.Seq
        (native_pack_string (EvaluateProofInternal.native_seq_update_string_result s i repl)) := by
  simp only [__smtx_model_eval_str_update]
  rw [show __smtx_elem_typeof_seq_value (native_pack_string s) =
      SmtType.Char by
    simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
  rw [EvaluateProofInternal.native_seq_update_pack_string]

theorem EvaluateProofInternal.native_seq_update_eq_self_of_neg
    (xs ys : List SmtValue) (i : native_Int)
    (hi : i < 0) :
    native_seq_update xs i ys = xs := by
  unfold native_seq_update
  have hDecNeg : decide (i < 0) = true := decide_eq_true hi
  change
    (if (decide (i < 0) || decide (Int.ofNat xs.length <= i)) = true then
        xs
      else
        List.take (Int.toNat i) xs ++
          List.take (xs.length - Int.toNat i) ys ++
            List.drop (Int.toNat i + ys.length) xs) =
      xs
  rw [ite_eq_left (by rw [hDecNeg]; simp)]

theorem EvaluateProofInternal.native_seq_update_eq_self_of_len_le
    (xs ys : List SmtValue) (i : native_Int)
    (hLen : Int.ofNat xs.length <= i) :
    native_seq_update xs i ys = xs := by
  unfold native_seq_update
  have hDecLen :
      decide (Int.ofNat xs.length <= i) = true := decide_eq_true hLen
  change
    (if (decide (i < 0) || decide (Int.ofNat xs.length <= i)) = true then
        xs
      else
        List.take (Int.toNat i) xs ++
          List.take (xs.length - Int.toNat i) ys ++
            List.drop (Int.toNat i + ys.length) xs) =
      xs
  rw [ite_eq_left (by rw [hDecLen]; simp)]

theorem EvaluateProofInternal.smt_typeof_str_update_eq_typeof_string_of_arg_types
    (s n repl : Term) (result : native_String)
    (hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hNTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hReplTySeq : __smtx_typeof (__eo_to_smt repl) = SmtType.Seq SmtType.Char)
    (hResultValid : native_string_valid result = true) :
    __smtx_typeof
        (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt repl)) =
      __smtx_typeof (SmtTerm.String result) := by
  rw [typeof_str_update_eq]
  simp [__smtx_typeof_str_update, __smtx_typeof, hSTySeq, hNTy,
    hReplTySeq, native_Teq, native_ite, hResultValid]

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_update_to_string_of_runs
    (M : SmtModel)
    (s n repl runS runN runRepl : Term) (result : native_String) :
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt runS)) ->
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt n))
        (__smtx_model_eval M (__eo_to_smt runN)) ->
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt repl))
        (__smtx_model_eval M (__eo_to_smt runRepl)) ->
    __smtx_model_eval_str_update
        (__smtx_model_eval M (__eo_to_smt runS))
        (__smtx_model_eval M (__eo_to_smt runN))
        (__smtx_model_eval M (__eo_to_smt runRepl)) =
      SmtValue.Seq (native_pack_string result) ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt repl)))
        (SmtValue.Seq (native_pack_string result)) := by
  intro hSRel hNRel hReplRel hRunEval
  have hRel :=
    EvaluateProofInternal.smt_value_rel_model_eval_str_update_of_rel
      (__smtx_model_eval M (__eo_to_smt s))
      (__smtx_model_eval M (__eo_to_smt n))
      (__smtx_model_eval M (__eo_to_smt repl))
      (__smtx_model_eval M (__eo_to_smt runS))
      (__smtx_model_eval M (__eo_to_smt runN))
      (__smtx_model_eval M (__eo_to_smt runRepl))
      hSRel hNRel hReplRel
  rw [show
      __smtx_model_eval M
          (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt repl)) =
        __smtx_model_eval_str_update
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt n))
          (__smtx_model_eval M (__eo_to_smt repl)) by
    rw [__smtx_model_eval.eq_90]]
  rw [hRunEval] at hRel
  exact hRel

theorem EvaluateProofInternal.eo_or_bool_args_of_bool
    (x y : Term) (b : Bool) :
    __eo_or x y = Term.Boolean b ->
      ∃ bx, ∃ byv,
        x = Term.Boolean bx ∧ y = Term.Boolean byv ∧
          native_or bx byv = b := by
  cases x <;> cases y <;> intro h <;>
    simp [__eo_or, __eo_requires, native_ite, native_teq] at h
  case Binary.Binary wx nx wy ny =>
    exfalso
    by_cases hEq : wx = wy
    · subst wy
      simp [native_not] at h
    · simp [hEq] at h
  case Boolean.Boolean bx byv =>
    cases h
    exact ⟨bx, byv, rfl, rfl, rfl⟩

theorem EvaluateProofInternal.str_update_result_strings_in_bounds
    (s repl : native_String) (idx : Nat) (hIdxLe : idx ≤ s.length) :
    __eo_concat
        (__eo_concat
          (__eo_extract (Term.String s) (Term.Numeral 0)
            (__eo_add (Term.Numeral (Int.ofNat idx))
              (Term.Numeral (-1 : native_Int))))
          (__eo_extract (Term.String repl) (Term.Numeral 0)
            (__eo_add
              (__eo_add (__eo_neg (Term.Numeral (Int.ofNat idx)))
                (__eo_len (Term.String s)))
              (Term.Numeral (-1 : native_Int)))))
        (__eo_extract (Term.String s)
          (__eo_add (Term.Numeral (Int.ofNat idx))
            (__eo_len (Term.String repl)))
          (__eo_len (Term.String s))) =
      Term.String
        (s.take idx ++ repl.take (s.length - idx) ++
          s.drop (idx + repl.length)) := by
  rw [show
      __eo_extract (Term.String s) (Term.Numeral 0)
          (__eo_add (Term.Numeral (Int.ofNat idx))
            (Term.Numeral (-1 : native_Int))) =
        Term.String (s.take idx) by
    simp [__eo_add, __eo_extract, native_zplus, native_zneg]
    change native_str_substr s 0
        ((Int.ofNat idx : native_Int) + (-1 : native_Int) + 1) =
      s.take idx
    rw [show (Int.ofNat idx + (-1 : native_Int) + 1) =
        Int.ofNat idx by omega]
    exact EvaluateProofInternal.native_str_substr_prefix_take_local s idx]
  rw [show
      __eo_extract (Term.String repl) (Term.Numeral 0)
          (__eo_add
            (__eo_add (__eo_neg (Term.Numeral (Int.ofNat idx)))
              (__eo_len (Term.String s)))
            (Term.Numeral (-1 : native_Int))) =
        Term.String (repl.take (s.length - idx)) by
    simp [__eo_add, __eo_neg, __eo_len, __eo_extract, native_zplus,
      native_zneg, native_str_len]
    change native_str_substr repl 0
        (-(Int.ofNat idx : native_Int) + Int.ofNat s.length +
          (-1 : native_Int) + 1) =
      repl.take (s.length - idx)
    rw [show
        -Int.ofNat idx + Int.ofNat s.length + (-1 : native_Int) + 1 =
          Int.ofNat (s.length - idx) by
      calc
        -Int.ofNat idx + Int.ofNat s.length + (-1 : native_Int) + 1 =
            Int.ofNat s.length - Int.ofNat idx := by omega
        _ = Int.ofNat (s.length - idx) :=
            (Int.ofNat_sub hIdxLe).symm]
    exact EvaluateProofInternal.native_str_substr_prefix_take_local repl (s.length - idx)]
  rw [show
      __eo_extract (Term.String s)
          (__eo_add (Term.Numeral (Int.ofNat idx))
            (__eo_len (Term.String repl)))
          (__eo_len (Term.String s)) =
        Term.String (s.drop (idx + repl.length)) by
    simp [__eo_add, __eo_len, __eo_extract, native_zplus, native_zneg,
      native_str_len]
    change native_str_substr s
        ((Int.ofNat idx : native_Int) + Int.ofNat repl.length)
        (Int.ofNat s.length -
            ((Int.ofNat idx : native_Int) + Int.ofNat repl.length) + 1) =
      s.drop (idx + repl.length)
    rw [show
        Int.ofNat idx + Int.ofNat repl.length =
          Int.ofNat (idx + repl.length) by
      simp]
    exact by
      simpa [native_str_len] using
        EvaluateProofInternal.native_str_substr_suffix_drop_local s (idx + repl.length)]
  simp [__eo_concat, native_str_concat, List.append_assoc]

theorem EvaluateProofInternal.str_update_result_strings
    (s repl : native_String) (i : native_Int) :
    let runLen := __eo_len (Term.String s)
    let runRepl := Term.String repl
    __eo_ite
        (__eo_or (__eo_gt (Term.Numeral 0) (Term.Numeral i))
          (__eo_gt (Term.Numeral i) runLen))
        (Term.String s)
        (__eo_concat
          (__eo_concat
            (__eo_extract (Term.String s) (Term.Numeral 0)
              (__eo_add (Term.Numeral i)
                (Term.Numeral (-1 : native_Int))))
            (__eo_extract runRepl (Term.Numeral 0)
              (__eo_add (__eo_add (__eo_neg (Term.Numeral i)) runLen)
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract (Term.String s)
            (__eo_add (Term.Numeral i) (__eo_len runRepl)) runLen)) =
      Term.String (EvaluateProofInternal.native_seq_update_string_result s i repl) := by
  dsimp
  by_cases hiNeg : i < 0
  · have hLt : native_zlt i 0 = true := by
      rw [show native_zlt i 0 = decide (i < 0) by rfl]
      exact decide_eq_true hiNeg
    simp [EvaluateProofInternal.native_seq_update_string_result, __eo_gt, __eo_or, __eo_ite,
      __eo_len, native_or, native_ite, native_teq, native_str_len,
      hLt, hiNeg]
  · have hLt : native_zlt i 0 = false := by
      rw [show native_zlt i 0 = decide (i < 0) by rfl]
      exact decide_eq_false hiNeg
    by_cases hLenLe : Int.ofNat s.length ≤ i
    · by_cases hLenLt : Int.ofNat s.length < i
      · have hGt : native_zlt (native_str_len s) i = true := by
          rw [show native_zlt (native_str_len s) i =
              decide (native_str_len s < i) by rfl]
          have hsimpa := decide_eq_true hLenLt
          try simp [native_str_len] at hsimpa ⊢
          exact decide_eq_true hsimpa
        have hResultEq : EvaluateProofInternal.native_seq_update_string_result s i repl = s := by
          unfold EvaluateProofInternal.native_seq_update_string_result
          have hGuard :
              (decide (i < 0) ||
                decide (Int.ofNat s.length ≤ i)) = true := by
            rw [show decide (i < 0) = false by
              exact decide_eq_false hiNeg]
            rw [show decide (Int.ofNat s.length ≤ i) = true by
              exact decide_eq_true hLenLe]
            rfl
          rw [ite_eq_left hGuard]
        simp [hResultEq, __eo_len, __eo_gt, __eo_or, __eo_ite,
          native_or, native_ite, native_teq, hLt, hGt]
      · have hiEq : i = Int.ofNat s.length := by
          exact Int.le_antisymm (Int.le_of_not_gt hLenLt) hLenLe
        subst i
        have hGt : native_zlt (native_str_len s) (Int.ofNat s.length) =
            false := by
          rw [show native_zlt (native_str_len s) (Int.ofNat s.length) =
              decide (native_str_len s < Int.ofNat s.length) by rfl]
          simp [native_str_len]
        rw [EvaluateProofInternal.str_update_result_strings_in_bounds s repl s.length
          (Nat.le_refl _)]
        have hDrop : s.drop (s.length + repl.length) = [] :=
          List.drop_eq_nil_of_le (Nat.le_add_right _ _)
        simp [EvaluateProofInternal.native_seq_update_string_result, __eo_len, __eo_gt,
          __eo_or, __eo_ite, native_or, native_ite, native_teq,
          native_str_len, hDrop]
    · have hiNonneg : 0 ≤ i := Int.le_of_not_gt hiNeg
      let idx := Int.toNat i
      have hiEq : i = Int.ofNat idx :=
        (Int.toNat_of_nonneg hiNonneg).symm
      have hIdxLt : idx < s.length := by
        rw [hiEq] at hLenLe
        by_cases hLt : idx < s.length
        · exact hLt
        · exfalso
          exact hLenLe (Int.ofNat_le.mpr (Nat.le_of_not_gt hLt))
      have hLtIdx : native_zlt (Int.ofNat idx) 0 = false := by
        rw [show native_zlt (Int.ofNat idx) 0 =
            decide ((Int.ofNat idx : native_Int) < 0) by rfl]
        simp
      have hGtIdx :
          native_zlt (native_str_len s) (Int.ofNat idx) = false := by
        rw [show native_zlt (native_str_len s) (Int.ofNat idx) =
            decide (native_str_len s < (Int.ofNat idx : native_Int)) by
          rfl]
        apply decide_eq_false
        rw [native_str_len]
        intro hBad
        have hBadNat : s.length < idx := Int.ofNat_lt.mp hBad
        exact (Nat.lt_irrefl idx) (Nat.lt_trans hIdxLt hBadNat)
      have hIdxNonneg : ¬((Int.ofNat idx : native_Int) < 0) := by
        exact Int.not_lt_of_ge (Int.natCast_nonneg idx)
      have hLenNotLeIdx :
          ¬Int.ofNat s.length ≤ (Int.ofNat idx : native_Int) := by
        intro hLe
        exact (Nat.not_le_of_gt hIdxLt) (Int.ofNat_le.mp hLe)
      have hGuardFalseIdx :
          (decide ((Int.ofNat idx : native_Int) < 0) ||
            decide (Int.ofNat s.length ≤ (Int.ofNat idx : native_Int))) =
              false := by
        rw [show decide ((Int.ofNat idx : native_Int) < 0) = false by
          exact decide_eq_false hIdxNonneg]
        rw [show decide (Int.ofNat s.length ≤
            (Int.ofNat idx : native_Int)) = false by
          exact decide_eq_false hLenNotLeIdx]
        rfl
      rw [hiEq]
      rw [EvaluateProofInternal.str_update_result_strings_in_bounds s repl idx
        (Nat.le_of_lt hIdxLt)]
      have hIdxLe : idx ≤ s.length := Nat.le_of_lt hIdxLt
      have hLenNotLtIdx : ¬s.length < idx := by
        intro hBad
        exact (Nat.lt_irrefl idx) (Nat.lt_trans hIdxLt hBad)
      simp [EvaluateProofInternal.native_seq_update_string_result, __eo_len, __eo_gt,
        __eo_or, __eo_ite, native_zlt, native_or, native_ite, native_teq,
        native_str_len, hLenNotLtIdx]
      let body :=
        s.take idx ++
          (repl.take (s.length - idx) ++ s.drop (idx + repl.length))
      change
        (if (Int.ofNat idx : native_Int) < 0 then Term.String s
          else Term.String body) =
        Term.String
          (if (Int.ofNat idx : native_Int) < 0 ∨ s.length ≤ idx then
            s
          else body)
      by_cases hNegIdx : (Int.ofNat idx : native_Int) < 0
      · exact False.elim (hIdxNonneg hNegIdx)
      · have hLenLeIdxFalse : ¬s.length ≤ idx :=
          Nat.not_le_of_gt hIdxLt
        rw [ite_eq_right hNegIdx]
        rw [show
            (if (Int.ofNat idx : native_Int) < 0 ∨ s.length ≤ idx then
              s
            else body) = body by
          rw [ite_eq_right]
          intro hGuard
          cases hGuard with
          | inl hBad => exact hNegIdx hBad
          | inr hBad => exact hLenLeIdxFalse hBad]

theorem EvaluateProofInternal.str_update_run_repl_string_of_body_nonstuck
    (s : native_String) (runRepl : Term) (i : native_Int)
    (hRunReplTy :
      __smtx_typeof (__eo_to_smt runRepl) =
        SmtType.Seq SmtType.Char)
    (hBody :
      __eo_concat
          (__eo_concat
            (__eo_extract (Term.String s) (Term.Numeral 0)
              (__eo_add (Term.Numeral i)
                (Term.Numeral (-1 : native_Int))))
            (__eo_extract runRepl (Term.Numeral 0)
              (__eo_add
                (__eo_add (__eo_neg (Term.Numeral i))
                  (__eo_len (Term.String s)))
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract (Term.String s)
            (__eo_add (Term.Numeral i) (__eo_len runRepl))
            (__eo_len (Term.String s))) ≠ Term.Stuck) :
      ∃ repl : native_String,
        runRepl = Term.String repl ∧ native_string_valid repl = true := by
  cases runRepl
  case String repl =>
    exact ⟨repl, rfl, EvaluateProofInternal.native_string_valid_of_string_type hRunReplTy⟩
  case Binary w n =>
    exfalso
    change __smtx_typeof (SmtTerm.Binary w n) =
      SmtType.Seq SmtType.Char at hRunReplTy
    rw [__smtx_typeof.eq_5] at hRunReplTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hRunReplTy
  all_goals
    exfalso
    apply hBody
    simp [__eo_extract, __eo_concat, __eo_add, __eo_len,
      native_zplus, native_zneg, native_str_len]

theorem EvaluateProofInternal.eo_extract_string_same_index
    (s : native_String) (i : native_Int) :
    __eo_extract (Term.String s) (Term.Numeral i) (Term.Numeral i) =
      Term.String (native_str_substr s i 1) := by
  simp [__eo_extract]
  have h :
      native_zplus (native_zplus i (native_zneg i)) 1 = (1 : native_Int) := by
    change (i + -i) + 1 = (1 : native_Int)
    rw [Int.add_right_neg]
    rfl
  rw [h]

theorem EvaluateProofInternal.eo_extract_string_substr_window
    (s : native_String) (i n : native_Int) :
    __eo_extract (Term.String s) (Term.Numeral i)
        (__eo_add (__eo_add (Term.Numeral i) (Term.Numeral n))
          (Term.Numeral (-1 : native_Int))) =
      Term.String (native_str_substr s i n) := by
  simp [__eo_extract, __eo_add, native_zplus, native_zneg]
  rw [show i + n + -1 + -i + 1 = n by
    simp [Int.add_assoc]
    rw [show -1 + (-i + 1) = -i by
      rw [Int.add_comm (-i) 1]
      rw [← Int.add_assoc]
      simp]
    rw [Int.add_comm n (-i)]
    rw [← Int.add_assoc]
    rw [Int.add_right_neg]
    simp]

theorem EvaluateProofInternal.eo_substr_len_arg_of_end_numeral
    (i j : native_Int) (m : Term)
    (hEnd :
      __eo_add (__eo_add (Term.Numeral i) m)
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral j) :
    ∃ n : native_Int, m = Term.Numeral n ∧ j = i + n + -1 := by
  cases m <;> simp [__eo_add, native_zplus] at hEnd
  case Numeral n =>
    exact ⟨n, rfl, hEnd.symm⟩

theorem EvaluateProofInternal.eo_extract_string_zero_len_minus_one
    (pfx subject : native_String) :
    __eo_extract (Term.String subject) (Term.Numeral 0)
        (__eo_add (__eo_len (Term.String pfx))
          (Term.Numeral (-1 : native_Int))) =
      Term.String (native_str_substr subject 0 (native_str_len pfx)) := by
  simp [__eo_extract, __eo_len, __eo_add, native_zplus, native_zneg]
  rw [show native_str_len pfx + (-1 : native_Int) + 1 =
      native_str_len pfx by
    rw [Int.add_assoc]
    simp]

theorem EvaluateProofInternal.eo_extract_string_suffix_window
    (suffix subject : native_String) :
    __eo_extract (Term.String subject)
        (__eo_add (__eo_len (Term.String subject))
          (__eo_neg (__eo_len (Term.String suffix))))
        (__eo_add (__eo_len (Term.String subject))
          (Term.Numeral (-1 : native_Int))) =
      Term.String
        (native_str_substr subject
          (native_str_len subject + -native_str_len suffix)
          (native_str_len suffix)) := by
  simp [__eo_extract, __eo_len, __eo_add, __eo_neg, native_zplus,
    native_zneg]
  rw [show
      native_str_len subject + -1 +
          -(native_str_len subject + -native_str_len suffix) + 1 =
        native_str_len suffix by
    simp [Int.neg_add, Int.add_assoc, Int.add_comm, Int.add_left_comm]
    rw [Int.add_right_neg]
    rw [Int.add_zero]]

theorem EvaluateProofInternal.smt_value_rel_seq_right_local
    {v : SmtValue} {s : SmtSeq} :
    RuleProofs.smt_value_rel v (SmtValue.Seq s) ->
    ∃ s', v = SmtValue.Seq s' ∧ RuleProofs.smt_seq_rel s' s := by
  intro hRel
  cases v <;>
    simp [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel,
      __smtx_model_eval_eq, native_veq] at hRel ⊢
  case Seq s' =>
    exact hRel

theorem EvaluateProofInternal.smtx_model_eval_str_indexof_pack_string_of_rel
    (a b c : SmtValue) (s pat : native_String) (i : native_Int) :
    RuleProofs.smt_value_rel a
        (SmtValue.Seq (native_pack_string s)) ->
    RuleProofs.smt_value_rel b
        (SmtValue.Seq (native_pack_string pat)) ->
    RuleProofs.smt_value_rel c (SmtValue.Numeral i) ->
      __smtx_model_eval_str_indexof a b c =
        SmtValue.Numeral (native_str_indexof s pat i) := by
  intro hA hB hC
  rcases EvaluateProofInternal.smt_value_rel_seq_right_local hA with
    ⟨aSeq, hAEq, hASeqRel⟩
  rcases EvaluateProofInternal.smt_value_rel_seq_right_local hB with
    ⟨bSeq, hBEq, hBSeqRel⟩
  have hASeqEq :
      aSeq = native_pack_string s :=
    (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
  have hBSeqEq :
      bSeq = native_pack_string pat :=
    (RuleProofs.smt_seq_rel_iff_eq _ _).1 hBSeqRel
  have hCEq : c = SmtValue.Numeral i :=
    EvaluateProofInternal.smt_value_rel_numeral_eq c i hC
  rw [hAEq, hASeqEq, hBEq, hBSeqEq, hCEq]
  exact EvaluateProofInternal.smtx_model_eval_str_indexof_pack_string s pat i

