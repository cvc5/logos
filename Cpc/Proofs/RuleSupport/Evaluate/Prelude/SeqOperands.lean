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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCode
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringCode

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.eo_concat_args_string_of_typeof_seq
    (x y T : Term) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.Seq) T ->
    ∃ sx : native_String, ∃ sy : native_String,
      x = Term.String sx ∧ y = Term.String sy ∧
        T = Term.UOp UserOp.Char := by
  cases x <;> intro h
  case String sx =>
    cases y <;> simp only [__eo_concat] at h
    case String sy =>
      change
        __eo_typeof (Term.String (native_str_concat sx sy)) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      change
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
      exact ⟨sx, sy, rfl, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) T at h
      change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_concat] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_mk_binary (native_zplus wx wy)
              (native_binary_concat wx nx wy ny)) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      cases hWidth : native_zleq 0 (native_zplus wx wy)
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
        cases h
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        change
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_zplus wx wy)) =
            Term.Apply (Term.UOp UserOp.Seq) T at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) T at h
      change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.Seq) T at h
    change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
    cases h

theorem EvaluateProofInternal.eo_concat_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx nx wy ny : native_Int,
      x = Term.Binary wx nx ∧ y = Term.Binary wy ny ∧
        w = native_zplus wx wy ∧
          native_zleq 0 (native_zplus wx wy) = true := by
  cases x <;> intro h
  case String sx =>
    cases y <;> simp only [__eo_concat] at h
    case String sy =>
      change
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_concat] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_mk_binary (native_zplus wx wy)
              (native_binary_concat wx nx wy ny)) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases hWidth : native_zleq 0 (native_zplus wx wy)
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        cases h
        exact ⟨wx, nx, wy, ny, rfl, rfl, rfl, hWidth⟩
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.native_string_valid_of_string_type
    {str : native_String}
    (hTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char) :
    native_string_valid str = true := by
  change __smtx_typeof (SmtTerm.String str) =
    SmtType.Seq SmtType.Char at hTy
  cases hValid : native_string_valid str <;>
    simp [__smtx_typeof, native_ite, hValid] at hTy ⊢

theorem EvaluateProofInternal.smt_string_seq_type_inv
    {str : native_String} {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq T) :
    native_string_valid str = true ∧ T = SmtType.Char := by
  change __smtx_typeof (SmtTerm.String str) = SmtType.Seq T at hTy
  rw [__smtx_typeof.eq_4] at hTy
  cases hValid : native_string_valid str
  · simp [native_ite, hValid] at hTy
  · simp [native_ite, hValid] at hTy
    constructor
    · rfl
    · cases hTy
      rfl

theorem EvaluateProofInternal.eo_len_seq_arg_of_nonstuck
    (x : Term) {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hLen : __eo_len x ≠ Term.Stuck) :
    ∃ str : native_String,
      x = Term.String str ∧ native_string_valid str = true ∧
        T = SmtType.Char := by
  cases x <;> simp [__eo_len] at hLen
  case String str =>
    rcases EvaluateProofInternal.smt_string_seq_type_inv hTy with ⟨hValid, hT⟩
    exact ⟨str, rfl, hValid, hT⟩
  case Binary w n =>
    change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Seq T at hTy
    rw [__smtx_typeof.eq_5] at hTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hTy

theorem EvaluateProofInternal.eo_extract_same_seq_int_args_of_nonstuck
    (x n : Term) {T : SmtType}
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (_hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hExt : __eo_extract x n n ≠ Term.Stuck) :
    ∃ str : native_String, ∃ i : native_Int,
      x = Term.String str ∧ n = Term.Numeral i ∧
        native_string_valid str = true ∧ T = SmtType.Char := by
  cases x <;> simp [__eo_extract] at hExt
  case String str =>
    cases n <;> simp at hExt
    case Numeral i =>
      rcases EvaluateProofInternal.smt_string_seq_type_inv hxTy with ⟨hValid, hT⟩
      exact ⟨str, i, rfl, rfl, hValid, hT⟩
  case Binary w nval =>
    change __smtx_typeof (SmtTerm.Binary w nval) = SmtType.Seq T at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq nval (native_mod_total nval (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hxTy

theorem EvaluateProofInternal.eo_extract_seq_args_of_nonstuck
    (x i j : Term) {T : SmtType}
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hExt : __eo_extract x i j ≠ Term.Stuck) :
    ∃ str : native_String, ∃ start stop : native_Int,
      x = Term.String str ∧ i = Term.Numeral start ∧
        j = Term.Numeral stop ∧ native_string_valid str = true ∧
          T = SmtType.Char := by
  cases x <;> simp [__eo_extract] at hExt
  case String str =>
    cases i <;> try
      exact False.elim (hExt rfl)
    case Numeral start =>
      cases j <;> try
        exact False.elim (hExt rfl)
      case Numeral stop =>
        rcases EvaluateProofInternal.smt_string_seq_type_inv hxTy with ⟨hValid, hT⟩
        exact ⟨str, start, stop, rfl, rfl, rfl, hValid, hT⟩
  case Binary w nval =>
    change __smtx_typeof (SmtTerm.Binary w nval) = SmtType.Seq T at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq nval (native_mod_total nval (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hxTy

theorem EvaluateProofInternal.eo_extract_seq_char_numeral_args_of_nonstuck
    (x : Term) (i j : native_Int)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char)
    (hExt : __eo_extract x (Term.Numeral i) (Term.Numeral j) ≠
      Term.Stuck) :
    ∃ str : native_String,
      x = Term.String str ∧ native_string_valid str = true := by
  cases x <;> simp [__eo_extract] at hExt
  case String str =>
    exact ⟨str, rfl, EvaluateProofInternal.native_string_valid_of_string_type hxTy⟩
  case Binary w nval =>
    change __smtx_typeof (SmtTerm.Binary w nval) =
      SmtType.Seq SmtType.Char at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq nval (native_mod_total nval (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hxTy

theorem EvaluateProofInternal.eo_find_seq_args_of_nonstuck
    (x y : Term) {T : SmtType}
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hFind : __eo_find x y ≠ Term.Stuck) :
    ∃ sx sy : native_String,
      x = Term.String sx ∧ y = Term.String sy ∧
          native_string_valid sx = true ∧
          native_string_valid sy = true ∧ T = SmtType.Char := by
  cases x <;> simp [__eo_find] at hFind
  case String sx =>
    cases y <;> simp at hFind
    case String sy =>
      rcases EvaluateProofInternal.smt_string_seq_type_inv hxTy with ⟨hSxValid, hT⟩
      subst T
      exact ⟨sx, sy, rfl, rfl, hSxValid,
        EvaluateProofInternal.native_string_valid_of_string_type hyTy, rfl⟩

theorem EvaluateProofInternal.eo_find_to_str_seq_args_of_nonstuck
    (x y : Term) {T : SmtType}
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hFind : __eo_find (__eo_to_str x) (__eo_to_str y) ≠ Term.Stuck) :
    ∃ sx sy : native_String,
      x = Term.String sx ∧ y = Term.String sy ∧
          native_string_valid sx = true ∧
          native_string_valid sy = true ∧ T = SmtType.Char := by
  cases x <;> simp [__eo_to_str, __eo_find] at hFind hxTy
  case String sx =>
    cases y <;> simp at hFind hyTy
    case String sy =>
      rcases EvaluateProofInternal.smt_string_seq_type_inv hxTy with ⟨hSxValid, hT⟩
      subst T
      exact ⟨sx, sy, rfl, rfl, hSxValid,
        EvaluateProofInternal.native_string_valid_of_string_type hyTy, rfl⟩
    case Numeral n =>
      change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Seq T at hyTy
      rw [__smtx_typeof.eq_2] at hyTy
      cases hyTy
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Seq T at hxTy
    rw [__smtx_typeof.eq_2] at hxTy
    cases hxTy

theorem EvaluateProofInternal.str_replace_run_repl_string_of_nonneg
    (s pat : native_String) (z : Term)
    (hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char)
    (hNonneg : ¬ native_str_indexof s pat 0 < 0)
    (hRun :
      __eo_ite (__eo_is_neg
            (__eo_find (__eo_to_str (Term.String s))
              (__eo_to_str (Term.String pat))))
          (Term.String s)
          (__eo_concat
            (__eo_concat
              (__eo_extract (Term.String s) (Term.Numeral 0)
                (__eo_add
                  (__eo_find (__eo_to_str (Term.String s))
                    (__eo_to_str (Term.String pat)))
                  (Term.Numeral (-1 : native_Int)))) z)
            (__eo_extract (Term.String s)
              (__eo_add
                (__eo_find (__eo_to_str (Term.String s))
                  (__eo_to_str (Term.String pat)))
                (__eo_len (Term.String pat)))
              (__eo_len (Term.String s)))) ≠ Term.Stuck) :
    ∃ repl : native_String,
      z = Term.String repl ∧ native_string_valid repl = true := by
  have hLt : native_zlt (native_str_indexof s pat 0) 0 = false := by
    rw [show native_zlt (native_str_indexof s pat 0) 0 =
      decide (native_str_indexof s pat 0 < 0) by rfl]
    exact decide_eq_false hNonneg
  cases z <;>
    simp [__eo_find, __eo_to_str, __eo_is_neg, __eo_ite, native_ite,
      native_teq, hLt, __eo_extract, __eo_add, __eo_len, __eo_concat,
      native_zplus, native_zneg, native_str_len] at hRun hZTy
  case String repl =>
    exact ⟨repl, rfl, EvaluateProofInternal.native_string_valid_of_string_type hZTy⟩

theorem EvaluateProofInternal.smt_model_eval_seq_of_type_local
    (M : SmtModel) (hM : model_wf M)
    (t : SmtTerm) (T : SmtType)
    (hTy : __smtx_typeof t = SmtType.Seq T) :
    ∃ seq : SmtSeq, __smtx_model_eval M t = SmtValue.Seq seq := by
  have hNN : __smtx_typeof t ≠ SmtType.None := by
    rw [hTy]
    simp
  have hValTy :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact seq_value_canonical (by simpa [hTy] using hValTy)

theorem EvaluateProofInternal.str_to_code_result_string
    {str : native_String}
    (hValid : native_string_valid str = true) :
    __eo_ite (__eo_eq (__eo_len (Term.String str)) (Term.Numeral 1))
        (__eo_to_z (Term.String str))
        (__eo_ite (__eo_is_z (__eo_len (Term.String str)))
          (Term.Numeral (-1 : native_Int))
          (__eo_mk_apply (Term.UOp UserOp.str_to_code) (Term.String str))) =
      Term.Numeral (native_str_to_code str) := by
  cases str with
  | nil =>
      simp [__eo_len, __eo_eq, __eo_ite, __eo_is_z, __eo_is_z_internal,
        native_str_len, native_str_to_code, native_ite, native_teq,
        native_and, native_not]
  | cons c cs =>
      cases cs with
      | nil =>
          have hc : native_char_valid c = true := by
            simpa [native_string_valid] using hValid
          rw [EvaluateProofInternal.eo_to_z_singleton hc]
          simp [__eo_len, __eo_eq, __eo_ite, native_str_len,
            native_str_to_code, native_ite, native_teq, hc]
      | cons d ds =>
          have hNonneg : 0 ≤ (Int.ofNat ds.length) := Int.natCast_nonneg _
          have hLenNe : ¬(1 : Int) = Int.ofNat ds.length + 1 + 1 := by
            omega
          simp [__eo_len, __eo_eq, __eo_ite, __eo_is_z,
            __eo_is_z_internal, native_str_len, native_str_to_code,
            native_ite, native_teq, native_and, native_not]
          by_cases hLen : (1 : Int) = Int.ofNat ds.length + 1 + 1
          · exact False.elim (hLenNe hLen)
          · rfl

