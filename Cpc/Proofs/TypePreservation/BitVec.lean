module

public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.SmtModel
import all Cpc.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Shows that evaluating `ubv_to_int` terms produces values of the expected type. -/
theorem typeof_value_model_eval_ubv_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.ubv_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.ubv_to_int t)) =
      __smtx_typeof (SmtTerm.ubv_to_int t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.ubv_to_int __smtx_model_eval_ubv_to_int
    SmtType.Int t (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres (fun w n hWidth _hMod => by
      simp [__smtx_model_eval_ubv_to_int, __smtx_typeof_value])

/-- Shows that evaluating `sbv_to_int` terms produces values of the expected type. -/
theorem typeof_value_model_eval_sbv_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.sbv_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.sbv_to_int t)) =
      __smtx_typeof (SmtTerm.sbv_to_int t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.sbv_to_int __smtx_model_eval_sbv_to_int
    SmtType.Int t (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres (fun w n hWidth _hMod => by
      simp [__smtx_model_eval_sbv_to_int, __smtx_typeof_value])

/-- Shows that evaluating `bvshl` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvshl
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvshl t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvshl t1 t2)) =
      __smtx_typeof (SmtTerm.bvshl t1 t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvshl __smtx_model_eval_bvshl t1 t2
    (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 (fun w n1 n2 hWidth _hMod1 _hMod2 => by
      simpa [__smtx_model_eval_bvshl] using
        typeof_value_binary_mod_of_nonneg w (native_zmult n1 (native_int_pow2 n2)) hWidth)

/-- Shows that evaluating `bvlshr` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvlshr
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvlshr t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvlshr t1 t2)) =
      __smtx_typeof (SmtTerm.bvlshr t1 t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvlshr __smtx_model_eval_bvlshr t1 t2
    (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 (fun w n1 n2 hWidth _hMod1 _hMod2 => by
      simpa [__smtx_model_eval_bvlshr] using
        typeof_value_binary_mod_of_nonneg w (native_div_total n1 (native_int_pow2 n2)) hWidth)

/-- Shows that evaluating `bvsge_of_bitvec` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsge_of_bitvec
    {v1 v2 : SmtValue}
    {w : native_Nat}
    (h1 : __smtx_typeof_value v1 = SmtType.BitVec w)
    (h2 : __smtx_typeof_value v2 = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvsge v1 v2) = SmtType.Bool := by
  rcases bitvec_value_canonical h1 with ⟨n1, hv1⟩
  rcases bitvec_value_canonical h2 with ⟨n2, hv2⟩
  rw [hv1, hv2]
  exact typeof_value_model_eval_bvsge_value (native_nat_to_int w) n1 n2

/-- Shows that evaluating `bvsdiv_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsdiv_value
    (w n1 n2 : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hMod1 : native_zeq n1 (native_mod_total n1 (native_int_pow2 w)) = true)
    (hMod2 : native_zeq n2 (native_mod_total n2 (native_int_pow2 w)) = true) :
    __smtx_typeof_value (__smtx_model_eval_bvsdiv (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec (native_int_to_nat w) := by
  let v0 := __smtx_model_eval_bvneg (SmtValue.Binary w n2)
  let v1 := __smtx_model_eval_bvneg (SmtValue.Binary w n1)
  let v3 := SmtValue.Binary 1 1
  let v4 :=
    __smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value (SmtValue.Binary w n1)))
      (SmtValue.Numeral 1)
  let v5 := __smtx_model_eval_eq (__smtx_model_eval_extract v4 v4 (SmtValue.Binary w n2)) v3
  let v6 := __smtx_model_eval_eq (__smtx_model_eval_extract v4 v4 (SmtValue.Binary w n1)) v3
  let v7 := __smtx_model_eval_not v6
  let v8 := __smtx_model_eval_not v5
  have hBin1 : __smtx_typeof_value (SmtValue.Binary w n1) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_binary_of_nonneg w n1 hWidth hMod1
  have hBin2 : __smtx_typeof_value (SmtValue.Binary w n2) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_binary_of_nonneg w n2 hWidth hMod2
  have hv0 : __smtx_typeof_value v0 = SmtType.BitVec (native_int_to_nat w) := by
    simpa [v0] using typeof_value_model_eval_bvneg_value w n2 hWidth
  have hv1 : __smtx_typeof_value v1 = SmtType.BitVec (native_int_to_nat w) := by
    simpa [v1] using typeof_value_model_eval_bvneg_value w n1 hWidth
  have h5 : __smtx_typeof_value v5 = SmtType.Bool := by
    unfold v5
    exact typeof_value_model_eval_eq_value _ _
  have h6 : __smtx_typeof_value v6 = SmtType.Bool := by
    unfold v6
    exact typeof_value_model_eval_eq_value _ _
  have h7 : __smtx_typeof_value v7 = SmtType.Bool := by
    simpa [v7] using typeof_value_model_eval_not_of_bool h6
  have h8 : __smtx_typeof_value v8 = SmtType.Bool := by
    simpa [v8] using typeof_value_model_eval_not_of_bool h5
  have h78 : __smtx_typeof_value (__smtx_model_eval_and v7 v8) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h7 h8
  have h68 : __smtx_typeof_value (__smtx_model_eval_and v6 v8) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h6 h8
  have h75 : __smtx_typeof_value (__smtx_model_eval_and v7 v5) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h7 h5
  have hu0 : __smtx_typeof_value (__smtx_model_eval_bvudiv (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvudiv_value w n1 n2 hWidth
  have hu1 : __smtx_typeof_value (__smtx_model_eval_bvudiv v1 (SmtValue.Binary w n2)) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvudiv_of_bitvec hv1 hBin2
  have hu2 : __smtx_typeof_value (__smtx_model_eval_bvudiv (SmtValue.Binary w n1) v0) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvudiv_of_bitvec hBin1 hv0
  have hu3 : __smtx_typeof_value (__smtx_model_eval_bvudiv v1 v0) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvudiv_of_bitvec hv1 hv0
  have hn1 : __smtx_typeof_value (__smtx_model_eval_bvneg (__smtx_model_eval_bvudiv v1 (SmtValue.Binary w n2))) =
      SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvneg_of_bitvec hu1
  have hn2 : __smtx_typeof_value (__smtx_model_eval_bvneg (__smtx_model_eval_bvudiv (SmtValue.Binary w n1) v0)) =
      SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvneg_of_bitvec hu2
  unfold __smtx_model_eval_bvsdiv
  simpa [v0, v1, v3, v4, v5, v6, v7, v8] using
    (typeof_value_model_eval_ite_of_bool h78 hu0
      (typeof_value_model_eval_ite_of_bool h68 hn1
        (typeof_value_model_eval_ite_of_bool h75 hn2 hu3)))

/-- Shows that evaluating `bvsdiv` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsdiv
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvsdiv t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvsdiv t1 t2)) =
      __smtx_typeof (SmtTerm.bvsdiv t1 t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvsdiv __smtx_model_eval_bvsdiv t1 t2
    (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 typeof_value_model_eval_bvsdiv_value

/-- Shows that evaluating `bvsrem_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsrem_value
    (w n1 n2 : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hMod1 : native_zeq n1 (native_mod_total n1 (native_int_pow2 w)) = true)
    (hMod2 : native_zeq n2 (native_mod_total n2 (native_int_pow2 w)) = true) :
    __smtx_typeof_value (__smtx_model_eval_bvsrem (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec (native_int_to_nat w) := by
  let v0 := __smtx_model_eval_bvneg (SmtValue.Binary w n2)
  let v1 := __smtx_model_eval_bvneg (SmtValue.Binary w n1)
  let v3 := SmtValue.Binary 1 1
  let v4 :=
    __smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value (SmtValue.Binary w n1)))
      (SmtValue.Numeral 1)
  let v5 := __smtx_model_eval_eq (__smtx_model_eval_extract v4 v4 (SmtValue.Binary w n2)) v3
  let v6 := __smtx_model_eval_eq (__smtx_model_eval_extract v4 v4 (SmtValue.Binary w n1)) v3
  let v7 := __smtx_model_eval_not v6
  let v8 := __smtx_model_eval_not v5
  have hBin1 : __smtx_typeof_value (SmtValue.Binary w n1) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_binary_of_nonneg w n1 hWidth hMod1
  have hBin2 : __smtx_typeof_value (SmtValue.Binary w n2) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_binary_of_nonneg w n2 hWidth hMod2
  have hv0 : __smtx_typeof_value v0 = SmtType.BitVec (native_int_to_nat w) := by
    simpa [v0] using typeof_value_model_eval_bvneg_value w n2 hWidth
  have hv1 : __smtx_typeof_value v1 = SmtType.BitVec (native_int_to_nat w) := by
    simpa [v1] using typeof_value_model_eval_bvneg_value w n1 hWidth
  have h5 : __smtx_typeof_value v5 = SmtType.Bool := by
    unfold v5
    exact typeof_value_model_eval_eq_value _ _
  have h6 : __smtx_typeof_value v6 = SmtType.Bool := by
    unfold v6
    exact typeof_value_model_eval_eq_value _ _
  have h7 : __smtx_typeof_value v7 = SmtType.Bool := by
    simpa [v7] using typeof_value_model_eval_not_of_bool h6
  have h8 : __smtx_typeof_value v8 = SmtType.Bool := by
    simpa [v8] using typeof_value_model_eval_not_of_bool h5
  have h78 : __smtx_typeof_value (__smtx_model_eval_and v7 v8) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h7 h8
  have h68 : __smtx_typeof_value (__smtx_model_eval_and v6 v8) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h6 h8
  have h75 : __smtx_typeof_value (__smtx_model_eval_and v7 v5) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h7 h5
  have hu0 : __smtx_typeof_value (__smtx_model_eval_bvurem (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvurem_value w n1 n2 hWidth
  have hu1 : __smtx_typeof_value (__smtx_model_eval_bvurem v1 (SmtValue.Binary w n2)) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvurem_of_bitvec hv1 hBin2
  have hu2 : __smtx_typeof_value (__smtx_model_eval_bvurem (SmtValue.Binary w n1) v0) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvurem_of_bitvec hBin1 hv0
  have hu3 : __smtx_typeof_value (__smtx_model_eval_bvurem v1 v0) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvurem_of_bitvec hv1 hv0
  have hn1 : __smtx_typeof_value (__smtx_model_eval_bvneg (__smtx_model_eval_bvurem v1 (SmtValue.Binary w n2))) =
      SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvneg_of_bitvec hu1
  have hn3 : __smtx_typeof_value (__smtx_model_eval_bvneg (__smtx_model_eval_bvurem v1 v0)) =
      SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvneg_of_bitvec hu3
  unfold __smtx_model_eval_bvsrem
  simpa [v0, v1, v3, v4, v5, v6, v7, v8] using
    (typeof_value_model_eval_ite_of_bool h78 hu0
      (typeof_value_model_eval_ite_of_bool h68 hn1
        (typeof_value_model_eval_ite_of_bool h75 hu2 hn3)))

/-- Shows that evaluating `bvsrem` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsrem
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvsrem t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvsrem t1 t2)) =
      __smtx_typeof (SmtTerm.bvsrem t1 t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvsrem __smtx_model_eval_bvsrem t1 t2
    (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 typeof_value_model_eval_bvsrem_value

/-- Shows that evaluating `bvsmod_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsmod_value
    (w n1 n2 : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hMod1 : native_zeq n1 (native_mod_total n1 (native_int_pow2 w)) = true)
    (hMod2 : native_zeq n2 (native_mod_total n2 (native_int_pow2 w)) = true) :
    __smtx_typeof_value (__smtx_model_eval_bvsmod (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec (native_int_to_nat w) := by
  let v1 := SmtValue.Binary 1 1
  let v2 := __smtx_bv_sizeof_value (SmtValue.Binary w n1)
  let v3 := __smtx_model_eval__ (SmtValue.Numeral v2) (SmtValue.Numeral 1)
  let v4 := __smtx_model_eval_eq (__smtx_model_eval_extract v3 v3 (SmtValue.Binary w n2)) v1
  let v5 := __smtx_model_eval_eq (__smtx_model_eval_extract v3 v3 (SmtValue.Binary w n1)) v1
  let v6 :=
    __smtx_model_eval_bvurem
      (__smtx_model_eval_ite v5 (__smtx_model_eval_bvneg (SmtValue.Binary w n1)) (SmtValue.Binary w n1))
      (__smtx_model_eval_ite v4 (__smtx_model_eval_bvneg (SmtValue.Binary w n2)) (SmtValue.Binary w n2))
  let v7 := __smtx_model_eval_bvneg v6
  let v8 := __smtx_model_eval_not v5
  let v9 := __smtx_model_eval_not v4
  have hBin1 : __smtx_typeof_value (SmtValue.Binary w n1) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_binary_of_nonneg w n1 hWidth hMod1
  have hBin2 : __smtx_typeof_value (SmtValue.Binary w n2) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_binary_of_nonneg w n2 hWidth hMod2
  have hNeg1 : __smtx_typeof_value (__smtx_model_eval_bvneg (SmtValue.Binary w n1)) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvneg_value w n1 hWidth
  have hNeg2 : __smtx_typeof_value (__smtx_model_eval_bvneg (SmtValue.Binary w n2)) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvneg_value w n2 hWidth
  have h4 : __smtx_typeof_value v4 = SmtType.Bool := by
    unfold v4
    exact typeof_value_model_eval_eq_value _ _
  have h5 : __smtx_typeof_value v5 = SmtType.Bool := by
    unfold v5
    exact typeof_value_model_eval_eq_value _ _
  have hAbs1 :
      __smtx_typeof_value
          (__smtx_model_eval_ite v5 (__smtx_model_eval_bvneg (SmtValue.Binary w n1)) (SmtValue.Binary w n1)) =
        SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_ite_of_bool h5 hNeg1 hBin1
  have hAbs2 :
      __smtx_typeof_value
          (__smtx_model_eval_ite v4 (__smtx_model_eval_bvneg (SmtValue.Binary w n2)) (SmtValue.Binary w n2)) =
        SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_ite_of_bool h4 hNeg2 hBin2
  have h6 : __smtx_typeof_value v6 = SmtType.BitVec (native_int_to_nat w) := by
    unfold v6
    exact typeof_value_model_eval_bvurem_of_bitvec hAbs1 hAbs2
  have h7 : __smtx_typeof_value v7 = SmtType.BitVec (native_int_to_nat w) := by
    unfold v7
    exact typeof_value_model_eval_bvneg_of_bitvec h6
  have h8 : __smtx_typeof_value v8 = SmtType.Bool := by
    simpa [v8] using typeof_value_model_eval_not_of_bool h5
  have h9 : __smtx_typeof_value v9 = SmtType.Bool := by
    simpa [v9] using typeof_value_model_eval_not_of_bool h4
  have hEq0 : __smtx_typeof_value (__smtx_model_eval_eq v6 (SmtValue.Binary v2 0)) = SmtType.Bool := by
    exact typeof_value_model_eval_eq_value _ _
  have h89 : __smtx_typeof_value (__smtx_model_eval_and v8 v9) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h8 h9
  have h59 : __smtx_typeof_value (__smtx_model_eval_and v5 v9) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h5 h9
  have h84 : __smtx_typeof_value (__smtx_model_eval_and v8 v4) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h8 h4
  have hAdd1 : __smtx_typeof_value (__smtx_model_eval_bvadd v7 (SmtValue.Binary w n2)) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvadd_of_bitvec h7 hBin2
  have hAdd2 : __smtx_typeof_value (__smtx_model_eval_bvadd v6 (SmtValue.Binary w n2)) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvadd_of_bitvec h6 hBin2
  unfold __smtx_model_eval_bvsmod
  simpa [v1, v2, v3, v4, v5, v6, v7, v8, v9] using
    (typeof_value_model_eval_ite_of_bool hEq0 h6
      (typeof_value_model_eval_ite_of_bool h89 h6
        (typeof_value_model_eval_ite_of_bool h59 hAdd1
          (typeof_value_model_eval_ite_of_bool h84 hAdd2 h7))))

/-- Shows that evaluating `bvsmod` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsmod
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvsmod t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvsmod t1 t2)) =
      __smtx_typeof (SmtTerm.bvsmod t1 t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvsmod __smtx_model_eval_bvsmod t1 t2
    (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 typeof_value_model_eval_bvsmod_value

/-- Shows that evaluating `bvashr_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvashr_value
    (w n1 n2 : native_Int)
    (hWidth : native_zleq 0 w = true)
    (_hMod1 : native_zeq n1 (native_mod_total n1 (native_int_pow2 w)) = true)
    (hMod2 : native_zeq n2 (native_mod_total n2 (native_int_pow2 w)) = true) :
    __smtx_typeof_value (__smtx_model_eval_bvashr (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec (native_int_to_nat w) := by
  let v1 :=
    __smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value (SmtValue.Binary w n1)))
      (SmtValue.Numeral 1)
  have hBin2 : __smtx_typeof_value (SmtValue.Binary w n2) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_binary_of_nonneg w n2 hWidth hMod2
  have hCond :
      __smtx_typeof_value
          (__smtx_model_eval_eq (__smtx_model_eval_extract v1 v1 (SmtValue.Binary w n1)) (SmtValue.Binary 1 0)) =
        SmtType.Bool := by
    exact typeof_value_model_eval_eq_value _ _
  have hL : __smtx_typeof_value (__smtx_model_eval_bvlshr (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvlshr_value w n1 n2 hWidth
  have hNot : __smtx_typeof_value (__smtx_model_eval_bvnot (SmtValue.Binary w n1)) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvnot_value w n1 hWidth
  have hR0 :
      __smtx_typeof_value
          (__smtx_model_eval_bvlshr (__smtx_model_eval_bvnot (SmtValue.Binary w n1)) (SmtValue.Binary w n2)) =
        SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvlshr_of_bitvec hNot hBin2
  have hR :
      __smtx_typeof_value
          (__smtx_model_eval_bvnot
            (__smtx_model_eval_bvlshr (__smtx_model_eval_bvnot (SmtValue.Binary w n1)) (SmtValue.Binary w n2))) =
        SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvnot_of_bitvec hR0
  unfold __smtx_model_eval_bvashr
  simpa [v1] using typeof_value_model_eval_ite_of_bool hCond hL hR

/-- Shows that evaluating `bvashr` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvashr
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvashr t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvashr t1 t2)) =
      __smtx_typeof (SmtTerm.bvashr t1 t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvashr __smtx_model_eval_bvashr t1 t2
    (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 typeof_value_model_eval_bvashr_value

/-- Shows that evaluating `bvssubo_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvssubo_value
    (w n1 n2 : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hMod1 : native_zeq n1 (native_mod_total n1 (native_int_pow2 w)) = true)
    (_hMod2 : native_zeq n2 (native_mod_total n2 (native_int_pow2 w)) = true) :
    __smtx_typeof_value (__smtx_model_eval_bvssubo (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  have hBin1 : __smtx_typeof_value (SmtValue.Binary w n1) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_binary_of_nonneg w n1 hWidth hMod1
  have hCond : __smtx_typeof_value (__smtx_model_eval_bvnego (SmtValue.Binary w n2)) = SmtType.Bool := by
    exact typeof_value_model_eval_bvnego_value w n2
  have hThen :
      __smtx_typeof_value
          (__smtx_model_eval_bvsge (SmtValue.Binary w n1)
            (SmtValue.Binary (__smtx_bv_sizeof_value (SmtValue.Binary w n1)) 0)) =
        SmtType.Bool := by
    simpa [__smtx_bv_sizeof_value] using typeof_value_model_eval_bvsge_value w n1 0
  have hNeg2 : __smtx_typeof_value (__smtx_model_eval_bvneg (SmtValue.Binary w n2)) = SmtType.BitVec (native_int_to_nat w) := by
    exact typeof_value_model_eval_bvneg_value w n2 hWidth
  have hElse :
      __smtx_typeof_value
          (__smtx_model_eval_bvsaddo (SmtValue.Binary w n1) (__smtx_model_eval_bvneg (SmtValue.Binary w n2))) =
        SmtType.Bool := by
    exact typeof_value_model_eval_bvsaddo_of_bitvec hBin1 hNeg2
  unfold __smtx_model_eval_bvssubo
  exact typeof_value_model_eval_ite_of_bool hCond hThen hElse

/-- Shows that evaluating `bvssubo` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvssubo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvssubo t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvssubo t1 t2)) =
      __smtx_typeof (SmtTerm.bvssubo t1 t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvssubo __smtx_model_eval_bvssubo
    SmtType.Bool t1 t2 (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 typeof_value_model_eval_bvssubo_value

/-- Shows that evaluating `bvsdivo_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsdivo_value
    (w n1 n2 : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvsdivo (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  have hCond : __smtx_typeof_value (__smtx_model_eval_bvnego (SmtValue.Binary w n1)) = SmtType.Bool := by
    exact typeof_value_model_eval_bvnego_value w n1
  have hEq :
      __smtx_typeof_value
          (__smtx_model_eval_eq (SmtValue.Binary w n2)
            (__smtx_model_eval_bvnot
              (SmtValue.Binary (__smtx_bv_sizeof_value (SmtValue.Binary w n1)) 0))) =
        SmtType.Bool := by
    simpa [__smtx_bv_sizeof_value] using
      (typeof_value_model_eval_eq_value
        (SmtValue.Binary w n2)
        (__smtx_model_eval_bvnot (SmtValue.Binary w 0)))
  unfold __smtx_model_eval_bvsdivo
  exact typeof_value_model_eval_and_of_bool hCond hEq

/-- Shows that evaluating `bvsdivo` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsdivo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvsdivo t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvsdivo t1 t2)) =
      __smtx_typeof (SmtTerm.bvsdivo t1 t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsdivo __smtx_model_eval_bvsdivo
    SmtType.Bool t1 t2 (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2
      (fun w n1 n2 hWidth _hMod1 _hMod2 => typeof_value_model_eval_bvsdivo_value w n1 n2 hWidth)

/-- Lemma about `model_eval_repeat_rec_binary`. -/
theorem model_eval_repeat_rec_binary :
    ∀ n : native_Nat, ∀ w x : native_Int,
      ∃ m : native_Int,
        __smtx_repeat_rec n (SmtValue.Binary w x) =
          SmtValue.Binary (native_zmult (native_nat_to_int n) w) m ∧
        native_zeq m
          (native_mod_total m (native_int_pow2 (native_zmult (native_nat_to_int n) w))) = true
  | native_nat_zero, w, x => by
      refine ⟨0, ?_⟩
      constructor
      · simp [__smtx_repeat_rec, SmtEval.native_zmult, Smtm.native_nat_to_int]
      · simp [SmtEval.native_zeq, SmtEval.native_mod_total, SmtEval.native_zmult,
          Smtm.native_nat_to_int]
  | native_nat_succ n, w, x => by
      rcases model_eval_repeat_rec_binary n w x with ⟨m, hm, hCanon⟩
      refine ⟨native_mod_total
        (native_binary_concat w x (native_zmult (native_nat_to_int n) w) m)
        (native_int_pow2 (native_zmult (native_nat_to_int (native_nat_succ n)) w)), ?_, ?_⟩
      rw [__smtx_repeat_rec, hm, __smtx_model_eval_concat]
      have hWidthEq : w + ↑n * w = (↑n + 1) * w := by
        calc
          w + ↑n * w = 1 * w + ↑n * w := by simp
          _ = (1 + ↑n) * w := by rw [Int.add_mul]
          _ = (↑n + 1) * w := by simp [Int.add_comm]
      have hWidthEq' :
          native_zplus w (native_zmult (native_nat_to_int n) w) =
            native_zmult (native_nat_to_int (native_nat_succ n)) w := by
        simpa [SmtEval.native_zplus, SmtEval.native_zmult, Smtm.native_nat_to_int] using hWidthEq
      exact congrArg
        (fun z =>
          SmtValue.Binary z
            (native_mod_total
              (native_binary_concat w x (native_zmult (native_nat_to_int n) w) m)
              (native_int_pow2 z)))
        hWidthEq'
      exact native_mod_total_canonical
        (native_zmult (native_nat_to_int (native_nat_succ n)) w)
        (native_binary_concat w x (native_zmult (native_nat_to_int n) w) m)

/-- Shows that evaluating `repeat` terms produces values of the expected type. -/
theorem typeof_value_model_eval_repeat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.repeat t1 t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.repeat t1 t2)) =
      __smtx_typeof (SmtTerm.repeat t1 t2) := by
  rcases repeat_args_of_non_none ht with ⟨i, w, h1, h2, hi1⟩
  rw [show __smtx_typeof (SmtTerm.repeat t1 t2) =
      SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w))) by
    rw [typeof_repeat_eq, h1, h2]
    simp [__smtx_typeof_repeat, native_ite, hi1]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [h1]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv, __smtx_model_eval_repeat]
  have hi : 0 <= i := by
    have hi' : 1 <= i := by
      simpa [SmtEval.native_zleq] using hi1
    calc
      (0 : Int) <= 1 := by decide
      _ <= i := hi'
  have hw0 : native_zleq 0 (native_nat_to_int w) = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  have hw : 0 <= native_nat_to_int w := by
    simpa [SmtEval.native_zleq] using hw0
  have hMult : native_zleq 0 (native_zmult i (native_nat_to_int w)) = true := by
    have hMultInt : 0 <= i * native_nat_to_int w := Int.mul_nonneg hi hw
    unfold native_zleq native_zmult
    exact decide_eq_true hMultInt
  rcases model_eval_repeat_rec_binary (native_int_to_nat i) (native_nat_to_int w) n with ⟨m, hm, hCanon⟩
  rw [hm]
  have hNat :
      native_zmult (native_nat_to_int (native_int_to_nat i)) (native_nat_to_int w) =
        native_zmult i (native_nat_to_int w) := by
    simp [SmtEval.native_zmult, Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hi]
  rw [hNat]
  exact typeof_value_binary_of_nonneg (native_zmult i (native_nat_to_int w)) m hMult (by
    simpa [SmtEval.native_zmult, Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hi] using hCanon)

/-- Lemma about `model_eval_rotate_left_step_binary`. -/
theorem model_eval_rotate_left_step_binary
    (w x : native_Int) :
    ∃ y : native_Int,
      __smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral (native_zplus (native_zplus w (native_zneg 1)) (native_zneg 1)))
            (SmtValue.Numeral 0)
            (SmtValue.Binary w x))
          (__smtx_model_eval_extract
            (SmtValue.Numeral (native_zplus w (native_zneg 1)))
            (SmtValue.Numeral (native_zplus w (native_zneg 1)))
            (SmtValue.Binary w x)) =
        SmtValue.Binary w y ∧
      native_zeq y (native_mod_total y (native_int_pow2 w)) = true := by
  let hi := native_zplus w (native_zneg 1)
  let w1 := native_zplus (native_zplus (native_zplus hi (native_zneg 1)) 1) (native_zneg 0)
  let w2 := native_zplus (native_zplus hi 1) (native_zneg hi)
  refine ⟨native_mod_total
      (native_binary_concat w1
        (native_mod_total
          (native_binary_extract w x (native_zplus hi (native_zneg 1)) 0)
          (native_int_pow2 w1))
        w2
        (native_mod_total (native_binary_extract w x hi hi) (native_int_pow2 w2)))
      (native_int_pow2 w), ?_, ?_⟩
  · simp [__smtx_model_eval_concat, __smtx_model_eval_extract, w1, w2, hi,
      SmtEval.native_zplus, SmtEval.native_zneg]
    have hWidthEq : w + -1 + -1 + 1 + (w + -1 + 1 + -(w + -1)) = w := by
      rw [Int.neg_add]
      calc
        w + -1 + -1 + 1 + (w + -1 + 1 + (-w + 1)) = w + (w + -w) := by
          simp [Int.add_assoc, Int.add_left_comm, Int.add_comm]
        _ = w := by
          simpa [Int.add_assoc] using (Int.add_neg_cancel_right w w)
    constructor
    · exact hWidthEq
    · simp [hWidthEq]
  · exact native_mod_total_canonical w
      (native_binary_concat w1
        (native_mod_total
          (native_binary_extract w x (native_zplus hi (native_zneg 1)) 0)
          (native_int_pow2 w1))
        w2
        (native_mod_total (native_binary_extract w x hi hi) (native_int_pow2 w2)))

/-- Lemma about `model_eval_rotate_left_rec_binary`. -/
theorem model_eval_rotate_left_rec_binary :
    ∀ n : native_Nat, ∀ w x : native_Int,
      native_zeq x (native_mod_total x (native_int_pow2 w)) = true ->
      ∃ m : native_Int,
        __smtx_rotate_left_rec n (SmtValue.Binary w x) =
          SmtValue.Binary w m ∧
        native_zeq m (native_mod_total m (native_int_pow2 w)) = true
  | native_nat_zero, w, x, hCanon => by
      refine ⟨x, ?_, hCanon⟩
      simp [__smtx_rotate_left_rec]
  | native_nat_succ n, w, x, hCanon => by
      rcases model_eval_rotate_left_step_binary w x with ⟨y, hy, hCanonY⟩
      rcases model_eval_rotate_left_rec_binary n w y hCanonY with ⟨m, hm, hCanon⟩
      refine ⟨m, ?_, hCanon⟩
      rw [__smtx_rotate_left_rec, hy, hm]

/-- Shows that evaluating `rotate_left` terms produces values of the expected type. -/
theorem typeof_value_model_eval_rotate_left
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.rotate_left t1 t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.rotate_left t1 t2)) =
      __smtx_typeof (SmtTerm.rotate_left t1 t2) := by
  rcases rotate_left_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.rotate_left t1 t2) =
      SmtType.BitVec w by
    rw [typeof_rotate_left_eq, h1, h2]
    simp [__smtx_typeof_rotate_left, native_ite, hi0]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [h1]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv, __smtx_model_eval_rotate_left]
  have hCanonIn :
      native_zeq n (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true := by
    exact bitvec_payload_canonical (by simpa [h2, hv] using hpres2)
  rcases model_eval_rotate_left_rec_binary (native_int_to_nat i) (native_nat_to_int w) n hCanonIn with ⟨m, hm, hCanon⟩
  rw [hm]
  have hw0 : native_zleq 0 (native_nat_to_int w) = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  simpa [native_nat_to_int, native_int_to_nat, Smtm.native_nat_to_int,
    SmtEval.native_int_to_nat] using
      typeof_value_binary_of_nonneg (native_nat_to_int w) m hw0
        (by simpa [Smtm.native_nat_to_int] using hCanon)

/-- Lemma about `model_eval_rotate_right_step_binary`. -/
theorem model_eval_rotate_right_step_binary
    (w x : native_Int) :
    ∃ y : native_Int,
      __smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral 0)
            (SmtValue.Numeral 0)
            (SmtValue.Binary w x))
          (__smtx_model_eval_extract
            (SmtValue.Numeral (native_zplus w (native_zneg 1)))
            (SmtValue.Numeral 1)
            (SmtValue.Binary w x)) =
        SmtValue.Binary w y ∧
      native_zeq y (native_mod_total y (native_int_pow2 w)) = true := by
  let hi := native_zplus w (native_zneg 1)
  let w1 := native_zplus (native_zplus 0 1) (native_zneg 0)
  let w2 := native_zplus (native_zplus hi 1) (native_zneg 1)
  refine ⟨native_mod_total
      (native_binary_concat w1
        (native_mod_total (native_binary_extract w x 0 0) (native_int_pow2 w1))
        w2
        (native_mod_total (native_binary_extract w x hi 1) (native_int_pow2 w2)))
      (native_int_pow2 w), ?_, ?_⟩
  · simp [__smtx_model_eval_concat, __smtx_model_eval_extract, w1, w2, hi,
      SmtEval.native_zplus, SmtEval.native_zneg]
    have hWidthEq : 1 + (w + -1 + 1 + -1) = w := by
      simp [Int.add_left_comm, Int.add_comm]
    constructor
    · exact hWidthEq
    · simp [hWidthEq]
  · exact native_mod_total_canonical w
      (native_binary_concat w1
        (native_mod_total (native_binary_extract w x 0 0) (native_int_pow2 w1))
        w2
        (native_mod_total (native_binary_extract w x hi 1) (native_int_pow2 w2)))

/-- Lemma about `model_eval_rotate_right_rec_binary`. -/
theorem model_eval_rotate_right_rec_binary :
    ∀ n : native_Nat, ∀ w x : native_Int,
      native_zeq x (native_mod_total x (native_int_pow2 w)) = true ->
      ∃ m : native_Int,
        __smtx_rotate_right_rec n (SmtValue.Binary w x) =
          SmtValue.Binary w m ∧
        native_zeq m (native_mod_total m (native_int_pow2 w)) = true
  | native_nat_zero, w, x, hCanon => by
      refine ⟨x, ?_, hCanon⟩
      simp [__smtx_rotate_right_rec]
  | native_nat_succ n, w, x, hCanon => by
      rcases model_eval_rotate_right_step_binary w x with ⟨y, hy, hCanonY⟩
      rcases model_eval_rotate_right_rec_binary n w y hCanonY with ⟨m, hm, hCanon⟩
      refine ⟨m, ?_, hCanon⟩
      rw [__smtx_rotate_right_rec, hy, hm]

/-- Shows that evaluating `rotate_right` terms produces values of the expected type. -/
theorem typeof_value_model_eval_rotate_right
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.rotate_right t1 t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.rotate_right t1 t2)) =
      __smtx_typeof (SmtTerm.rotate_right t1 t2) := by
  rcases rotate_right_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.rotate_right t1 t2) =
      SmtType.BitVec w by
    rw [typeof_rotate_right_eq, h1, h2]
    simp [__smtx_typeof_rotate_right, native_ite, hi0]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [h1]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv, __smtx_model_eval_rotate_right]
  have hCanonIn :
      native_zeq n (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true := by
    exact bitvec_payload_canonical (by simpa [h2, hv] using hpres2)
  rcases model_eval_rotate_right_rec_binary (native_int_to_nat i) (native_nat_to_int w) n hCanonIn with ⟨m, hm, hCanon⟩
  rw [hm]
  have hw0 : native_zleq 0 (native_nat_to_int w) = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  simpa [native_nat_to_int, native_int_to_nat, Smtm.native_nat_to_int,
    SmtEval.native_int_to_nat] using
      typeof_value_binary_of_nonneg (native_nat_to_int w) m hw0
        (by simpa [Smtm.native_nat_to_int] using hCanon)

/-- Shows that evaluating `bvuaddo` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvuaddo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvuaddo t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvuaddo t1 t2)) =
      __smtx_typeof (SmtTerm.bvuaddo t1 t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvuaddo __smtx_model_eval_bvuaddo
    SmtType.Bool t1 t2 (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 (fun _ _ _ _ _ _ => by
      simp [__smtx_model_eval_bvuaddo, __smtx_typeof_value])

/-- Shows that evaluating `bvnego` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvnego
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvnego t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvnego t)) =
      __smtx_typeof (SmtTerm.bvnego t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.bvnego __smtx_model_eval_bvnego
    SmtType.Bool t (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres (fun _ _ _ => by
      simp [__smtx_model_eval_bvnego, __smtx_typeof_value])

/-- Shows that evaluating `bvsaddo` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsaddo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvsaddo t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvsaddo t1 t2)) =
      __smtx_typeof (SmtTerm.bvsaddo t1 t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsaddo __smtx_model_eval_bvsaddo
    SmtType.Bool t1 t2 (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 (fun _ _ _ _ _ _ => by
      simp [__smtx_model_eval_bvsaddo, __smtx_typeof_value])

/-- Shows that evaluating `bvumulo` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvumulo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvumulo t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvumulo t1 t2)) =
      __smtx_typeof (SmtTerm.bvumulo t1 t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvumulo __smtx_model_eval_bvumulo
    SmtType.Bool t1 t2 (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 (fun _ _ _ _ _ _ => by
      simp [__smtx_model_eval_bvumulo, __smtx_typeof_value])

/-- Shows that evaluating `bvsmulo` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvsmulo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvsmulo t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvsmulo t1 t2)) =
      __smtx_typeof (SmtTerm.bvsmulo t1 t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsmulo __smtx_model_eval_bvsmulo
    SmtType.Bool t1 t2 (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 (fun _ _ _ _ _ _ => by
      simp [__smtx_model_eval_bvsmulo, __smtx_typeof_value])

/-- Shows that evaluating `bvusubo` terms produces values of the expected type. -/
theorem typeof_value_model_eval_bvusubo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bvusubo t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bvusubo t1 t2)) =
      __smtx_typeof (SmtTerm.bvusubo t1 t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvusubo __smtx_model_eval_bvusubo
    SmtType.Bool t1 t2 (by rw [__smtx_typeof.eq_def] <;> simp only) (by rw [__smtx_model_eval.eq_def] <;> simp only) ht hpres1 hpres2 (fun w n1 n2 hWidth _hMod1 _hMod2 => by
      simpa [__smtx_model_eval_bvusubo, __smtx_model_eval_bvult] using
        typeof_value_model_eval_bvugt_value w n2 n1 hWidth)

/-- Shows that evaluating `zero_extend` terms produces values of the expected type. -/
theorem typeof_value_model_eval_zero_extend
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.zero_extend t1 t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.zero_extend t1 t2)) =
      __smtx_typeof (SmtTerm.zero_extend t1 t2) := by
  rcases zero_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.zero_extend t1 t2) =
      SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) by
    rw [typeof_zero_extend_eq, h1, h2]
    simp [__smtx_typeof_zero_extend, native_ite, hi0]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [h1]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv]
  have hi : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hw0 : native_zleq 0 (native_nat_to_int w) = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  have hw : 0 <= native_nat_to_int w := by
    simpa [SmtEval.native_zleq] using hw0
  have hWidth : native_zleq 0 (native_zplus i (native_nat_to_int w)) = true := by
    have hAdd : 0 <= i + native_nat_to_int w := Int.add_nonneg hi hw
    unfold native_zleq native_zplus
    exact decide_eq_true hAdd
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 (native_zplus i (native_nat_to_int w)))) = true := by
    have hCanon :
        native_zeq n (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true :=
      bitvec_payload_canonical (by simpa [h2, hv] using hpres2)
    exact bitvec_payload_canonical_zero_extend hi0 hw0 hCanon
  simpa [__smtx_model_eval_zero_extend] using
    typeof_value_binary_of_nonneg (native_zplus i (native_nat_to_int w)) n hWidth hMod

/-- Shows that evaluating `sign_extend` terms produces values of the expected type. -/
theorem typeof_value_model_eval_sign_extend
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.sign_extend t1 t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.sign_extend t1 t2)) =
      __smtx_typeof (SmtTerm.sign_extend t1 t2) := by
  rcases sign_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.sign_extend t1 t2) =
      SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) by
    rw [typeof_sign_extend_eq, h1, h2]
    simp [__smtx_typeof_sign_extend, native_ite, hi0]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [h1]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv]
  have hi : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hw0 : native_zleq 0 (native_nat_to_int w) = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  have hw : 0 <= native_nat_to_int w := by
    simpa [SmtEval.native_zleq] using hw0
  have hWidth : native_zleq 0 (native_zplus i (native_nat_to_int w)) = true := by
    have hAdd : 0 <= i + native_nat_to_int w := Int.add_nonneg hi hw
    unfold native_zleq native_zplus
    exact decide_eq_true hAdd
  simpa [__smtx_model_eval_sign_extend] using
    typeof_value_binary_mod_of_nonneg (native_zplus i (native_nat_to_int w))
      (native_binary_uts (native_nat_to_int w) n) hWidth

/-- Shows that evaluating `int_to_bv` terms produces values of the expected type. -/
theorem typeof_value_model_eval_int_to_bv
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.int_to_bv t1 t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.int_to_bv t1 t2)) =
      __smtx_typeof (SmtTerm.int_to_bv t1 t2) := by
  rcases int_to_bv_args_of_non_none ht with ⟨i, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.int_to_bv t1 t2) =
      SmtType.BitVec (native_int_to_nat i) by
    rw [typeof_int_to_bv_eq, h1, h2]
    simp [__smtx_typeof_int_to_bv, native_ite, hi0]]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [h1]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n, hn⟩
  rw [hn]
  simpa [__smtx_model_eval_int_to_bv] using
    typeof_value_binary_mod_of_nonneg i n hi0

end Smtm
